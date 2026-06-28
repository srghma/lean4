// Lean compiler output
// Module: Lean.Elab.Tactic.Rewrite
// Imports: Lean.Meta.Tactic.Rewrite Lean.Meta.Tactic.Replace Lean.Elab.Tactic.Location Lean.Elab.ConfigEval Lean.Meta.Eqns
use crate::r#gen::Init::Data::List::Basic::l_List_reverse___redArg;
use crate::r#gen::Init::Meta::Defs::{l_Lean_Syntax_isNone, l_Lean_mkCIdentFrom};
use crate::r#gen::Init::Prelude::{
    l_Lean_Name_mkStr1, l_Lean_Name_mkStr3, l_Lean_Name_mkStr4, l_Lean_Name_mkStr5,
    l_Lean_Name_str___override, l_Lean_Syntax_getArg, l_Lean_Syntax_getArgs,
    l_Lean_Syntax_isOfKind, l_Lean_replaceRef,
};
use crate::r#gen::Lean::CoreM::l_Lean_Exception_isRuntime;
use crate::r#gen::Lean::Data::NameMap::Basic::l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg;
use crate::r#gen::Lean::Data::PersistentArray::l_Lean_PersistentArray_push___redArg;
use crate::r#gen::Lean::DeclarationRange::l_Lean_addBuiltinDeclarationRanges;
use crate::r#gen::Lean::Elab::ConfigEval::Basic::{
    l_Lean_Elab_ConfigEval_ConfigItem_addCompletionInfo,
    l_Lean_Elab_ConfigEval_ConfigItem_addConstInfo, l_Lean_Elab_ConfigEval_ConfigItem_checkNotBool,
    l_Lean_Elab_ConfigEval_ConfigItem_getRootStr, l_Lean_Elab_ConfigEval_ConfigItem_isAnonymous,
    l_Lean_Elab_ConfigEval_ConfigItem_shift,
    l_Lean_Elab_ConfigEval_ConfigItem_throwInvalidOption___redArg,
    l_Lean_Elab_ConfigEval_EvalConfigItem_defaultOnErr___redArg,
    l_Lean_Elab_ConfigEval_EvalConfigItem_setConfig_x27___redArg,
};
use crate::r#gen::Lean::Elab::ConfigEval::DeriveEvalConfigItem::l_Lean_Elab_ConfigEval_evalBoolItem;
use crate::r#gen::Lean::Elab::ConfigEval::DeriveEvalExpr::l_Lean_Elab_ConfigEval_EvalExpr_withSimpleEvalExpr___redArg;
use crate::r#gen::Lean::Elab::ConfigEval::Instances::l_Lean_Elab_ConfigEval_EvalExpr_evalBoolExpr;
use crate::r#gen::Lean::Elab::ConfigEval::MetaInstances::{
    l_Lean_Elab_ConfigEval_instEvalExprApplyNewGoals_evalExpr,
    l_Lean_Elab_ConfigEval_instEvalExprOccurrences_evalExpr,
    l_Lean_Elab_ConfigEval_instEvalExprTransparencyMode_evalExpr,
    l_Lean_Elab_ConfigEval_instEvalTermApplyNewGoals_evalTerm,
    l_Lean_Elab_ConfigEval_instEvalTermOccurrences_evalTerm,
    l_Lean_Elab_ConfigEval_instEvalTermTransparencyMode_evalTerm,
};
use crate::r#gen::Lean::Elab::ConfigEval::Types::l_Lean_Elab_ConfigEval_unsupportedExprExceptionId;
use crate::r#gen::Lean::Elab::ConfigEval::{
    initialize_Lean_Elab_ConfigEval, runtime_initialize_Lean_Elab_ConfigEval,
};
use crate::r#gen::Lean::Elab::Exception::{
    l_Lean_Elab_abortTacticExceptionId, l_Lean_Elab_abortTermExceptionId,
    l_Lean_Elab_unsupportedSyntaxExceptionId,
};
use crate::r#gen::Lean::Elab::SyntheticMVars::l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_withSynthesizeImp;
use crate::r#gen::Lean::Elab::Tactic::Basic::{
    l_Lean_Elab_Tactic_SavedState_restore___redArg, l_Lean_Elab_Tactic_getMainGoal___redArg,
    l_Lean_Elab_Tactic_getMainTarget, l_Lean_Elab_Tactic_mkInitialTacticInfo,
    l_Lean_Elab_Tactic_replaceMainGoal___redArg, l_Lean_Elab_Tactic_saveState___redArg,
    l_Lean_Elab_Tactic_tacticElabAttribute, l_Lean_Elab_Tactic_withMainContext___boxed,
    l_Lean_Elab_Tactic_withMainContext___redArg, l_Lean_Elab_Tactic_withoutRecover___redArg,
};
use crate::r#gen::Lean::Elab::Tactic::ElabTerm::l_Lean_Elab_Tactic_elabTerm;
use crate::r#gen::Lean::Elab::Tactic::Location::{
    initialize_Lean_Elab_Tactic_Location, l_Lean_Elab_Tactic_expandOptLocation,
    l_Lean_Elab_Tactic_withLocation, runtime_initialize_Lean_Elab_Tactic_Location,
};
use crate::r#gen::Lean::Elab::Term::TermElabM::{
    l_Lean_Elab_Term_addTermInfo, l_Lean_Elab_Term_elabTermEnsuringType___boxed,
    l_Lean_Elab_Term_isLocalIdent_x3f, l_Lean_Elab_Term_logUnassignedUsingErrorInfos,
};
use crate::r#gen::Lean::Elab::Util::{l_Lean_Elab_getBetterRef, l_Lean_Elab_pp_macroStack};
use crate::r#gen::Lean::Exception::{l_Lean_Exception_isInterrupt, l_Lean_Exception_toMessageData};
use crate::r#gen::Lean::Expr::{
    l_Lean_Expr_const___override, l_Lean_Expr_hasExprMVar, l_Lean_Expr_hasMVar, l_Lean_Expr_hash,
    l_Lean_Expr_mvar___override, l_Lean_instBEqMVarId_beq, l_Lean_instHashableMVarId_hash,
    l_Lean_instInhabitedExpr, l_Lean_mkConst, l_Lean_mkFVar,
};
use crate::r#gen::Lean::InternalExceptionId::l_Lean_instBEqInternalExceptionId_beq;
use crate::r#gen::Lean::KeyedDeclsAttribute::l_Lean_KeyedDeclsAttribute_addBuiltin___redArg;
use crate::r#gen::Lean::LocalContext::l_Lean_LocalDecl_type;
use crate::r#gen::Lean::Message::{
    l_Lean_MessageData_hint_x27, l_Lean_MessageData_nil, l_Lean_MessageData_note,
    l_Lean_MessageData_ofConstName, l_Lean_MessageData_ofExpr, l_Lean_MessageData_ofFormat,
    l_Lean_MessageData_ofName, l_Lean_MessageData_ofSyntax, l_Lean_indentD, l_Lean_indentExpr,
    l_Lean_stringToMessageData,
};
use crate::r#gen::Lean::Meta::AppBuilder::l_Lean_Meta_mkEqMP;
use crate::r#gen::Lean::Meta::Basic::{
    l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp, l_Lean_FVarId_getDecl___redArg,
    l_Lean_MVarId_setKind___redArg, l_Lean_MessageData_ofLazyM, l_Lean_Meta_mapErrorImp___redArg,
    l_Lean_Meta_mkConstWithFreshMVarLevels,
};
use crate::r#gen::Lean::Meta::Check::l_Lean_Meta_check;
use crate::r#gen::Lean::Meta::CollectMVars::l_Lean_Meta_getMVars;
use crate::r#gen::Lean::Meta::Eqns::{
    initialize_Lean_Meta_Eqns, l_Lean_Meta_getEqnsFor_x3f, l_Lean_Meta_unfoldThmSuffix,
    runtime_initialize_Lean_Meta_Eqns,
};
use crate::r#gen::Lean::Meta::InferType::l_Lean_Meta_isProp;
use crate::r#gen::Lean::Meta::Tactic::Replace::{
    initialize_Lean_Meta_Tactic_Replace, l_Lean_MVarId_replace, l_Lean_MVarId_replaceTargetEq,
    runtime_initialize_Lean_Meta_Tactic_Replace,
};
use crate::r#gen::Lean::Meta::Tactic::Rewrite::{
    initialize_Lean_Meta_Tactic_Rewrite, l_Lean_MVarId_rewrite,
    runtime_initialize_Lean_Meta_Tactic_Rewrite,
};
use crate::r#gen::Lean::Meta::Tactic::Util::{
    l_Lean_MVarId_getType, l_Lean_Meta_throwTacticEx___redArg,
};
use crate::r#gen::Lean::MetavarContext::{
    l_Lean_MetavarContext_getDecl, l_Lean_MetavarContext_getDelayedMVarAssignmentCore_x3f,
    l_Lean_MetavarContext_getExprAssignmentCore_x3f, l_Lean_instantiateMVarsCore,
};
use crate::r#gen::Lean::ReservedNameAction::l_Lean_realizeGlobalConstNoOverload;
use crate::r#gen::Lean::Util::Sorry::{l_Lean_Expr_hasSorry, l_Lean_Expr_hasSyntheticSorry};
use crate::lean_imports_rs::Init::Data::Array::Basic::{
    lean_array_uget_borrowed, lean_array_uset, lean_mk_array,
};
use crate::lean_imports_rs::Init::Data::Array::Set::lean_array_fset;
use crate::lean_imports_rs::Init::Data::Nat::Bitwise::Basic::lean_nat_shiftr;
use crate::lean_imports_rs::Init::Data::UInt::Basic::{
    lean_uint64_shift_right, lean_uint64_to_usize, lean_uint64_xor, lean_usize_land,
    lean_usize_shift_left, lean_usize_shift_right,
};
use crate::lean_imports_rs::Init::Data::UInt::BasicAux::{
    lean_usize_of_nat, lean_usize_sub, lean_usize_to_nat,
};
use crate::lean_imports_rs::Init::Prelude::{
    lean_array_fget, lean_array_fget_borrowed, lean_array_get_borrowed, lean_array_get_size,
    lean_array_push, lean_array_to_list, lean_mk_empty_array_with_capacity, lean_nat_add,
    lean_nat_dec_eq, lean_nat_dec_le, lean_nat_dec_lt, lean_nat_div, lean_nat_mul,
    lean_string_dec_eq,
};
use crate::lean_imports_rs::Init::System::ST::{
    lean_st_ref_get, lean_st_ref_set, lean_st_ref_take,
};
use crate::lean_imports_rs::Lean::Expr::lean_expr_eqv;
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_alloc_closure, lean_alloc_ctor, lean_apply_2,
    lean_apply_9, lean_apply_10, lean_apply_11, lean_box, lean_closure_set, lean_ctor_get,
    lean_ctor_get_uint8, lean_ctor_set, lean_ctor_set_tag, lean_ctor_set_uint8,
    lean_ctor_set_usize, lean_dec, lean_dec_ref, lean_dec_ref_known, lean_del_object, lean_inc,
    lean_inc_n, lean_inc_ref, lean_inc_ref_n, lean_io_result_is_error, lean_io_result_mk_ok,
    lean_is_exclusive, lean_mark_persistent, lean_obj_once, lean_obj_tag, lean_unbox,
    lean_unbox_usize, lean_unsigned_to_nat, lean_usize_once,
};
pub static l_Lean_Meta_withInstancesTypeCheckNote___at___00Lean_Elab_Tactic_elabRewrite_spec__0___redArg___lam__1___closed__0_value: LeanStringObject<312> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 312, m_capacity: 312, m_length: 311, m_data: [84, 104, 101, 32, 116, 97, 114, 103, 101, 116, 32, 101, 120, 112, 114, 101, 115, 115, 105, 111, 110, 32, 105, 115, 32, 110, 111, 116, 32, 116, 121, 112, 101, 45, 99, 111, 114, 114, 101, 99, 116, 32, 117, 110, 100, 101, 114, 32, 116, 104, 101, 32, 96, 105, 110, 115, 116, 97, 110, 99, 101, 115, 96, 32, 116, 114, 97, 110, 115, 112, 97, 114, 101, 110, 99, 121, 32, 108, 101, 118, 101, 108, 44, 32, 119, 104, 105, 99, 104, 32, 109, 97, 121, 32, 104, 97, 118, 101, 32, 116, 114, 105, 103, 103, 101, 114, 101, 100, 32, 116, 104, 101, 32, 102, 97, 105, 108, 117, 114, 101, 46, 32, 84, 104, 105, 115, 32, 105, 115, 32, 117, 115, 117, 97, 108, 108, 121, 32, 99, 97, 117, 115, 101, 100, 32, 98, 121, 32, 117, 110, 102, 111, 108, 100, 105, 110, 103, 32, 111, 102, 32, 115, 101, 109, 105, 114, 101, 100, 117, 99, 105, 98, 108, 101, 32, 100, 101, 102, 105, 110, 105, 116, 105, 111, 110, 115, 32, 105, 110, 32, 112, 114, 105, 111, 114, 32, 116, 97, 99, 116, 105, 99, 32, 115, 116, 101, 112, 115, 46, 32, 85, 115, 101, 32, 96, 115, 101, 116, 95, 111, 112, 116, 105, 111, 110, 32, 108, 105, 110, 116, 101, 114, 46, 116, 97, 99, 116, 105, 99, 67, 104, 101, 99, 107, 73, 110, 115, 116, 97, 110, 99, 101, 115, 32, 116, 114, 117, 101, 96, 32, 116, 111, 32, 105, 110, 118, 101, 115, 116, 105, 103, 97, 116, 101, 32, 116, 104, 101, 32, 115, 111, 117, 114, 99, 101, 32, 111, 102, 32, 116, 104, 101, 32, 105, 115, 115, 117, 101, 46, 10, 70, 117, 108, 108, 32, 101, 114, 114, 111, 114, 58, 0]};
static mut l_Lean_Meta_withInstancesTypeCheckNote___at___00Lean_Elab_Tactic_elabRewrite_spec__0___redArg___lam__1___closed__0: *mut LeanObject = core::ptr::addr_of!(l_Lean_Meta_withInstancesTypeCheckNote___at___00Lean_Elab_Tactic_elabRewrite_spec__0___redArg___lam__1___closed__0_value) as *mut LeanObject;
static mut l_Lean_Meta_withInstancesTypeCheckNote___at___00Lean_Elab_Tactic_elabRewrite_spec__0___redArg___lam__1___closed__1_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Meta_withInstancesTypeCheckNote___at___00Lean_Elab_Tactic_elabRewrite_spec__0___redArg___lam__1___closed__1: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Elab_throwAbortTactic___at___00Lean_Elab_Tactic_elabRewrite_spec__4___redArg___closed__0_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Elab_throwAbortTactic___at___00Lean_Elab_Tactic_elabRewrite_spec__4___redArg___closed__0: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_elabRewrite_spec__2_spec__2_spec__6___closed__0_value: LeanCtorObject<1> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*1 + 0) as u16, other: 1, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_elabRewrite_spec__2_spec__2_spec__6___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_elabRewrite_spec__2_spec__2_spec__6___closed__0_value) as *mut LeanObject;
pub static l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_elabRewrite_spec__2_spec__2_spec__6___closed__1_value: LeanCtorObject<1> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*1 + 0) as u16, other: 1, tag: 0 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_elabRewrite_spec__2_spec__2_spec__6___closed__1: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_elabRewrite_spec__2_spec__2_spec__6___closed__1_value) as *mut LeanObject;
static mut l_Lean_occursCheck___at___00Lean_Elab_Tactic_elabRewrite_spec__2___closed__0_once:
    LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_occursCheck___at___00Lean_Elab_Tactic_elabRewrite_spec__2___closed__0:
    *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_occursCheck___at___00Lean_Elab_Tactic_elabRewrite_spec__2___closed__1_once:
    LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_occursCheck___at___00Lean_Elab_Tactic_elabRewrite_spec__2___closed__1:
    *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_Tactic_elabRewrite___closed__0_value: LeanStringObject<32> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 32,
        m_capacity: 32,
        m_length: 31,
        m_data: [
            79, 99, 99, 117, 114, 115, 32, 99, 104, 101, 99, 107, 32, 102, 97, 105, 108, 101, 100,
            58, 32, 69, 120, 112, 114, 101, 115, 115, 105, 111, 110, 0,
        ],
    };
static mut l_Lean_Elab_Tactic_elabRewrite___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_elabRewrite___closed__0_value) as *mut LeanObject;
static mut l_Lean_Elab_Tactic_elabRewrite___closed__1_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_Tactic_elabRewrite___closed__1: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_Tactic_elabRewrite___closed__2_value: LeanStringObject<20> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 20,
        m_capacity: 20,
        m_length: 19,
        m_data: [
            10, 99, 111, 110, 116, 97, 105, 110, 115, 32, 116, 104, 101, 32, 103, 111, 97, 108, 32,
            0,
        ],
    };
static mut l_Lean_Elab_Tactic_elabRewrite___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_elabRewrite___closed__2_value) as *mut LeanObject;
static mut l_Lean_Elab_Tactic_elabRewrite___closed__3_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_Tactic_elabRewrite___closed__3: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_finishElabRewrite_spec__0_spec__0_spec__2___redArg___closed__0_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_finishElabRewrite_spec__0_spec__0_spec__2___redArg___closed__0: usize = 0;
static mut l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_finishElabRewrite_spec__0_spec__0_spec__2___redArg___closed__1_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_finishElabRewrite_spec__0_spec__0_spec__2___redArg___closed__1: usize = 0;
pub static l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_withRWRulesSeq_go___closed__0_value: LeanStringObject<48> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 48, m_capacity: 48, m_length: 47, m_data: [70, 97, 105, 108, 101, 100, 32, 116, 111, 32, 114, 101, 119, 114, 105, 116, 101, 32, 117, 115, 105, 110, 103, 32, 101, 113, 117, 97, 116, 105, 111, 110, 32, 116, 104, 101, 111, 114, 101, 109, 115, 32, 102, 111, 114, 32, 96, 0]};
static mut l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_withRWRulesSeq_go___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_withRWRulesSeq_go___closed__0_value) as *mut LeanObject;
static mut l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_withRWRulesSeq_go___closed__1_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_withRWRulesSeq_go___closed__1: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_withRWRulesSeq_go___closed__2_value: LeanStringObject<2> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [96, 0]};
static mut l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_withRWRulesSeq_go___closed__2: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_withRWRulesSeq_go___closed__2_value) as *mut LeanObject;
static mut l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_withRWRulesSeq_go___closed__3_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_withRWRulesSeq_go___closed__3: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_withRWRulesSeq_spec__0_spec__0___redArg___closed__0_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_withRWRulesSeq_spec__0_spec__0___redArg___closed__0: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_withRWRulesSeq_spec__0_spec__0___redArg___closed__1_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_withRWRulesSeq_spec__0_spec__0___redArg___closed__1: *mut LeanObject = core::ptr::null_mut();
pub static l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_withRWRulesSeq_spec__1___redArg___lam__3___closed__0_value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [76, 101, 97, 110, 0]};
static mut l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_withRWRulesSeq_spec__1___redArg___lam__3___closed__0: *mut LeanObject = core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_withRWRulesSeq_spec__1___redArg___lam__3___closed__0_value) as *mut LeanObject;
pub static l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_withRWRulesSeq_spec__1___redArg___lam__3___closed__1_value: LeanStringObject<7> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [80, 97, 114, 115, 101, 114, 0]};
static mut l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_withRWRulesSeq_spec__1___redArg___lam__3___closed__1: *mut LeanObject = core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_withRWRulesSeq_spec__1___redArg___lam__3___closed__1_value) as *mut LeanObject;
pub static l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_withRWRulesSeq_spec__1___redArg___lam__3___closed__2_value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [84, 101, 114, 109, 0]};
static mut l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_withRWRulesSeq_spec__1___redArg___lam__3___closed__2: *mut LeanObject = core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_withRWRulesSeq_spec__1___redArg___lam__3___closed__2_value) as *mut LeanObject;
pub static l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_withRWRulesSeq_spec__1___redArg___lam__3___closed__3_value: LeanStringObject<9> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [101, 120, 112, 108, 105, 99, 105, 116, 0]};
static mut l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_withRWRulesSeq_spec__1___redArg___lam__3___closed__3: *mut LeanObject = core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_withRWRulesSeq_spec__1___redArg___lam__3___closed__3_value) as *mut LeanObject;
static l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_withRWRulesSeq_spec__1___redArg___lam__3___closed__4_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_withRWRulesSeq_spec__1___redArg___lam__3___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_withRWRulesSeq_spec__1___redArg___lam__3___closed__4_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_withRWRulesSeq_spec__1___redArg___lam__3___closed__4_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_withRWRulesSeq_spec__1___redArg___lam__3___closed__1_value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_withRWRulesSeq_spec__1___redArg___lam__3___closed__4_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_withRWRulesSeq_spec__1___redArg___lam__3___closed__4_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_withRWRulesSeq_spec__1___redArg___lam__3___closed__2_value) as *mut LeanObject,16572064140653406795 as *mut LeanObject] };
pub static l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_withRWRulesSeq_spec__1___redArg___lam__3___closed__4_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_withRWRulesSeq_spec__1___redArg___lam__3___closed__4_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_withRWRulesSeq_spec__1___redArg___lam__3___closed__3_value) as *mut LeanObject,13290931718435096973 as *mut LeanObject] };
static mut l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_withRWRulesSeq_spec__1___redArg___lam__3___closed__4: *mut LeanObject = core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_withRWRulesSeq_spec__1___redArg___lam__3___closed__4_value) as *mut LeanObject;
pub static l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_withRWRulesSeq_spec__1___redArg___lam__2___closed__0_value: LeanStringObject<21> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 21, m_capacity: 21, m_length: 20, m_data: [84, 114, 121, 32, 114, 101, 119, 114, 105, 116, 105, 110, 103, 32, 119, 105, 116, 104, 32, 96, 0]};
static mut l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_withRWRulesSeq_spec__1___redArg___lam__2___closed__0: *mut LeanObject = core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_withRWRulesSeq_spec__1___redArg___lam__2___closed__0_value) as *mut LeanObject;
static mut l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_withRWRulesSeq_spec__1___redArg___lam__2___closed__1_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_withRWRulesSeq_spec__1___redArg___lam__2___closed__1: *mut LeanObject = core::ptr::null_mut();
pub static l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_withRWRulesSeq_spec__1___redArg___lam__2___closed__2_value: LeanStringObject<1> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 1, m_capacity: 1, m_length: 0, m_data: [0]};
static mut l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_withRWRulesSeq_spec__1___redArg___lam__2___closed__2: *mut LeanObject = core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_withRWRulesSeq_spec__1___redArg___lam__2___closed__2_value) as *mut LeanObject;
static mut l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_withRWRulesSeq_spec__1___redArg___lam__2___closed__3_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_withRWRulesSeq_spec__1___redArg___lam__2___closed__3: *mut LeanObject = core::ptr::null_mut();
pub static l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_withRWRulesSeq_spec__1___redArg___closed__0_value: LeanStringObject<6> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [105, 100, 101, 110, 116, 0]};
static mut l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_withRWRulesSeq_spec__1___redArg___closed__0: *mut LeanObject = core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_withRWRulesSeq_spec__1___redArg___closed__0_value) as *mut LeanObject;
pub static l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_withRWRulesSeq_spec__1___redArg___closed__1_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_withRWRulesSeq_spec__1___redArg___closed__0_value) as *mut LeanObject,5117844058249666356 as *mut LeanObject] };
static mut l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_withRWRulesSeq_spec__1___redArg___closed__1: *mut LeanObject = core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_withRWRulesSeq_spec__1___redArg___closed__1_value) as *mut LeanObject;
pub static l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_withRWRulesSeq_spec__1___redArg___closed__2_value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [110, 117, 108, 108, 0]};
static mut l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_withRWRulesSeq_spec__1___redArg___closed__2: *mut LeanObject = core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_withRWRulesSeq_spec__1___redArg___closed__2_value) as *mut LeanObject;
pub static l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_withRWRulesSeq_spec__1___redArg___closed__3_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_withRWRulesSeq_spec__1___redArg___closed__2_value) as *mut LeanObject,9855511589286918680 as *mut LeanObject] };
static mut l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_withRWRulesSeq_spec__1___redArg___closed__3: *mut LeanObject = core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_withRWRulesSeq_spec__1___redArg___closed__3_value) as *mut LeanObject;
pub static l_Lean_Elab_Tactic_withRWRulesSeq___closed__0_value: LeanClosureObject<1> =
    LeanClosureObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut LeanObject>() * 1) as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Lean_Elab_Tactic_withRWRulesSeq___lam__1___boxed as *const core::ffi::c_void,
        m_arity: 10,
        m_num_fixed: 1,
        m_objs: [(((0 as usize) << 1) | 1) as *mut LeanObject],
    };
static mut l_Lean_Elab_Tactic_withRWRulesSeq___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_withRWRulesSeq___closed__0_value) as *mut LeanObject;
static mut l_Lean_Elab_ConfigEval_throwUnsupportedExpr___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_instEvalExprConfig_evalExpr_spec__0___redArg___closed__0_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Elab_ConfigEval_throwUnsupportedExpr___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_instEvalExprConfig_evalExpr_spec__0___redArg___closed__0: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_instEvalExprConfig_evalExpr___lam__0___closed__0_value: LeanStringObject<3> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [109, 107, 0]};
static mut l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_instEvalExprConfig_evalExpr___lam__0___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_instEvalExprConfig_evalExpr___lam__0___closed__0_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_instEvalExprConfig_evalExpr___lam__0___closed__1_value: LeanStringObject<7> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [102, 97, 105, 108, 101, 100, 0]};
static mut l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_instEvalExprConfig_evalExpr___lam__0___closed__1: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_instEvalExprConfig_evalExpr___lam__0___closed__1_value) as *mut LeanObject;
static mut l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_instEvalExprConfig_evalExpr___lam__0___closed__2_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_instEvalExprConfig_evalExpr___lam__0___closed__2: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_instEvalExprConfig_evalExpr___closed__0_value: LeanClosureObject<0> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_instEvalExprConfig_evalExpr___lam__0___boxed as *const core::ffi::c_void, m_arity: 7, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_instEvalExprConfig_evalExpr___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_instEvalExprConfig_evalExpr___closed__0_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_instEvalExprConfig_evalExpr___closed__1_value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [77, 101, 116, 97, 0]};
static mut l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_instEvalExprConfig_evalExpr___closed__1: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_instEvalExprConfig_evalExpr___closed__1_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_instEvalExprConfig_evalExpr___closed__2_value: LeanStringObject<8> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [82, 101, 119, 114, 105, 116, 101, 0]};
static mut l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_instEvalExprConfig_evalExpr___closed__2: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_instEvalExprConfig_evalExpr___closed__2_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_instEvalExprConfig_evalExpr___closed__3_value: LeanStringObject<7> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [67, 111, 110, 102, 105, 103, 0]};
static mut l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_instEvalExprConfig_evalExpr___closed__3: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_instEvalExprConfig_evalExpr___closed__3_value) as *mut LeanObject;
static l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_instEvalExprConfig_evalExpr___closed__4_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_withRWRulesSeq_spec__1___redArg___lam__3___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_instEvalExprConfig_evalExpr___closed__4_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_instEvalExprConfig_evalExpr___closed__4_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_instEvalExprConfig_evalExpr___closed__1_value) as *mut LeanObject,15449383196166861506 as *mut LeanObject] };
static l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_instEvalExprConfig_evalExpr___closed__4_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_instEvalExprConfig_evalExpr___closed__4_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_instEvalExprConfig_evalExpr___closed__2_value) as *mut LeanObject,3231726234450343084 as *mut LeanObject] };
pub static l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_instEvalExprConfig_evalExpr___closed__4_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_instEvalExprConfig_evalExpr___closed__4_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_instEvalExprConfig_evalExpr___closed__3_value) as *mut LeanObject,4444531101797470731 as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_instEvalExprConfig_evalExpr___closed__4: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_instEvalExprConfig_evalExpr___closed__4_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_instEvalExprConfig___closed__0_value: LeanClosureObject<0> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_instEvalExprConfig_evalExpr___boxed as *const core::ffi::c_void, m_arity: 6, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_instEvalExprConfig___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_instEvalExprConfig___closed__0_value) as *mut LeanObject;
static mut l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_instEvalExprConfig___closed__1_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_instEvalExprConfig___closed__1: *mut LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_instEvalExprConfig___closed__2_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_instEvalExprConfig___closed__2: *mut LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_instEvalExprConfig___closed__3_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_instEvalExprConfig___closed__3: *mut LeanObject = core::ptr::null_mut();
pub static mut l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_instEvalExprConfig:
    *mut LeanObject = core::ptr::null_mut();
static mut l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3_spec__7_spec__8_spec__11___closed__0_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3_spec__7_spec__8_spec__11___closed__0: *mut LeanObject = core::ptr::null_mut();
pub static l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3_spec__7_spec__8_spec__11___closed__1_value: LeanStringObject<16> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 16, m_capacity: 16, m_length: 15, m_data: [119, 104, 105, 108, 101, 32, 101, 120, 112, 97, 110, 100, 105, 110, 103, 0]};
static mut l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3_spec__7_spec__8_spec__11___closed__1: *mut LeanObject = core::ptr::addr_of!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3_spec__7_spec__8_spec__11___closed__1_value) as *mut LeanObject;
pub static l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3_spec__7_spec__8_spec__11___closed__2_value: LeanCtorObject<1> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*1 + 0) as u16, other: 1, tag: 3 }, m_objs: [core::ptr::addr_of!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3_spec__7_spec__8_spec__11___closed__1_value) as *mut LeanObject] };
static mut l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3_spec__7_spec__8_spec__11___closed__2: *mut LeanObject = core::ptr::addr_of!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3_spec__7_spec__8_spec__11___closed__2_value) as *mut LeanObject;
static mut l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3_spec__7_spec__8_spec__11___closed__3_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3_spec__7_spec__8_spec__11___closed__3: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3_spec__7_spec__8___redArg___closed__0_value: LeanStringObject<25> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 25, m_capacity: 25, m_length: 24, m_data: [119, 105, 116, 104, 32, 114, 101, 115, 117, 108, 116, 105, 110, 103, 32, 101, 120, 112, 97, 110, 115, 105, 111, 110, 0]};
static mut l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3_spec__7_spec__8___redArg___closed__0: *mut LeanObject = core::ptr::addr_of!(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3_spec__7_spec__8___redArg___closed__0_value) as *mut LeanObject;
pub static l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3_spec__7_spec__8___redArg___closed__1_value: LeanCtorObject<1> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*1 + 0) as u16, other: 1, tag: 3 }, m_objs: [core::ptr::addr_of!(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3_spec__7_spec__8___redArg___closed__0_value) as *mut LeanObject] };
static mut l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3_spec__7_spec__8___redArg___closed__1: *mut LeanObject = core::ptr::addr_of!(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3_spec__7_spec__8___redArg___closed__1_value) as *mut LeanObject;
static mut l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3_spec__7_spec__8___redArg___closed__2_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3_spec__7_spec__8___redArg___closed__2: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3_spec__8___redArg___closed__0_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3_spec__8___redArg___closed__0: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__2_spec__4___closed__0_value: LeanStringObject<14> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 14, m_capacity: 14, m_length: 13, m_data: [65, 112, 112, 108, 121, 78, 101, 119, 71, 111, 97, 108, 115, 0]};
static mut l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__2_spec__4___closed__0: *mut LeanObject = core::ptr::addr_of!(l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__2_spec__4___closed__0_value) as *mut LeanObject;
static l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__2_spec__4___closed__1_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_withRWRulesSeq_spec__1___redArg___lam__3___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__2_spec__4___closed__1_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__2_spec__4___closed__1_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_instEvalExprConfig_evalExpr___closed__1_value) as *mut LeanObject,15449383196166861506 as *mut LeanObject] };
pub static l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__2_spec__4___closed__1_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__2_spec__4___closed__1_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__2_spec__4___closed__0_value) as *mut LeanObject,1913141712249469064 as *mut LeanObject] };
static mut l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__2_spec__4___closed__1: *mut LeanObject = core::ptr::addr_of!(l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__2_spec__4___closed__1_value) as *mut LeanObject;
static mut l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__2_spec__4___closed__2_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__2_spec__4___closed__2: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__2_spec__4___closed__3_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__2_spec__4___closed__3: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__2_spec__4___closed__4_value: LeanStringObject<11> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 11, m_capacity: 11, m_length: 10, m_data: [10, 111, 102, 32, 116, 121, 112, 101, 32, 96, 0]};
static mut l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__2_spec__4___closed__4: *mut LeanObject = core::ptr::addr_of!(l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__2_spec__4___closed__4_value) as *mut LeanObject;
static mut l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__2_spec__4___closed__5_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__2_spec__4___closed__5: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__2_spec__4___closed__6_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__2_spec__4___closed__6: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__2_spec__4___closed__7_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__2_spec__4___closed__7: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__2_spec__4___closed__8_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__2_spec__4___closed__8: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__2_spec__4___closed__9_value: LeanStringObject<34> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 34, m_capacity: 34, m_length: 33, m_data: [67, 111, 117, 108, 100, 32, 110, 111, 116, 32, 101, 118, 97, 108, 117, 97, 116, 101, 32, 116, 104, 101, 32, 101, 120, 112, 114, 101, 115, 115, 105, 111, 110, 0]};
static mut l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__2_spec__4___closed__9: *mut LeanObject = core::ptr::addr_of!(l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__2_spec__4___closed__9_value) as *mut LeanObject;
static mut l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__2_spec__4___closed__10_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__2_spec__4___closed__10: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__2_spec__4___closed__11_value: LeanStringObject<29> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 29, m_capacity: 29, m_length: 28, m_data: [69, 120, 112, 114, 101, 115, 115, 105, 111, 110, 32, 99, 111, 110, 116, 97, 105, 110, 115, 32, 96, 115, 111, 114, 114, 121, 96, 58, 0]};
static mut l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__2_spec__4___closed__11: *mut LeanObject = core::ptr::addr_of!(l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__2_spec__4___closed__11_value) as *mut LeanObject;
static mut l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__2_spec__4___closed__12_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__2_spec__4___closed__12: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__1_spec__2___closed__0_value: LeanStringObject<12> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 12, m_capacity: 12, m_length: 11, m_data: [79, 99, 99, 117, 114, 114, 101, 110, 99, 101, 115, 0]};
static mut l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__1_spec__2___closed__0: *mut LeanObject = core::ptr::addr_of!(l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__1_spec__2___closed__0_value) as *mut LeanObject;
static l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__1_spec__2___closed__1_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_withRWRulesSeq_spec__1___redArg___lam__3___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__1_spec__2___closed__1_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__1_spec__2___closed__1_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_instEvalExprConfig_evalExpr___closed__1_value) as *mut LeanObject,15449383196166861506 as *mut LeanObject] };
pub static l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__1_spec__2___closed__1_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__1_spec__2___closed__1_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__1_spec__2___closed__0_value) as *mut LeanObject,10189614426786410228 as *mut LeanObject] };
static mut l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__1_spec__2___closed__1: *mut LeanObject = core::ptr::addr_of!(l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__1_spec__2___closed__1_value) as *mut LeanObject;
static mut l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__1_spec__2___closed__2_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__1_spec__2___closed__2: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__1_spec__2___closed__3_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__1_spec__2___closed__3: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__1_spec__2___closed__4_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__1_spec__2___closed__4: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__1_spec__2___closed__5_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__1_spec__2___closed__5: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__1_spec__2___closed__6_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__1_spec__2___closed__6: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3___closed__0_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3___closed__0: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3___closed__1_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3___closed__1: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3___closed__2_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3___closed__2: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__0_spec__0___closed__0_value: LeanStringObject<17> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 17, m_capacity: 17, m_length: 16, m_data: [84, 114, 97, 110, 115, 112, 97, 114, 101, 110, 99, 121, 77, 111, 100, 101, 0]};
static mut l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__0_spec__0___closed__0: *mut LeanObject = core::ptr::addr_of!(l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__0_spec__0___closed__0_value) as *mut LeanObject;
static l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__0_spec__0___closed__1_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_withRWRulesSeq_spec__1___redArg___lam__3___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__0_spec__0___closed__1_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__0_spec__0___closed__1_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_instEvalExprConfig_evalExpr___closed__1_value) as *mut LeanObject,15449383196166861506 as *mut LeanObject] };
pub static l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__0_spec__0___closed__1_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__0_spec__0___closed__1_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__0_spec__0___closed__0_value) as *mut LeanObject,7920553410559161077 as *mut LeanObject] };
static mut l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__0_spec__0___closed__1: *mut LeanObject = core::ptr::addr_of!(l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__0_spec__0___closed__1_value) as *mut LeanObject;
static mut l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__0_spec__0___closed__2_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__0_spec__0___closed__2: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__0_spec__0___closed__3_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__0_spec__0___closed__3: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__0_spec__0___closed__4_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__0_spec__0___closed__4: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__0_spec__0___closed__5_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__0_spec__0___closed__5: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__0_spec__0___closed__6_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__0_spec__0___closed__6: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem___lam__0___closed__0_value: LeanCtorObject<1> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*1 + 0) as u16, other: 1, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_instEvalExprConfig_evalExpr___closed__4_value) as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem___lam__0___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem___lam__0___closed__0_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem___lam__0___closed__1_value: LeanStringObject<7> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [99, 111, 110, 102, 105, 103, 0]};
static mut l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem___lam__0___closed__1: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem___lam__0___closed__1_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem___lam__0___closed__2_value: LeanStringObject<9> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [110, 101, 119, 71, 111, 97, 108, 115, 0]};
static mut l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem___lam__0___closed__2: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem___lam__0___closed__2_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem___lam__0___closed__3_value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [111, 99, 99, 115, 0]};
static mut l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem___lam__0___closed__3: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem___lam__0___closed__3_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem___lam__0___closed__4_value: LeanStringObject<13> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 13, m_capacity: 13, m_length: 12, m_data: [111, 102, 102, 115, 101, 116, 67, 110, 115, 116, 114, 115, 0]};
static mut l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem___lam__0___closed__4: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem___lam__0___closed__4_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem___lam__0___closed__5_value: LeanStringObject<13> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 13, m_capacity: 13, m_length: 12, m_data: [116, 114, 97, 110, 115, 112, 97, 114, 101, 110, 99, 121, 0]};
static mut l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem___lam__0___closed__5: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem___lam__0___closed__5_value) as *mut LeanObject;
static l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem___lam__0___closed__6_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_withRWRulesSeq_spec__1___redArg___lam__3___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem___lam__0___closed__6_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem___lam__0___closed__6_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_instEvalExprConfig_evalExpr___closed__1_value) as *mut LeanObject,15449383196166861506 as *mut LeanObject] };
static l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem___lam__0___closed__6_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem___lam__0___closed__6_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_instEvalExprConfig_evalExpr___closed__2_value) as *mut LeanObject,3231726234450343084 as *mut LeanObject] };
static l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem___lam__0___closed__6_value_aux_3: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem___lam__0___closed__6_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_instEvalExprConfig_evalExpr___closed__3_value) as *mut LeanObject,4444531101797470731 as *mut LeanObject] };
pub static l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem___lam__0___closed__6_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem___lam__0___closed__6_value_aux_3) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem___lam__0___closed__5_value) as *mut LeanObject,13559935064002620297 as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem___lam__0___closed__6: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem___lam__0___closed__6_value) as *mut LeanObject;
static l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem___lam__0___closed__7_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_withRWRulesSeq_spec__1___redArg___lam__3___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem___lam__0___closed__7_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem___lam__0___closed__7_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_instEvalExprConfig_evalExpr___closed__1_value) as *mut LeanObject,15449383196166861506 as *mut LeanObject] };
static l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem___lam__0___closed__7_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem___lam__0___closed__7_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_instEvalExprConfig_evalExpr___closed__2_value) as *mut LeanObject,3231726234450343084 as *mut LeanObject] };
static l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem___lam__0___closed__7_value_aux_3: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem___lam__0___closed__7_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_instEvalExprConfig_evalExpr___closed__3_value) as *mut LeanObject,4444531101797470731 as *mut LeanObject] };
pub static l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem___lam__0___closed__7_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem___lam__0___closed__7_value_aux_3) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem___lam__0___closed__4_value) as *mut LeanObject,13158473008816018672 as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem___lam__0___closed__7: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem___lam__0___closed__7_value) as *mut LeanObject;
static l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem___lam__0___closed__8_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_withRWRulesSeq_spec__1___redArg___lam__3___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem___lam__0___closed__8_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem___lam__0___closed__8_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_instEvalExprConfig_evalExpr___closed__1_value) as *mut LeanObject,15449383196166861506 as *mut LeanObject] };
static l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem___lam__0___closed__8_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem___lam__0___closed__8_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_instEvalExprConfig_evalExpr___closed__2_value) as *mut LeanObject,3231726234450343084 as *mut LeanObject] };
static l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem___lam__0___closed__8_value_aux_3: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem___lam__0___closed__8_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_instEvalExprConfig_evalExpr___closed__3_value) as *mut LeanObject,4444531101797470731 as *mut LeanObject] };
pub static l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem___lam__0___closed__8_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem___lam__0___closed__8_value_aux_3) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem___lam__0___closed__3_value) as *mut LeanObject,692840103835893188 as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem___lam__0___closed__8: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem___lam__0___closed__8_value) as *mut LeanObject;
static l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem___lam__0___closed__9_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_withRWRulesSeq_spec__1___redArg___lam__3___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem___lam__0___closed__9_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem___lam__0___closed__9_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_instEvalExprConfig_evalExpr___closed__1_value) as *mut LeanObject,15449383196166861506 as *mut LeanObject] };
static l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem___lam__0___closed__9_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem___lam__0___closed__9_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_instEvalExprConfig_evalExpr___closed__2_value) as *mut LeanObject,3231726234450343084 as *mut LeanObject] };
static l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem___lam__0___closed__9_value_aux_3: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem___lam__0___closed__9_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_instEvalExprConfig_evalExpr___closed__3_value) as *mut LeanObject,4444531101797470731 as *mut LeanObject] };
pub static l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem___lam__0___closed__9_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem___lam__0___closed__9_value_aux_3) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem___lam__0___closed__2_value) as *mut LeanObject,17718680079647960655 as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem___lam__0___closed__9: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem___lam__0___closed__9_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem___closed__0_value: LeanClosureObject<0> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem___lam__0___boxed as *const core::ffi::c_void, m_arity: 9, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem___closed__0_value) as *mut LeanObject;
pub static mut l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem___closed__0_value) as *mut LeanObject;
static mut l_Lean_Elab_Tactic_elabRewriteConfig___redArg___lam__0___closed__0_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Elab_Tactic_elabRewriteConfig___redArg___lam__0___closed__0: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Elab_Tactic_elabRewriteConfig___redArg___lam__0___closed__1_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Elab_Tactic_elabRewriteConfig___redArg___lam__0___closed__1: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Elab_Tactic_elabRewriteConfig___redArg___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Lean_Elab_Tactic_elabRewriteConfig___redArg___lam__0___boxed
            as *const core::ffi::c_void,
        m_arity: 9,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Elab_Tactic_elabRewriteConfig___redArg___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_elabRewriteConfig___redArg___closed__0_value)
        as *mut LeanObject;
pub static l_Lean_Elab_Tactic_evalRewriteSeq___lam__0___closed__0_value: LeanStringObject<8> =
    LeanStringObject {
        m_header: LeanObject {
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
static mut l_Lean_Elab_Tactic_evalRewriteSeq___lam__0___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_evalRewriteSeq___lam__0___closed__0_value)
        as *mut LeanObject;
pub static l_Lean_Elab_Tactic_evalRewriteSeq___lam__0___closed__1_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Tactic_evalRewriteSeq___lam__0___closed__0_value)
                as *mut LeanObject,
            12013589835852235629 as *mut LeanObject,
        ],
    };
static mut l_Lean_Elab_Tactic_evalRewriteSeq___lam__0___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_evalRewriteSeq___lam__0___closed__1_value)
        as *mut LeanObject;
pub static l_Lean_Elab_Tactic_evalRewriteSeq___lam__0___closed__2_value: LeanStringObject<62> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 62,
        m_capacity: 62,
        m_length: 61,
        m_data: [
            68, 105, 100, 32, 110, 111, 116, 32, 102, 105, 110, 100, 32, 97, 110, 32, 111, 99, 99,
            117, 114, 114, 101, 110, 99, 101, 32, 111, 102, 32, 116, 104, 101, 32, 112, 97, 116,
            116, 101, 114, 110, 32, 105, 110, 32, 116, 104, 101, 32, 99, 117, 114, 114, 101, 110,
            116, 32, 103, 111, 97, 108, 0,
        ],
    };
static mut l_Lean_Elab_Tactic_evalRewriteSeq___lam__0___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_evalRewriteSeq___lam__0___closed__2_value)
        as *mut LeanObject;
pub static l_Lean_Elab_Tactic_evalRewriteSeq___lam__0___closed__3_value: LeanCtorObject<1> =
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
            core::ptr::addr_of!(l_Lean_Elab_Tactic_evalRewriteSeq___lam__0___closed__2_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Elab_Tactic_evalRewriteSeq___lam__0___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_evalRewriteSeq___lam__0___closed__3_value)
        as *mut LeanObject;
static mut l_Lean_Elab_Tactic_evalRewriteSeq___lam__0___closed__4_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Elab_Tactic_evalRewriteSeq___lam__0___closed__4: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Elab_Tactic_evalRewriteSeq___lam__0___closed__5_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Elab_Tactic_evalRewriteSeq___lam__0___closed__5: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Elab_Tactic_evalRewriteSeq___closed__0_value: LeanCtorObject<2> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 1
                + 8) as u16,
            other: 1,
            tag: 0,
        },
        m_objs: [
            (((0 as usize) << 1) | 1) as *mut LeanObject,
            258 as *mut LeanObject,
        ],
    };
static mut l_Lean_Elab_Tactic_evalRewriteSeq___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_evalRewriteSeq___closed__0_value) as *mut LeanObject;
pub static l_Lean_Elab_Tactic_evalRewriteSeq___closed__1_value: LeanClosureObject<0> =
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
        m_fun: l_Lean_Elab_Tactic_evalRewriteSeq___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 10,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Elab_Tactic_evalRewriteSeq___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_evalRewriteSeq___closed__1_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_evalRewriteSeq___regBuiltin_Lean_Elab_Tactic_evalRewriteSeq__1___closed__0_value: LeanStringObject<7> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [84, 97, 99, 116, 105, 99, 0]};
static mut l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_evalRewriteSeq___regBuiltin_Lean_Elab_Tactic_evalRewriteSeq__1___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_evalRewriteSeq___regBuiltin_Lean_Elab_Tactic_evalRewriteSeq__1___closed__0_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_evalRewriteSeq___regBuiltin_Lean_Elab_Tactic_evalRewriteSeq__1___closed__1_value: LeanStringObject<11> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 11, m_capacity: 11, m_length: 10, m_data: [114, 101, 119, 114, 105, 116, 101, 83, 101, 113, 0]};
static mut l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_evalRewriteSeq___regBuiltin_Lean_Elab_Tactic_evalRewriteSeq__1___closed__1: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_evalRewriteSeq___regBuiltin_Lean_Elab_Tactic_evalRewriteSeq__1___closed__1_value) as *mut LeanObject;
static l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_evalRewriteSeq___regBuiltin_Lean_Elab_Tactic_evalRewriteSeq__1___closed__2_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_withRWRulesSeq_spec__1___redArg___lam__3___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_evalRewriteSeq___regBuiltin_Lean_Elab_Tactic_evalRewriteSeq__1___closed__2_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_evalRewriteSeq___regBuiltin_Lean_Elab_Tactic_evalRewriteSeq__1___closed__2_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_withRWRulesSeq_spec__1___redArg___lam__3___closed__1_value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_evalRewriteSeq___regBuiltin_Lean_Elab_Tactic_evalRewriteSeq__1___closed__2_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_evalRewriteSeq___regBuiltin_Lean_Elab_Tactic_evalRewriteSeq__1___closed__2_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_evalRewriteSeq___regBuiltin_Lean_Elab_Tactic_evalRewriteSeq__1___closed__0_value) as *mut LeanObject,18344149449936419494 as *mut LeanObject] };
pub static l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_evalRewriteSeq___regBuiltin_Lean_Elab_Tactic_evalRewriteSeq__1___closed__2_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_evalRewriteSeq___regBuiltin_Lean_Elab_Tactic_evalRewriteSeq__1___closed__2_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_evalRewriteSeq___regBuiltin_Lean_Elab_Tactic_evalRewriteSeq__1___closed__1_value) as *mut LeanObject,12565229273558214597 as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_evalRewriteSeq___regBuiltin_Lean_Elab_Tactic_evalRewriteSeq__1___closed__2: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_evalRewriteSeq___regBuiltin_Lean_Elab_Tactic_evalRewriteSeq__1___closed__2_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_evalRewriteSeq___regBuiltin_Lean_Elab_Tactic_evalRewriteSeq__1___closed__3_value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [69, 108, 97, 98, 0]};
static mut l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_evalRewriteSeq___regBuiltin_Lean_Elab_Tactic_evalRewriteSeq__1___closed__3: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_evalRewriteSeq___regBuiltin_Lean_Elab_Tactic_evalRewriteSeq__1___closed__3_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_evalRewriteSeq___regBuiltin_Lean_Elab_Tactic_evalRewriteSeq__1___closed__4_value: LeanStringObject<15> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 15, m_capacity: 15, m_length: 14, m_data: [101, 118, 97, 108, 82, 101, 119, 114, 105, 116, 101, 83, 101, 113, 0]};
static mut l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_evalRewriteSeq___regBuiltin_Lean_Elab_Tactic_evalRewriteSeq__1___closed__4: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_evalRewriteSeq___regBuiltin_Lean_Elab_Tactic_evalRewriteSeq__1___closed__4_value) as *mut LeanObject;
static l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_evalRewriteSeq___regBuiltin_Lean_Elab_Tactic_evalRewriteSeq__1___closed__5_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_withRWRulesSeq_spec__1___redArg___lam__3___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_evalRewriteSeq___regBuiltin_Lean_Elab_Tactic_evalRewriteSeq__1___closed__5_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_evalRewriteSeq___regBuiltin_Lean_Elab_Tactic_evalRewriteSeq__1___closed__5_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_evalRewriteSeq___regBuiltin_Lean_Elab_Tactic_evalRewriteSeq__1___closed__3_value) as *mut LeanObject,11510100434945111860 as *mut LeanObject] };
static l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_evalRewriteSeq___regBuiltin_Lean_Elab_Tactic_evalRewriteSeq__1___closed__5_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_evalRewriteSeq___regBuiltin_Lean_Elab_Tactic_evalRewriteSeq__1___closed__5_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_evalRewriteSeq___regBuiltin_Lean_Elab_Tactic_evalRewriteSeq__1___closed__0_value) as *mut LeanObject,12733524109236233889 as *mut LeanObject] };
pub static l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_evalRewriteSeq___regBuiltin_Lean_Elab_Tactic_evalRewriteSeq__1___closed__5_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_evalRewriteSeq___regBuiltin_Lean_Elab_Tactic_evalRewriteSeq__1___closed__5_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_evalRewriteSeq___regBuiltin_Lean_Elab_Tactic_evalRewriteSeq__1___closed__4_value) as *mut LeanObject,9150174117457099907 as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_evalRewriteSeq___regBuiltin_Lean_Elab_Tactic_evalRewriteSeq__1___closed__5: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_evalRewriteSeq___regBuiltin_Lean_Elab_Tactic_evalRewriteSeq__1___closed__5_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_evalRewriteSeq___regBuiltin_Lean_Elab_Tactic_evalRewriteSeq_declRange__3___closed__0_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 71 as usize) << 1) | 1) as *mut LeanObject,((( 48 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_evalRewriteSeq___regBuiltin_Lean_Elab_Tactic_evalRewriteSeq_declRange__3___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_evalRewriteSeq___regBuiltin_Lean_Elab_Tactic_evalRewriteSeq_declRange__3___closed__0_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_evalRewriteSeq___regBuiltin_Lean_Elab_Tactic_evalRewriteSeq_declRange__3___closed__1_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 78 as usize) << 1) | 1) as *mut LeanObject,((( 91 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_evalRewriteSeq___regBuiltin_Lean_Elab_Tactic_evalRewriteSeq_declRange__3___closed__1: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_evalRewriteSeq___regBuiltin_Lean_Elab_Tactic_evalRewriteSeq_declRange__3___closed__1_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_evalRewriteSeq___regBuiltin_Lean_Elab_Tactic_evalRewriteSeq_declRange__3___closed__2_value: LeanCtorObject<4> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*4 + 0) as u16, other: 4, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_evalRewriteSeq___regBuiltin_Lean_Elab_Tactic_evalRewriteSeq_declRange__3___closed__0_value) as *mut LeanObject,((( 48 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_evalRewriteSeq___regBuiltin_Lean_Elab_Tactic_evalRewriteSeq_declRange__3___closed__1_value) as *mut LeanObject,((( 91 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_evalRewriteSeq___regBuiltin_Lean_Elab_Tactic_evalRewriteSeq_declRange__3___closed__2: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_evalRewriteSeq___regBuiltin_Lean_Elab_Tactic_evalRewriteSeq_declRange__3___closed__2_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_evalRewriteSeq___regBuiltin_Lean_Elab_Tactic_evalRewriteSeq_declRange__3___closed__3_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 71 as usize) << 1) | 1) as *mut LeanObject,((( 52 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_evalRewriteSeq___regBuiltin_Lean_Elab_Tactic_evalRewriteSeq_declRange__3___closed__3: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_evalRewriteSeq___regBuiltin_Lean_Elab_Tactic_evalRewriteSeq_declRange__3___closed__3_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_evalRewriteSeq___regBuiltin_Lean_Elab_Tactic_evalRewriteSeq_declRange__3___closed__4_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 71 as usize) << 1) | 1) as *mut LeanObject,((( 66 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_evalRewriteSeq___regBuiltin_Lean_Elab_Tactic_evalRewriteSeq_declRange__3___closed__4: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_evalRewriteSeq___regBuiltin_Lean_Elab_Tactic_evalRewriteSeq_declRange__3___closed__4_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_evalRewriteSeq___regBuiltin_Lean_Elab_Tactic_evalRewriteSeq_declRange__3___closed__5_value: LeanCtorObject<4> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*4 + 0) as u16, other: 4, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_evalRewriteSeq___regBuiltin_Lean_Elab_Tactic_evalRewriteSeq_declRange__3___closed__3_value) as *mut LeanObject,((( 52 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_evalRewriteSeq___regBuiltin_Lean_Elab_Tactic_evalRewriteSeq_declRange__3___closed__4_value) as *mut LeanObject,((( 66 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_evalRewriteSeq___regBuiltin_Lean_Elab_Tactic_evalRewriteSeq_declRange__3___closed__5: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_evalRewriteSeq___regBuiltin_Lean_Elab_Tactic_evalRewriteSeq_declRange__3___closed__5_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_evalRewriteSeq___regBuiltin_Lean_Elab_Tactic_evalRewriteSeq_declRange__3___closed__6_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_evalRewriteSeq___regBuiltin_Lean_Elab_Tactic_evalRewriteSeq_declRange__3___closed__2_value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_evalRewriteSeq___regBuiltin_Lean_Elab_Tactic_evalRewriteSeq_declRange__3___closed__5_value) as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_evalRewriteSeq___regBuiltin_Lean_Elab_Tactic_evalRewriteSeq_declRange__3___closed__6: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_evalRewriteSeq___regBuiltin_Lean_Elab_Tactic_evalRewriteSeq_declRange__3___closed__6_value) as *mut LeanObject;
pub unsafe fn l_Lean_Meta_withInstancesTypeCheckNote___at___00Lean_Elab_Tactic_elabRewrite_spec__0___redArg___lam__0(
    mut v_x_4328_: *mut LeanObject,
    mut v___y_4329_: *mut LeanObject,
    mut v___y_4330_: *mut LeanObject,
    mut v___y_4331_: *mut LeanObject,
    mut v___y_4332_: *mut LeanObject,
    mut v___y_4333_: *mut LeanObject,
    mut v___y_4334_: *mut LeanObject,
    mut v___y_4335_: *mut LeanObject,
    mut v___y_4336_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4338_: *mut LeanObject = core::ptr::null_mut();
    lean_inc(v___y_4332_);
    lean_inc_ref(v___y_4331_);
    lean_inc(v___y_4330_);
    lean_inc_ref(v___y_4329_);
    v___x_4338_ = lean_apply_9(
        v_x_4328_,
        v___y_4329_,
        v___y_4330_,
        v___y_4331_,
        v___y_4332_,
        v___y_4333_,
        v___y_4334_,
        v___y_4335_,
        v___y_4336_,
        lean_box(0),
    );
    return v___x_4338_;
}
pub unsafe fn l_Lean_Meta_withInstancesTypeCheckNote___at___00Lean_Elab_Tactic_elabRewrite_spec__0___redArg___lam__0___boxed(
    mut v_x_4339_: *mut LeanObject,
    mut v___y_4340_: *mut LeanObject,
    mut v___y_4341_: *mut LeanObject,
    mut v___y_4342_: *mut LeanObject,
    mut v___y_4343_: *mut LeanObject,
    mut v___y_4344_: *mut LeanObject,
    mut v___y_4345_: *mut LeanObject,
    mut v___y_4346_: *mut LeanObject,
    mut v___y_4347_: *mut LeanObject,
    mut v___y_4348_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4349_: *mut LeanObject = core::ptr::null_mut();
    v_res_4349_ = l_Lean_Meta_withInstancesTypeCheckNote___at___00Lean_Elab_Tactic_elabRewrite_spec__0___redArg___lam__0(v_x_4339_, v___y_4340_, v___y_4341_, v___y_4342_, v___y_4343_, v___y_4344_, v___y_4345_, v___y_4346_, v___y_4347_);
    lean_dec(v___y_4343_);
    lean_dec_ref(v___y_4342_);
    lean_dec(v___y_4341_);
    lean_dec_ref(v___y_4340_);
    return v_res_4349_;
}
pub unsafe fn _init_l_Lean_Meta_withInstancesTypeCheckNote___at___00Lean_Elab_Tactic_elabRewrite_spec__0___redArg___lam__1___closed__1()
-> *mut LeanObject {
    let mut v___x_4351_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4352_: *mut LeanObject = core::ptr::null_mut();
    v___x_4351_ = l_Lean_Meta_withInstancesTypeCheckNote___at___00Lean_Elab_Tactic_elabRewrite_spec__0___redArg___lam__1___closed__0;
    v___x_4352_ = l_Lean_stringToMessageData(v___x_4351_);
    return v___x_4352_;
}
pub unsafe fn l_Lean_Meta_withInstancesTypeCheckNote___at___00Lean_Elab_Tactic_elabRewrite_spec__0___redArg___lam__1(
    mut v_e_4353_: *mut LeanObject,
    mut v___x_4354_: u8,
    mut v___y_4355_: *mut LeanObject,
    mut v___y_4356_: *mut LeanObject,
    mut v___y_4357_: *mut LeanObject,
    mut v___y_4358_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4360_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4362_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4363_: u8 = 0;
    let mut v___x_4364_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4366_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4367_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4368_: u8 = 0;
    let mut v_unused_4369_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4370_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4372_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4373_: u8 = 0;
    let mut v___y_4375_: u8 = 0;
    let mut v___x_4376_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4377_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4378_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4379_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4380_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4382_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4383_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4385_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4386_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4387_: u8 = 0;
    let mut v___x_4388_: u8 = 0;
    let mut v_isSharedCheck_4389_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4360_ = l_Lean_Meta_check(
                    v_e_4353_,
                    v___x_4354_,
                    v___y_4355_,
                    v___y_4356_,
                    v___y_4357_,
                    v___y_4358_,
                );
                if lean_obj_tag(v___x_4360_) == 0 {
                    v_isSharedCheck_4368_ = (!lean_is_exclusive(v___x_4360_)) as u8;
                    if v_isSharedCheck_4368_ == 0 {
                        v_unused_4369_ = lean_ctor_get(v___x_4360_, 0);
                        lean_dec(v_unused_4369_);
                        v___x_4362_ = v___x_4360_;
                        v_isShared_4363_ = v_isSharedCheck_4368_;
                        state = 1;
                        continue;
                    } else {
                        lean_dec(v___x_4360_);
                        v___x_4362_ = lean_box(0);
                        v_isShared_4363_ = v_isSharedCheck_4368_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_4370_ = lean_ctor_get(v___x_4360_, 0);
                    v_isSharedCheck_4389_ = (!lean_is_exclusive(v___x_4360_)) as u8;
                    if v_isSharedCheck_4389_ == 0 {
                        v___x_4372_ = v___x_4360_;
                        v_isShared_4373_ = v_isSharedCheck_4389_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_4370_);
                        lean_dec(v___x_4360_);
                        v___x_4372_ = lean_box(0);
                        v_isShared_4373_ = v_isSharedCheck_4389_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v___x_4364_ = l_Lean_MessageData_nil;
                if v_isShared_4363_ == 0 {
                    lean_ctor_set(v___x_4362_, 0, v___x_4364_);
                    v___x_4366_ = v___x_4362_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4367_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4367_, 0, v___x_4364_);
                    v___x_4366_ = v_reuseFailAlloc_4367_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_4366_;
            }
            3 => {
                v___x_4387_ = l_Lean_Exception_isInterrupt(v_a_4370_);
                if v___x_4387_ == 0 {
                    lean_inc(v_a_4370_);
                    v___x_4388_ = l_Lean_Exception_isRuntime(v_a_4370_);
                    v___y_4375_ = v___x_4388_;
                    state = 4;
                    continue;
                } else {
                    v___y_4375_ = v___x_4387_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                if v___y_4375_ == 0 {
                    v___x_4376_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Meta_withInstancesTypeCheckNote___at___00Lean_Elab_Tactic_elabRewrite_spec__0___redArg___lam__1___closed__1), core::ptr::addr_of_mut!(l_Lean_Meta_withInstancesTypeCheckNote___at___00Lean_Elab_Tactic_elabRewrite_spec__0___redArg___lam__1___closed__1_once), _init_l_Lean_Meta_withInstancesTypeCheckNote___at___00Lean_Elab_Tactic_elabRewrite_spec__0___redArg___lam__1___closed__1);
                    v___x_4377_ = l_Lean_Exception_toMessageData(v_a_4370_);
                    v___x_4378_ = l_Lean_indentD(v___x_4377_);
                    v___x_4379_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_4379_, 0, v___x_4376_);
                    lean_ctor_set(v___x_4379_, 1, v___x_4378_);
                    v___x_4380_ = l_Lean_MessageData_note(v___x_4379_);
                    if v_isShared_4373_ == 0 {
                        lean_ctor_set_tag(v___x_4372_, 0);
                        lean_ctor_set(v___x_4372_, 0, v___x_4380_);
                        v___x_4382_ = v___x_4372_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_4383_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_4383_, 0, v___x_4380_);
                        v___x_4382_ = v_reuseFailAlloc_4383_;
                        state = 5;
                        continue;
                    }
                } else {
                    if v_isShared_4373_ == 0 {
                        v___x_4385_ = v___x_4372_;
                        state = 6;
                        continue;
                    } else {
                        v_reuseFailAlloc_4386_ = lean_alloc_ctor(1, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_4386_, 0, v_a_4370_);
                        v___x_4385_ = v_reuseFailAlloc_4386_;
                        state = 6;
                        continue;
                    }
                }
            }
            5 => {
                return v___x_4382_;
            }
            6 => {
                return v___x_4385_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_withInstancesTypeCheckNote___at___00Lean_Elab_Tactic_elabRewrite_spec__0___redArg___lam__1___boxed(
    mut v_e_4390_: *mut LeanObject,
    mut v___x_4391_: *mut LeanObject,
    mut v___y_4392_: *mut LeanObject,
    mut v___y_4393_: *mut LeanObject,
    mut v___y_4394_: *mut LeanObject,
    mut v___y_4395_: *mut LeanObject,
    mut v___y_4396_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_12854__boxed_4397_: u8 = 0;
    let mut v_res_4398_: *mut LeanObject = core::ptr::null_mut();
    v___x_12854__boxed_4397_ = (lean_unbox(v___x_4391_) as u8);
    v_res_4398_ = l_Lean_Meta_withInstancesTypeCheckNote___at___00Lean_Elab_Tactic_elabRewrite_spec__0___redArg___lam__1(v_e_4390_, v___x_12854__boxed_4397_, v___y_4392_, v___y_4393_, v___y_4394_, v___y_4395_);
    lean_dec(v___y_4395_);
    lean_dec_ref(v___y_4394_);
    lean_dec(v___y_4393_);
    lean_dec_ref(v___y_4392_);
    return v_res_4398_;
}
pub unsafe fn l_Lean_Meta_withInstancesTypeCheckNote___at___00Lean_Elab_Tactic_elabRewrite_spec__0___redArg___lam__2(
    mut v_typeCheckNote_4399_: *mut LeanObject,
    mut v_x_4400_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4401_: *mut LeanObject = core::ptr::null_mut();
    v___x_4401_ = lean_alloc_ctor(7, 2, (0) as u32);
    lean_ctor_set(v___x_4401_, 0, v_x_4400_);
    lean_ctor_set(v___x_4401_, 1, v_typeCheckNote_4399_);
    return v___x_4401_;
}
pub unsafe fn l_Lean_Meta_withInstancesTypeCheckNote___at___00Lean_Elab_Tactic_elabRewrite_spec__0___redArg(
    mut v_e_4402_: *mut LeanObject,
    mut v_x_4403_: *mut LeanObject,
    mut v___y_4404_: *mut LeanObject,
    mut v___y_4405_: *mut LeanObject,
    mut v___y_4406_: *mut LeanObject,
    mut v___y_4407_: *mut LeanObject,
    mut v___y_4408_: *mut LeanObject,
    mut v___y_4409_: *mut LeanObject,
    mut v___y_4410_: *mut LeanObject,
    mut v___y_4411_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_4413_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4414_: u8 = 0;
    let mut v___x_4415_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_4416_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4417_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4418_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4419_: *mut LeanObject = core::ptr::null_mut();
    let mut v_typeCheckNote_4420_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_4421_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4422_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4423_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4425_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4426_: u8 = 0;
    let mut v___x_4428_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4429_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4430_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                lean_inc(v___y_4407_);
                lean_inc_ref(v___y_4406_);
                lean_inc(v___y_4405_);
                lean_inc_ref(v___y_4404_);
                v___f_4413_ = lean_alloc_closure(l_Lean_Meta_withInstancesTypeCheckNote___at___00Lean_Elab_Tactic_elabRewrite_spec__0___redArg___lam__0___boxed as *mut core::ffi::c_void, 10, 5);
                lean_closure_set(v___f_4413_, 0, v_x_4403_);
                lean_closure_set(v___f_4413_, 1, v___y_4404_);
                lean_closure_set(v___f_4413_, 2, v___y_4405_);
                lean_closure_set(v___f_4413_, 3, v___y_4406_);
                lean_closure_set(v___f_4413_, 4, v___y_4407_);
                v___x_4414_ = 3;
                v___x_4415_ = lean_box((v___x_4414_) as usize);
                lean_inc_ref(v_e_4402_);
                v___f_4416_ = lean_alloc_closure(l_Lean_Meta_withInstancesTypeCheckNote___at___00Lean_Elab_Tactic_elabRewrite_spec__0___redArg___lam__1___boxed as *mut core::ffi::c_void, 7, 2);
                lean_closure_set(v___f_4416_, 0, v_e_4402_);
                lean_closure_set(v___f_4416_, 1, v___x_4415_);
                v___x_4417_ = lean_unsigned_to_nat(1);
                v___x_4418_ = lean_mk_empty_array_with_capacity(v___x_4417_);
                v___x_4419_ = lean_array_push(v___x_4418_, v_e_4402_);
                v_typeCheckNote_4420_ = l_Lean_MessageData_ofLazyM(v___f_4416_, v___x_4419_);
                v___f_4421_ = lean_alloc_closure(l_Lean_Meta_withInstancesTypeCheckNote___at___00Lean_Elab_Tactic_elabRewrite_spec__0___redArg___lam__2 as *mut core::ffi::c_void, 2, 1);
                lean_closure_set(v___f_4421_, 0, v_typeCheckNote_4420_);
                v___x_4422_ = l_Lean_Meta_mapErrorImp___redArg(
                    v___f_4413_,
                    v___f_4421_,
                    v___y_4408_,
                    v___y_4409_,
                    v___y_4410_,
                    v___y_4411_,
                );
                if lean_obj_tag(v___x_4422_) == 0 {
                    return v___x_4422_;
                } else {
                    v_a_4423_ = lean_ctor_get(v___x_4422_, 0);
                    v_isSharedCheck_4430_ = (!lean_is_exclusive(v___x_4422_)) as u8;
                    if v_isSharedCheck_4430_ == 0 {
                        v___x_4425_ = v___x_4422_;
                        v_isShared_4426_ = v_isSharedCheck_4430_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_4423_);
                        lean_dec(v___x_4422_);
                        v___x_4425_ = lean_box(0);
                        v_isShared_4426_ = v_isSharedCheck_4430_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_4426_ == 0 {
                    v___x_4428_ = v___x_4425_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4429_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4429_, 0, v_a_4423_);
                    v___x_4428_ = v_reuseFailAlloc_4429_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_4428_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_withInstancesTypeCheckNote___at___00Lean_Elab_Tactic_elabRewrite_spec__0___redArg___boxed(
    mut v_e_4431_: *mut LeanObject,
    mut v_x_4432_: *mut LeanObject,
    mut v___y_4433_: *mut LeanObject,
    mut v___y_4434_: *mut LeanObject,
    mut v___y_4435_: *mut LeanObject,
    mut v___y_4436_: *mut LeanObject,
    mut v___y_4437_: *mut LeanObject,
    mut v___y_4438_: *mut LeanObject,
    mut v___y_4439_: *mut LeanObject,
    mut v___y_4440_: *mut LeanObject,
    mut v___y_4441_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4442_: *mut LeanObject = core::ptr::null_mut();
    v_res_4442_ = l_Lean_Meta_withInstancesTypeCheckNote___at___00Lean_Elab_Tactic_elabRewrite_spec__0___redArg(v_e_4431_, v_x_4432_, v___y_4433_, v___y_4434_, v___y_4435_, v___y_4436_, v___y_4437_, v___y_4438_, v___y_4439_, v___y_4440_);
    lean_dec(v___y_4440_);
    lean_dec_ref(v___y_4439_);
    lean_dec(v___y_4438_);
    lean_dec_ref(v___y_4437_);
    lean_dec(v___y_4436_);
    lean_dec_ref(v___y_4435_);
    lean_dec(v___y_4434_);
    lean_dec_ref(v___y_4433_);
    return v_res_4442_;
}
pub unsafe fn l_Lean_Meta_withInstancesTypeCheckNote___at___00Lean_Elab_Tactic_elabRewrite_spec__0(
    mut v_00_u03b1_4443_: *mut LeanObject,
    mut v_e_4444_: *mut LeanObject,
    mut v_x_4445_: *mut LeanObject,
    mut v___y_4446_: *mut LeanObject,
    mut v___y_4447_: *mut LeanObject,
    mut v___y_4448_: *mut LeanObject,
    mut v___y_4449_: *mut LeanObject,
    mut v___y_4450_: *mut LeanObject,
    mut v___y_4451_: *mut LeanObject,
    mut v___y_4452_: *mut LeanObject,
    mut v___y_4453_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4455_: *mut LeanObject = core::ptr::null_mut();
    v___x_4455_ = l_Lean_Meta_withInstancesTypeCheckNote___at___00Lean_Elab_Tactic_elabRewrite_spec__0___redArg(v_e_4444_, v_x_4445_, v___y_4446_, v___y_4447_, v___y_4448_, v___y_4449_, v___y_4450_, v___y_4451_, v___y_4452_, v___y_4453_);
    return v___x_4455_;
}
pub unsafe fn l_Lean_Meta_withInstancesTypeCheckNote___at___00Lean_Elab_Tactic_elabRewrite_spec__0___boxed(
    mut v_00_u03b1_4456_: *mut LeanObject,
    mut v_e_4457_: *mut LeanObject,
    mut v_x_4458_: *mut LeanObject,
    mut v___y_4459_: *mut LeanObject,
    mut v___y_4460_: *mut LeanObject,
    mut v___y_4461_: *mut LeanObject,
    mut v___y_4462_: *mut LeanObject,
    mut v___y_4463_: *mut LeanObject,
    mut v___y_4464_: *mut LeanObject,
    mut v___y_4465_: *mut LeanObject,
    mut v___y_4466_: *mut LeanObject,
    mut v___y_4467_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4468_: *mut LeanObject = core::ptr::null_mut();
    v_res_4468_ =
        l_Lean_Meta_withInstancesTypeCheckNote___at___00Lean_Elab_Tactic_elabRewrite_spec__0(
            v_00_u03b1_4456_,
            v_e_4457_,
            v_x_4458_,
            v___y_4459_,
            v___y_4460_,
            v___y_4461_,
            v___y_4462_,
            v___y_4463_,
            v___y_4464_,
            v___y_4465_,
            v___y_4466_,
        );
    lean_dec(v___y_4466_);
    lean_dec_ref(v___y_4465_);
    lean_dec(v___y_4464_);
    lean_dec_ref(v___y_4463_);
    lean_dec(v___y_4462_);
    lean_dec_ref(v___y_4461_);
    lean_dec(v___y_4460_);
    lean_dec_ref(v___y_4459_);
    return v_res_4468_;
}
pub unsafe fn _init_l_Lean_Elab_throwAbortTactic___at___00Lean_Elab_Tactic_elabRewrite_spec__4___redArg___closed__0()
-> *mut LeanObject {
    let mut v___x_4469_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4470_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4471_: *mut LeanObject = core::ptr::null_mut();
    v___x_4469_ = lean_box(0);
    v___x_4470_ = l_Lean_Elab_abortTacticExceptionId;
    v___x_4471_ = lean_alloc_ctor(1, 2, (0) as u32);
    lean_ctor_set(v___x_4471_, 0, v___x_4470_);
    lean_ctor_set(v___x_4471_, 1, v___x_4469_);
    return v___x_4471_;
}
pub unsafe fn l_Lean_Elab_throwAbortTactic___at___00Lean_Elab_Tactic_elabRewrite_spec__4___redArg()
-> *mut LeanObject {
    let mut v___x_4473_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4474_: *mut LeanObject = core::ptr::null_mut();
    v___x_4473_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_throwAbortTactic___at___00Lean_Elab_Tactic_elabRewrite_spec__4___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_Elab_throwAbortTactic___at___00Lean_Elab_Tactic_elabRewrite_spec__4___redArg___closed__0_once), _init_l_Lean_Elab_throwAbortTactic___at___00Lean_Elab_Tactic_elabRewrite_spec__4___redArg___closed__0);
    v___x_4474_ = lean_alloc_ctor(1, 1, (0) as u32);
    lean_ctor_set(v___x_4474_, 0, v___x_4473_);
    return v___x_4474_;
}
pub unsafe fn l_Lean_Elab_throwAbortTactic___at___00Lean_Elab_Tactic_elabRewrite_spec__4___redArg___boxed(
    mut v___y_4475_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4476_: *mut LeanObject = core::ptr::null_mut();
    v_res_4476_ =
        l_Lean_Elab_throwAbortTactic___at___00Lean_Elab_Tactic_elabRewrite_spec__4___redArg();
    return v_res_4476_;
}
pub unsafe fn l_Lean_Elab_throwAbortTactic___at___00Lean_Elab_Tactic_elabRewrite_spec__4(
    mut v_00_u03b1_4477_: *mut LeanObject,
    mut v___y_4478_: *mut LeanObject,
    mut v___y_4479_: *mut LeanObject,
    mut v___y_4480_: *mut LeanObject,
    mut v___y_4481_: *mut LeanObject,
    mut v___y_4482_: *mut LeanObject,
    mut v___y_4483_: *mut LeanObject,
    mut v___y_4484_: *mut LeanObject,
    mut v___y_4485_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4487_: *mut LeanObject = core::ptr::null_mut();
    v___x_4487_ =
        l_Lean_Elab_throwAbortTactic___at___00Lean_Elab_Tactic_elabRewrite_spec__4___redArg();
    return v___x_4487_;
}
pub unsafe fn l_Lean_Elab_throwAbortTactic___at___00Lean_Elab_Tactic_elabRewrite_spec__4___boxed(
    mut v_00_u03b1_4488_: *mut LeanObject,
    mut v___y_4489_: *mut LeanObject,
    mut v___y_4490_: *mut LeanObject,
    mut v___y_4491_: *mut LeanObject,
    mut v___y_4492_: *mut LeanObject,
    mut v___y_4493_: *mut LeanObject,
    mut v___y_4494_: *mut LeanObject,
    mut v___y_4495_: *mut LeanObject,
    mut v___y_4496_: *mut LeanObject,
    mut v___y_4497_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4498_: *mut LeanObject = core::ptr::null_mut();
    v_res_4498_ = l_Lean_Elab_throwAbortTactic___at___00Lean_Elab_Tactic_elabRewrite_spec__4(
        v_00_u03b1_4488_,
        v___y_4489_,
        v___y_4490_,
        v___y_4491_,
        v___y_4492_,
        v___y_4493_,
        v___y_4494_,
        v___y_4495_,
        v___y_4496_,
    );
    lean_dec(v___y_4496_);
    lean_dec_ref(v___y_4495_);
    lean_dec(v___y_4494_);
    lean_dec_ref(v___y_4493_);
    lean_dec(v___y_4492_);
    lean_dec_ref(v___y_4491_);
    lean_dec(v___y_4490_);
    lean_dec_ref(v___y_4489_);
    return v_res_4498_;
}
pub unsafe fn l_Lean_Elab_Tactic_elabRewrite___lam__0(
    mut v_mvarId_4499_: *mut LeanObject,
    mut v_e_4500_: *mut LeanObject,
    mut v_a_4501_: *mut LeanObject,
    mut v_symm_4502_: u8,
    mut v_config_4503_: *mut LeanObject,
    mut v___y_4504_: *mut LeanObject,
    mut v___y_4505_: *mut LeanObject,
    mut v___y_4506_: *mut LeanObject,
    mut v___y_4507_: *mut LeanObject,
    mut v___y_4508_: *mut LeanObject,
    mut v___y_4509_: *mut LeanObject,
    mut v___y_4510_: *mut LeanObject,
    mut v___y_4511_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4513_: *mut LeanObject = core::ptr::null_mut();
    v___x_4513_ = l_Lean_MVarId_rewrite(
        v_mvarId_4499_,
        v_e_4500_,
        v_a_4501_,
        v_symm_4502_,
        v_config_4503_,
        v___y_4508_,
        v___y_4509_,
        v___y_4510_,
        v___y_4511_,
    );
    return v___x_4513_;
}
pub unsafe fn l_Lean_Elab_Tactic_elabRewrite___lam__0___boxed(
    mut v_mvarId_4514_: *mut LeanObject,
    mut v_e_4515_: *mut LeanObject,
    mut v_a_4516_: *mut LeanObject,
    mut v_symm_4517_: *mut LeanObject,
    mut v_config_4518_: *mut LeanObject,
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
    let mut v_symm_boxed_4528_: u8 = 0;
    let mut v_res_4529_: *mut LeanObject = core::ptr::null_mut();
    v_symm_boxed_4528_ = (lean_unbox(v_symm_4517_) as u8);
    v_res_4529_ = l_Lean_Elab_Tactic_elabRewrite___lam__0(
        v_mvarId_4514_,
        v_e_4515_,
        v_a_4516_,
        v_symm_boxed_4528_,
        v_config_4518_,
        v___y_4519_,
        v___y_4520_,
        v___y_4521_,
        v___y_4522_,
        v___y_4523_,
        v___y_4524_,
        v___y_4525_,
        v___y_4526_,
    );
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
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_elabRewrite_spec__2_spec__2_spec__4_spec__6___redArg(
    mut v_a_4530_: *mut LeanObject,
    mut v_x_4531_: *mut LeanObject,
) -> u8 {
    let mut v___x_4532_: u8 = 0;
    let mut v_key_4533_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_4534_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4535_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_4531_) == 0 {
                    v___x_4532_ = 0;
                    return v___x_4532_;
                } else {
                    v_key_4533_ = lean_ctor_get(v_x_4531_, 0);
                    v_tail_4534_ = lean_ctor_get(v_x_4531_, 2);
                    v___x_4535_ = lean_expr_eqv(v_key_4533_, v_a_4530_);
                    if v___x_4535_ == 0 {
                        v_x_4531_ = v_tail_4534_;
                        state = 0;
                        continue;
                    } else {
                        return v___x_4535_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_elabRewrite_spec__2_spec__2_spec__4_spec__6___redArg___boxed(
    mut v_a_4537_: *mut LeanObject,
    mut v_x_4538_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4539_: u8 = 0;
    let mut v_r_4540_: *mut LeanObject = core::ptr::null_mut();
    v_res_4539_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_elabRewrite_spec__2_spec__2_spec__4_spec__6___redArg(v_a_4537_, v_x_4538_);
    lean_dec(v_x_4538_);
    lean_dec_ref(v_a_4537_);
    v_r_4540_ = lean_box((v_res_4539_) as usize);
    return v_r_4540_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_elabRewrite_spec__2_spec__2_spec__4___redArg(
    mut v_m_4541_: *mut LeanObject,
    mut v_a_4542_: *mut LeanObject,
) -> u8 {
    let mut v_buckets_4543_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4544_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4545_: u64 = 0;
    let mut v___x_4546_: u64 = 0;
    let mut v___x_4547_: u64 = 0;
    let mut v_fold_4548_: u64 = 0;
    let mut v___x_4549_: u64 = 0;
    let mut v___x_4550_: u64 = 0;
    let mut v___x_4551_: u64 = 0;
    let mut v___x_4552_: usize = 0;
    let mut v___x_4553_: usize = 0;
    let mut v___x_4554_: usize = 0;
    let mut v___x_4555_: usize = 0;
    let mut v___x_4556_: usize = 0;
    let mut v___x_4557_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4558_: u8 = 0;
    v_buckets_4543_ = lean_ctor_get(v_m_4541_, 1);
    v___x_4544_ = lean_array_get_size(v_buckets_4543_);
    v___x_4545_ = l_Lean_Expr_hash(v_a_4542_);
    v___x_4546_ = 32u64;
    v___x_4547_ = lean_uint64_shift_right(v___x_4545_, v___x_4546_);
    v_fold_4548_ = lean_uint64_xor(v___x_4545_, v___x_4547_);
    v___x_4549_ = 16u64;
    v___x_4550_ = lean_uint64_shift_right(v_fold_4548_, v___x_4549_);
    v___x_4551_ = lean_uint64_xor(v_fold_4548_, v___x_4550_);
    v___x_4552_ = lean_uint64_to_usize(v___x_4551_);
    v___x_4553_ = lean_usize_of_nat(v___x_4544_);
    v___x_4554_ = 1usize;
    v___x_4555_ = lean_usize_sub(v___x_4553_, v___x_4554_);
    v___x_4556_ = lean_usize_land(v___x_4552_, v___x_4555_);
    v___x_4557_ = lean_array_uget_borrowed(v_buckets_4543_, v___x_4556_);
    v___x_4558_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_elabRewrite_spec__2_spec__2_spec__4_spec__6___redArg(v_a_4542_, v___x_4557_);
    return v___x_4558_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_elabRewrite_spec__2_spec__2_spec__4___redArg___boxed(
    mut v_m_4559_: *mut LeanObject,
    mut v_a_4560_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4561_: u8 = 0;
    let mut v_r_4562_: *mut LeanObject = core::ptr::null_mut();
    v_res_4561_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_elabRewrite_spec__2_spec__2_spec__4___redArg(v_m_4559_, v_a_4560_);
    lean_dec_ref(v_a_4560_);
    lean_dec_ref(v_m_4559_);
    v_r_4562_ = lean_box((v_res_4561_) as usize);
    return v_r_4562_;
}
pub unsafe fn l_Lean_getDelayedMVarAssignment_x3f___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_elabRewrite_spec__2_spec__2_spec__6_spec__11___redArg(
    mut v_mvarId_4563_: *mut LeanObject,
    mut v___y_4564_: *mut LeanObject,
    mut v___y_4565_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4567_: *mut LeanObject = core::ptr::null_mut();
    let mut v_mctx_4568_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4569_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4570_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4571_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4572_: *mut LeanObject = core::ptr::null_mut();
    v___x_4567_ = lean_st_ref_get(v___y_4565_);
    v_mctx_4568_ = lean_ctor_get(v___x_4567_, 0);
    lean_inc_ref(v_mctx_4568_);
    lean_dec(v___x_4567_);
    v___x_4569_ =
        l_Lean_MetavarContext_getDelayedMVarAssignmentCore_x3f(v_mctx_4568_, v_mvarId_4563_);
    lean_dec_ref(v_mctx_4568_);
    v___x_4570_ = lean_alloc_ctor(1, 1, (0) as u32);
    lean_ctor_set(v___x_4570_, 0, v___x_4569_);
    v___x_4571_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_4571_, 0, v___x_4570_);
    lean_ctor_set(v___x_4571_, 1, v___y_4564_);
    v___x_4572_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_4572_, 0, v___x_4571_);
    return v___x_4572_;
}
pub unsafe fn l_Lean_getDelayedMVarAssignment_x3f___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_elabRewrite_spec__2_spec__2_spec__6_spec__11___redArg___boxed(
    mut v_mvarId_4573_: *mut LeanObject,
    mut v___y_4574_: *mut LeanObject,
    mut v___y_4575_: *mut LeanObject,
    mut v___y_4576_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4577_: *mut LeanObject = core::ptr::null_mut();
    v_res_4577_ = l_Lean_getDelayedMVarAssignment_x3f___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_elabRewrite_spec__2_spec__2_spec__6_spec__11___redArg(v_mvarId_4573_, v___y_4574_, v___y_4575_);
    lean_dec(v___y_4575_);
    lean_dec(v_mvarId_4573_);
    return v_res_4577_;
}
pub unsafe fn l_Lean_getExprMVarAssignment_x3f___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_elabRewrite_spec__2_spec__2_spec__6_spec__10___redArg(
    mut v_mvarId_4578_: *mut LeanObject,
    mut v___y_4579_: *mut LeanObject,
    mut v___y_4580_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4582_: *mut LeanObject = core::ptr::null_mut();
    let mut v_mctx_4583_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4584_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4585_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4586_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4587_: *mut LeanObject = core::ptr::null_mut();
    v___x_4582_ = lean_st_ref_get(v___y_4580_);
    v_mctx_4583_ = lean_ctor_get(v___x_4582_, 0);
    lean_inc_ref(v_mctx_4583_);
    lean_dec(v___x_4582_);
    v___x_4584_ = l_Lean_MetavarContext_getExprAssignmentCore_x3f(v_mctx_4583_, v_mvarId_4578_);
    lean_dec_ref(v_mctx_4583_);
    v___x_4585_ = lean_alloc_ctor(1, 1, (0) as u32);
    lean_ctor_set(v___x_4585_, 0, v___x_4584_);
    v___x_4586_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_4586_, 0, v___x_4585_);
    lean_ctor_set(v___x_4586_, 1, v___y_4579_);
    v___x_4587_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_4587_, 0, v___x_4586_);
    return v___x_4587_;
}
pub unsafe fn l_Lean_getExprMVarAssignment_x3f___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_elabRewrite_spec__2_spec__2_spec__6_spec__10___redArg___boxed(
    mut v_mvarId_4588_: *mut LeanObject,
    mut v___y_4589_: *mut LeanObject,
    mut v___y_4590_: *mut LeanObject,
    mut v___y_4591_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4592_: *mut LeanObject = core::ptr::null_mut();
    v_res_4592_ = l_Lean_getExprMVarAssignment_x3f___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_elabRewrite_spec__2_spec__2_spec__6_spec__10___redArg(v_mvarId_4588_, v___y_4589_, v___y_4590_);
    lean_dec(v___y_4590_);
    lean_dec(v_mvarId_4588_);
    return v_res_4592_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_elabRewrite_spec__2_spec__2_spec__5_spec__8_spec__11_spec__15___redArg(
    mut v_x_4593_: *mut LeanObject,
    mut v_x_4594_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_key_4595_: *mut LeanObject = core::ptr::null_mut();
    let mut v_value_4596_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_4597_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4599_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4600_: u8 = 0;
    let mut v___x_4601_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4602_: u64 = 0;
    let mut v___x_4603_: u64 = 0;
    let mut v___x_4604_: u64 = 0;
    let mut v_fold_4605_: u64 = 0;
    let mut v___x_4606_: u64 = 0;
    let mut v___x_4607_: u64 = 0;
    let mut v___x_4608_: u64 = 0;
    let mut v___x_4609_: usize = 0;
    let mut v___x_4610_: usize = 0;
    let mut v___x_4611_: usize = 0;
    let mut v___x_4612_: usize = 0;
    let mut v___x_4613_: usize = 0;
    let mut v___x_4614_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4616_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4617_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4619_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4620_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_4594_) == 0 {
                    return v_x_4593_;
                } else {
                    v_key_4595_ = lean_ctor_get(v_x_4594_, 0);
                    v_value_4596_ = lean_ctor_get(v_x_4594_, 1);
                    v_tail_4597_ = lean_ctor_get(v_x_4594_, 2);
                    v_isSharedCheck_4620_ = (!lean_is_exclusive(v_x_4594_)) as u8;
                    if v_isSharedCheck_4620_ == 0 {
                        v___x_4599_ = v_x_4594_;
                        v_isShared_4600_ = v_isSharedCheck_4620_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_tail_4597_);
                        lean_inc(v_value_4596_);
                        lean_inc(v_key_4595_);
                        lean_dec(v_x_4594_);
                        v___x_4599_ = lean_box(0);
                        v_isShared_4600_ = v_isSharedCheck_4620_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_4601_ = lean_array_get_size(v_x_4593_);
                v___x_4602_ = l_Lean_Expr_hash(v_key_4595_);
                v___x_4603_ = 32u64;
                v___x_4604_ = lean_uint64_shift_right(v___x_4602_, v___x_4603_);
                v_fold_4605_ = lean_uint64_xor(v___x_4602_, v___x_4604_);
                v___x_4606_ = 16u64;
                v___x_4607_ = lean_uint64_shift_right(v_fold_4605_, v___x_4606_);
                v___x_4608_ = lean_uint64_xor(v_fold_4605_, v___x_4607_);
                v___x_4609_ = lean_uint64_to_usize(v___x_4608_);
                v___x_4610_ = lean_usize_of_nat(v___x_4601_);
                v___x_4611_ = 1usize;
                v___x_4612_ = lean_usize_sub(v___x_4610_, v___x_4611_);
                v___x_4613_ = lean_usize_land(v___x_4609_, v___x_4612_);
                v___x_4614_ = lean_array_uget_borrowed(v_x_4593_, v___x_4613_);
                lean_inc(v___x_4614_);
                if v_isShared_4600_ == 0 {
                    lean_ctor_set(v___x_4599_, 2, v___x_4614_);
                    v___x_4616_ = v___x_4599_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4619_ = lean_alloc_ctor(1, 3, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4619_, 0, v_key_4595_);
                    lean_ctor_set(v_reuseFailAlloc_4619_, 1, v_value_4596_);
                    lean_ctor_set(v_reuseFailAlloc_4619_, 2, v___x_4614_);
                    v___x_4616_ = v_reuseFailAlloc_4619_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_4617_ = lean_array_uset(v_x_4593_, v___x_4613_, v___x_4616_);
                v_x_4593_ = v___x_4617_;
                v_x_4594_ = v_tail_4597_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_elabRewrite_spec__2_spec__2_spec__5_spec__8_spec__11___redArg(
    mut v_i_4621_: *mut LeanObject,
    mut v_source_4622_: *mut LeanObject,
    mut v_target_4623_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4624_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4625_: u8 = 0;
    let mut v_es_4626_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4627_: *mut LeanObject = core::ptr::null_mut();
    let mut v_source_4628_: *mut LeanObject = core::ptr::null_mut();
    let mut v_target_4629_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4630_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4631_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4624_ = lean_array_get_size(v_source_4622_);
                v___x_4625_ = lean_nat_dec_lt(v_i_4621_, v___x_4624_);
                if v___x_4625_ == 0 {
                    lean_dec_ref(v_source_4622_);
                    lean_dec(v_i_4621_);
                    return v_target_4623_;
                } else {
                    v_es_4626_ = lean_array_fget(v_source_4622_, v_i_4621_);
                    v___x_4627_ = lean_box(0);
                    v_source_4628_ = lean_array_fset(v_source_4622_, v_i_4621_, v___x_4627_);
                    v_target_4629_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_elabRewrite_spec__2_spec__2_spec__5_spec__8_spec__11_spec__15___redArg(v_target_4623_, v_es_4626_);
                    v___x_4630_ = lean_unsigned_to_nat(1);
                    v___x_4631_ = lean_nat_add(v_i_4621_, v___x_4630_);
                    lean_dec(v_i_4621_);
                    v_i_4621_ = v___x_4631_;
                    v_source_4622_ = v_source_4628_;
                    v_target_4623_ = v_target_4629_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_elabRewrite_spec__2_spec__2_spec__5_spec__8___redArg(
    mut v_data_4633_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4634_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4635_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nbuckets_4636_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4637_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4638_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4639_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4640_: *mut LeanObject = core::ptr::null_mut();
    v___x_4634_ = lean_array_get_size(v_data_4633_);
    v___x_4635_ = lean_unsigned_to_nat(2);
    v_nbuckets_4636_ = lean_nat_mul(v___x_4634_, v___x_4635_);
    v___x_4637_ = lean_unsigned_to_nat(0);
    v___x_4638_ = lean_box(0);
    v___x_4639_ = lean_mk_array(v_nbuckets_4636_, v___x_4638_);
    v___x_4640_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_elabRewrite_spec__2_spec__2_spec__5_spec__8_spec__11___redArg(v___x_4637_, v_data_4633_, v___x_4639_);
    return v___x_4640_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_elabRewrite_spec__2_spec__2_spec__5___redArg(
    mut v_m_4641_: *mut LeanObject,
    mut v_a_4642_: *mut LeanObject,
    mut v_b_4643_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_size_4644_: *mut LeanObject = core::ptr::null_mut();
    let mut v_buckets_4645_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4646_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4647_: u64 = 0;
    let mut v___x_4648_: u64 = 0;
    let mut v___x_4649_: u64 = 0;
    let mut v_fold_4650_: u64 = 0;
    let mut v___x_4651_: u64 = 0;
    let mut v___x_4652_: u64 = 0;
    let mut v___x_4653_: u64 = 0;
    let mut v___x_4654_: usize = 0;
    let mut v___x_4655_: usize = 0;
    let mut v___x_4656_: usize = 0;
    let mut v___x_4657_: usize = 0;
    let mut v___x_4658_: usize = 0;
    let mut v_bkt_4659_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4660_: u8 = 0;
    let mut v___x_4662_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4663_: u8 = 0;
    let mut v___x_4664_: *mut LeanObject = core::ptr::null_mut();
    let mut v_size_x27_4665_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4666_: *mut LeanObject = core::ptr::null_mut();
    let mut v_buckets_x27_4667_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4668_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4669_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4670_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4671_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4672_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4673_: u8 = 0;
    let mut v_val_4674_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4676_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4677_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4679_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4680_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4681_: u8 = 0;
    let mut v_unused_4682_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_4683_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_size_4644_ = lean_ctor_get(v_m_4641_, 0);
                v_buckets_4645_ = lean_ctor_get(v_m_4641_, 1);
                v___x_4646_ = lean_array_get_size(v_buckets_4645_);
                v___x_4647_ = l_Lean_Expr_hash(v_a_4642_);
                v___x_4648_ = 32u64;
                v___x_4649_ = lean_uint64_shift_right(v___x_4647_, v___x_4648_);
                v_fold_4650_ = lean_uint64_xor(v___x_4647_, v___x_4649_);
                v___x_4651_ = 16u64;
                v___x_4652_ = lean_uint64_shift_right(v_fold_4650_, v___x_4651_);
                v___x_4653_ = lean_uint64_xor(v_fold_4650_, v___x_4652_);
                v___x_4654_ = lean_uint64_to_usize(v___x_4653_);
                v___x_4655_ = lean_usize_of_nat(v___x_4646_);
                v___x_4656_ = 1usize;
                v___x_4657_ = lean_usize_sub(v___x_4655_, v___x_4656_);
                v___x_4658_ = lean_usize_land(v___x_4654_, v___x_4657_);
                v_bkt_4659_ = lean_array_uget_borrowed(v_buckets_4645_, v___x_4658_);
                v___x_4660_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_elabRewrite_spec__2_spec__2_spec__4_spec__6___redArg(v_a_4642_, v_bkt_4659_);
                if v___x_4660_ == 0 {
                    lean_inc_ref(v_buckets_4645_);
                    lean_inc(v_size_4644_);
                    v_isSharedCheck_4681_ = (!lean_is_exclusive(v_m_4641_)) as u8;
                    if v_isSharedCheck_4681_ == 0 {
                        v_unused_4682_ = lean_ctor_get(v_m_4641_, 1);
                        lean_dec(v_unused_4682_);
                        v_unused_4683_ = lean_ctor_get(v_m_4641_, 0);
                        lean_dec(v_unused_4683_);
                        v___x_4662_ = v_m_4641_;
                        v_isShared_4663_ = v_isSharedCheck_4681_;
                        state = 1;
                        continue;
                    } else {
                        lean_dec(v_m_4641_);
                        v___x_4662_ = lean_box(0);
                        v_isShared_4663_ = v_isSharedCheck_4681_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec(v_b_4643_);
                    lean_dec_ref(v_a_4642_);
                    return v_m_4641_;
                }
            }
            1 => {
                v___x_4664_ = lean_unsigned_to_nat(1);
                v_size_x27_4665_ = lean_nat_add(v_size_4644_, v___x_4664_);
                lean_dec(v_size_4644_);
                lean_inc(v_bkt_4659_);
                v___x_4666_ = lean_alloc_ctor(1, 3, (0) as u32);
                lean_ctor_set(v___x_4666_, 0, v_a_4642_);
                lean_ctor_set(v___x_4666_, 1, v_b_4643_);
                lean_ctor_set(v___x_4666_, 2, v_bkt_4659_);
                v_buckets_x27_4667_ = lean_array_uset(v_buckets_4645_, v___x_4658_, v___x_4666_);
                v___x_4668_ = lean_unsigned_to_nat(4);
                v___x_4669_ = lean_nat_mul(v_size_x27_4665_, v___x_4668_);
                v___x_4670_ = lean_unsigned_to_nat(3);
                v___x_4671_ = lean_nat_div(v___x_4669_, v___x_4670_);
                lean_dec(v___x_4669_);
                v___x_4672_ = lean_array_get_size(v_buckets_x27_4667_);
                v___x_4673_ = lean_nat_dec_le(v___x_4671_, v___x_4672_);
                lean_dec(v___x_4671_);
                if v___x_4673_ == 0 {
                    v_val_4674_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_elabRewrite_spec__2_spec__2_spec__5_spec__8___redArg(v_buckets_x27_4667_);
                    if v_isShared_4663_ == 0 {
                        lean_ctor_set(v___x_4662_, 1, v_val_4674_);
                        lean_ctor_set(v___x_4662_, 0, v_size_x27_4665_);
                        v___x_4676_ = v___x_4662_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_4677_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_4677_, 0, v_size_x27_4665_);
                        lean_ctor_set(v_reuseFailAlloc_4677_, 1, v_val_4674_);
                        v___x_4676_ = v_reuseFailAlloc_4677_;
                        state = 2;
                        continue;
                    }
                } else {
                    if v_isShared_4663_ == 0 {
                        lean_ctor_set(v___x_4662_, 1, v_buckets_x27_4667_);
                        lean_ctor_set(v___x_4662_, 0, v_size_x27_4665_);
                        v___x_4679_ = v___x_4662_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_4680_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_4680_, 0, v_size_x27_4665_);
                        lean_ctor_set(v_reuseFailAlloc_4680_, 1, v_buckets_x27_4667_);
                        v___x_4679_ = v_reuseFailAlloc_4680_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_4676_;
            }
            3 => {
                return v___x_4679_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_elabRewrite_spec__2_spec__2(
    mut v_mvarId_4688_: *mut LeanObject,
    mut v_e_4689_: *mut LeanObject,
    mut v_a_4690_: *mut LeanObject,
    mut v___y_4691_: *mut LeanObject,
    mut v___y_4692_: *mut LeanObject,
    mut v___y_4693_: *mut LeanObject,
    mut v___y_4694_: *mut LeanObject,
    mut v___y_4695_: *mut LeanObject,
    mut v___y_4696_: *mut LeanObject,
    mut v___y_4697_: *mut LeanObject,
    mut v___y_4698_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_d_4701_: *mut LeanObject = core::ptr::null_mut();
    let mut v_b_4702_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4703_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4704_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4705_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_4706_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_4707_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4709_: u8 = 0;
    let mut v___x_4710_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4711_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4712_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4713_: u8 = 0;
    let mut v___x_4714_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4715_: *mut LeanObject = core::ptr::null_mut();
    let mut v_struct_4716_: *mut LeanObject = core::ptr::null_mut();
    let mut v_binderType_4718_: *mut LeanObject = core::ptr::null_mut();
    let mut v_body_4719_: *mut LeanObject = core::ptr::null_mut();
    let mut v_binderType_4720_: *mut LeanObject = core::ptr::null_mut();
    let mut v_body_4721_: *mut LeanObject = core::ptr::null_mut();
    let mut v_type_4722_: *mut LeanObject = core::ptr::null_mut();
    let mut v_value_4723_: *mut LeanObject = core::ptr::null_mut();
    let mut v_body_4724_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4725_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4726_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_4727_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_4728_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4729_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4730_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_4731_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_4732_: *mut LeanObject = core::ptr::null_mut();
    let mut v_expr_4734_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fn_4736_: *mut LeanObject = core::ptr::null_mut();
    let mut v_arg_4737_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4738_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4739_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_4740_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_4741_: *mut LeanObject = core::ptr::null_mut();
    let mut v_mvarId_4743_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4744_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4745_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4746_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4747_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4748_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4749_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4750_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4709_ = l_Lean_Expr_hasExprMVar(v_e_4689_);
                if v___x_4709_ == 0 {
                    lean_dec_ref(v_e_4689_);
                    v___x_4710_ = l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_elabRewrite_spec__2_spec__2_spec__6___closed__0;
                    v___x_4711_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v___x_4711_, 0, v___x_4710_);
                    lean_ctor_set(v___x_4711_, 1, v_a_4690_);
                    v___x_4712_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_4712_, 0, v___x_4711_);
                    return v___x_4712_;
                } else {
                    v___x_4713_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_elabRewrite_spec__2_spec__2_spec__4___redArg(v_a_4690_, v_e_4689_);
                    if v___x_4713_ == 0 {
                        v___x_4714_ = lean_box(0);
                        lean_inc_ref(v_e_4689_);
                        v___x_4715_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_elabRewrite_spec__2_spec__2_spec__5___redArg(v_a_4690_, v_e_4689_, v___x_4714_);
                        match lean_obj_tag(v_e_4689_) {
                            11 => {
                                v_struct_4716_ = lean_ctor_get(v_e_4689_, 2);
                                lean_inc_ref(v_struct_4716_);
                                lean_dec_ref_known(v_e_4689_, 3);
                                v_e_4689_ = v_struct_4716_;
                                v_a_4690_ = v___x_4715_;
                                state = 0;
                                continue;
                            }
                            7 => {
                                v_binderType_4718_ = lean_ctor_get(v_e_4689_, 1);
                                lean_inc_ref(v_binderType_4718_);
                                v_body_4719_ = lean_ctor_get(v_e_4689_, 2);
                                lean_inc_ref(v_body_4719_);
                                lean_dec_ref_known(v_e_4689_, 3);
                                v_d_4701_ = v_binderType_4718_;
                                v_b_4702_ = v_body_4719_;
                                v___y_4703_ = v___x_4715_;
                                state = 1;
                                continue;
                            }
                            6 => {
                                v_binderType_4720_ = lean_ctor_get(v_e_4689_, 1);
                                lean_inc_ref(v_binderType_4720_);
                                v_body_4721_ = lean_ctor_get(v_e_4689_, 2);
                                lean_inc_ref(v_body_4721_);
                                lean_dec_ref_known(v_e_4689_, 3);
                                v_d_4701_ = v_binderType_4720_;
                                v_b_4702_ = v_body_4721_;
                                v___y_4703_ = v___x_4715_;
                                state = 1;
                                continue;
                            }
                            8 => {
                                v_type_4722_ = lean_ctor_get(v_e_4689_, 1);
                                lean_inc_ref(v_type_4722_);
                                v_value_4723_ = lean_ctor_get(v_e_4689_, 2);
                                lean_inc_ref(v_value_4723_);
                                v_body_4724_ = lean_ctor_get(v_e_4689_, 3);
                                lean_inc_ref(v_body_4724_);
                                lean_dec_ref_known(v_e_4689_, 4);
                                v___x_4725_ = l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_elabRewrite_spec__2_spec__2(v_mvarId_4688_, v_type_4722_, v___x_4715_, v___y_4691_, v___y_4692_, v___y_4693_, v___y_4694_, v___y_4695_, v___y_4696_, v___y_4697_, v___y_4698_);
                                if lean_obj_tag(v___x_4725_) == 0 {
                                    v_a_4726_ = lean_ctor_get(v___x_4725_, 0);
                                    lean_inc(v_a_4726_);
                                    v_fst_4727_ = lean_ctor_get(v_a_4726_, 0);
                                    if lean_obj_tag(v_fst_4727_) == 0 {
                                        lean_dec(v_a_4726_);
                                        lean_dec_ref(v_body_4724_);
                                        lean_dec_ref(v_value_4723_);
                                        return v___x_4725_;
                                    } else {
                                        lean_dec_ref_known(v___x_4725_, 1);
                                        v_snd_4728_ = lean_ctor_get(v_a_4726_, 1);
                                        lean_inc(v_snd_4728_);
                                        lean_dec(v_a_4726_);
                                        v___x_4729_ = l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_elabRewrite_spec__2_spec__2(v_mvarId_4688_, v_value_4723_, v_snd_4728_, v___y_4691_, v___y_4692_, v___y_4693_, v___y_4694_, v___y_4695_, v___y_4696_, v___y_4697_, v___y_4698_);
                                        if lean_obj_tag(v___x_4729_) == 0 {
                                            v_a_4730_ = lean_ctor_get(v___x_4729_, 0);
                                            lean_inc(v_a_4730_);
                                            v_fst_4731_ = lean_ctor_get(v_a_4730_, 0);
                                            if lean_obj_tag(v_fst_4731_) == 0 {
                                                lean_dec(v_a_4730_);
                                                lean_dec_ref(v_body_4724_);
                                                return v___x_4729_;
                                            } else {
                                                lean_dec_ref_known(v___x_4729_, 1);
                                                v_snd_4732_ = lean_ctor_get(v_a_4730_, 1);
                                                lean_inc(v_snd_4732_);
                                                lean_dec(v_a_4730_);
                                                v_e_4689_ = v_body_4724_;
                                                v_a_4690_ = v_snd_4732_;
                                                state = 0;
                                                continue;
                                            }
                                        } else {
                                            lean_dec_ref(v_body_4724_);
                                            return v___x_4729_;
                                        }
                                    }
                                } else {
                                    lean_dec_ref(v_body_4724_);
                                    lean_dec_ref(v_value_4723_);
                                    return v___x_4725_;
                                }
                            }
                            10 => {
                                v_expr_4734_ = lean_ctor_get(v_e_4689_, 1);
                                lean_inc_ref(v_expr_4734_);
                                lean_dec_ref_known(v_e_4689_, 2);
                                v_e_4689_ = v_expr_4734_;
                                v_a_4690_ = v___x_4715_;
                                state = 0;
                                continue;
                            }
                            5 => {
                                v_fn_4736_ = lean_ctor_get(v_e_4689_, 0);
                                lean_inc_ref(v_fn_4736_);
                                v_arg_4737_ = lean_ctor_get(v_e_4689_, 1);
                                lean_inc_ref(v_arg_4737_);
                                lean_dec_ref_known(v_e_4689_, 2);
                                v___x_4738_ = l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_elabRewrite_spec__2_spec__2(v_mvarId_4688_, v_fn_4736_, v___x_4715_, v___y_4691_, v___y_4692_, v___y_4693_, v___y_4694_, v___y_4695_, v___y_4696_, v___y_4697_, v___y_4698_);
                                if lean_obj_tag(v___x_4738_) == 0 {
                                    v_a_4739_ = lean_ctor_get(v___x_4738_, 0);
                                    lean_inc(v_a_4739_);
                                    v_fst_4740_ = lean_ctor_get(v_a_4739_, 0);
                                    if lean_obj_tag(v_fst_4740_) == 0 {
                                        lean_dec(v_a_4739_);
                                        lean_dec_ref(v_arg_4737_);
                                        return v___x_4738_;
                                    } else {
                                        lean_dec_ref_known(v___x_4738_, 1);
                                        v_snd_4741_ = lean_ctor_get(v_a_4739_, 1);
                                        lean_inc(v_snd_4741_);
                                        lean_dec(v_a_4739_);
                                        v_e_4689_ = v_arg_4737_;
                                        v_a_4690_ = v_snd_4741_;
                                        state = 0;
                                        continue;
                                    }
                                } else {
                                    lean_dec_ref(v_arg_4737_);
                                    return v___x_4738_;
                                }
                            }
                            2 => {
                                v_mvarId_4743_ = lean_ctor_get(v_e_4689_, 0);
                                lean_inc(v_mvarId_4743_);
                                lean_dec_ref_known(v_e_4689_, 1);
                                v___x_4744_ = l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_elabRewrite_spec__2_spec__2_spec__6(v_mvarId_4688_, v_mvarId_4743_, v___x_4715_, v___y_4691_, v___y_4692_, v___y_4693_, v___y_4694_, v___y_4695_, v___y_4696_, v___y_4697_, v___y_4698_);
                                return v___x_4744_;
                            }
                            _ => {
                                lean_dec_ref(v_e_4689_);
                                v___x_4745_ = l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_elabRewrite_spec__2_spec__2_spec__6___closed__0;
                                v___x_4746_ = lean_alloc_ctor(0, 2, (0) as u32);
                                lean_ctor_set(v___x_4746_, 0, v___x_4745_);
                                lean_ctor_set(v___x_4746_, 1, v___x_4715_);
                                v___x_4747_ = lean_alloc_ctor(0, 1, (0) as u32);
                                lean_ctor_set(v___x_4747_, 0, v___x_4746_);
                                return v___x_4747_;
                            }
                        }
                    } else {
                        lean_dec_ref(v_e_4689_);
                        v___x_4748_ = l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_elabRewrite_spec__2_spec__2_spec__6___closed__0;
                        v___x_4749_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v___x_4749_, 0, v___x_4748_);
                        lean_ctor_set(v___x_4749_, 1, v_a_4690_);
                        v___x_4750_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v___x_4750_, 0, v___x_4749_);
                        return v___x_4750_;
                    }
                }
            }
            1 => {
                v___x_4704_ = l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_elabRewrite_spec__2_spec__2(v_mvarId_4688_, v_d_4701_, v___y_4703_, v___y_4691_, v___y_4692_, v___y_4693_, v___y_4694_, v___y_4695_, v___y_4696_, v___y_4697_, v___y_4698_);
                if lean_obj_tag(v___x_4704_) == 0 {
                    v_a_4705_ = lean_ctor_get(v___x_4704_, 0);
                    lean_inc(v_a_4705_);
                    v_fst_4706_ = lean_ctor_get(v_a_4705_, 0);
                    if lean_obj_tag(v_fst_4706_) == 0 {
                        lean_dec(v_a_4705_);
                        lean_dec_ref(v_b_4702_);
                        return v___x_4704_;
                    } else {
                        lean_dec_ref_known(v___x_4704_, 1);
                        v_snd_4707_ = lean_ctor_get(v_a_4705_, 1);
                        lean_inc(v_snd_4707_);
                        lean_dec(v_a_4705_);
                        v_e_4689_ = v_b_4702_;
                        v_a_4690_ = v_snd_4707_;
                        state = 0;
                        continue;
                    }
                } else {
                    lean_dec_ref(v_b_4702_);
                    return v___x_4704_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_elabRewrite_spec__2_spec__2_spec__6(
    mut v_mvarId_4751_: *mut LeanObject,
    mut v_mvarId_x27_4752_: *mut LeanObject,
    mut v_a_4753_: *mut LeanObject,
    mut v___y_4754_: *mut LeanObject,
    mut v___y_4755_: *mut LeanObject,
    mut v___y_4756_: *mut LeanObject,
    mut v___y_4757_: *mut LeanObject,
    mut v___y_4758_: *mut LeanObject,
    mut v___y_4759_: *mut LeanObject,
    mut v___y_4760_: *mut LeanObject,
    mut v___y_4761_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4763_: u8 = 0;
    let mut v___x_4764_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4765_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4767_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4768_: u8 = 0;
    let mut v_fst_4769_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_4770_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4772_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4773_: u8 = 0;
    let mut v_a_4774_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4776_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4777_: u8 = 0;
    let mut v___x_4779_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4781_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4783_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4784_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4785_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4786_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4787_: u8 = 0;
    let mut v_isSharedCheck_4788_: u8 = 0;
    let mut v_unused_4789_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4790_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_4791_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4792_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4793_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4795_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4796_: u8 = 0;
    let mut v_fst_4797_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_4798_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4800_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4801_: u8 = 0;
    let mut v_a_4802_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4804_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4805_: u8 = 0;
    let mut v___x_4807_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4809_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4811_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4812_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4813_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4814_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4815_: u8 = 0;
    let mut v_isSharedCheck_4816_: u8 = 0;
    let mut v_unused_4817_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4818_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_4819_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4821_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4822_: u8 = 0;
    let mut v___x_4823_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4825_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4827_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4828_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4829_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4830_: u8 = 0;
    let mut v_unused_4831_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_4832_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_4833_: *mut LeanObject = core::ptr::null_mut();
    let mut v_mvarIdPending_4834_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4836_: u8 = 0;
    let mut v_a_4837_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4839_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4840_: u8 = 0;
    let mut v___x_4842_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4843_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4844_: u8 = 0;
    let mut v_snd_4845_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_4846_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4847_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4848_: u8 = 0;
    let mut v_a_4849_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4851_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4852_: u8 = 0;
    let mut v___x_4854_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4855_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4856_: u8 = 0;
    let mut v___x_4857_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4858_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4859_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4763_ = l_Lean_instBEqMVarId_beq(v_mvarId_4751_, v_mvarId_x27_4752_);
                if v___x_4763_ == 0 {
                    v___x_4764_ = l_Lean_getExprMVarAssignment_x3f___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_elabRewrite_spec__2_spec__2_spec__6_spec__10___redArg(v_mvarId_x27_4752_, v_a_4753_, v___y_4759_);
                    if lean_obj_tag(v___x_4764_) == 0 {
                        v_a_4765_ = lean_ctor_get(v___x_4764_, 0);
                        v_isSharedCheck_4848_ = (!lean_is_exclusive(v___x_4764_)) as u8;
                        if v_isSharedCheck_4848_ == 0 {
                            v___x_4767_ = v___x_4764_;
                            v_isShared_4768_ = v_isSharedCheck_4848_;
                            state = 1;
                            continue;
                        } else {
                            lean_inc(v_a_4765_);
                            lean_dec(v___x_4764_);
                            v___x_4767_ = lean_box(0);
                            v_isShared_4768_ = v_isSharedCheck_4848_;
                            state = 1;
                            continue;
                        }
                    } else {
                        lean_dec(v_mvarId_x27_4752_);
                        v_a_4849_ = lean_ctor_get(v___x_4764_, 0);
                        v_isSharedCheck_4856_ = (!lean_is_exclusive(v___x_4764_)) as u8;
                        if v_isSharedCheck_4856_ == 0 {
                            v___x_4851_ = v___x_4764_;
                            v_isShared_4852_ = v_isSharedCheck_4856_;
                            state = 18;
                            continue;
                        } else {
                            lean_inc(v_a_4849_);
                            lean_dec(v___x_4764_);
                            v___x_4851_ = lean_box(0);
                            v_isShared_4852_ = v_isSharedCheck_4856_;
                            state = 18;
                            continue;
                        }
                    }
                } else {
                    lean_dec(v_mvarId_x27_4752_);
                    v___x_4857_ = l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_elabRewrite_spec__2_spec__2_spec__6___closed__1;
                    v___x_4858_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v___x_4858_, 0, v___x_4857_);
                    lean_ctor_set(v___x_4858_, 1, v_a_4753_);
                    v___x_4859_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_4859_, 0, v___x_4858_);
                    return v___x_4859_;
                }
            }
            1 => {
                v_fst_4769_ = lean_ctor_get(v_a_4765_, 0);
                lean_inc(v_fst_4769_);
                if lean_obj_tag(v_fst_4769_) == 0 {
                    lean_dec(v_mvarId_x27_4752_);
                    v_snd_4770_ = lean_ctor_get(v_a_4765_, 1);
                    v_isSharedCheck_4788_ = (!lean_is_exclusive(v_a_4765_)) as u8;
                    if v_isSharedCheck_4788_ == 0 {
                        v_unused_4789_ = lean_ctor_get(v_a_4765_, 0);
                        lean_dec(v_unused_4789_);
                        v___x_4772_ = v_a_4765_;
                        v_isShared_4773_ = v_isSharedCheck_4788_;
                        state = 2;
                        continue;
                    } else {
                        lean_inc(v_snd_4770_);
                        lean_dec(v_a_4765_);
                        v___x_4772_ = lean_box(0);
                        v_isShared_4773_ = v_isSharedCheck_4788_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_4767_);
                    v_a_4790_ = lean_ctor_get(v_fst_4769_, 0);
                    lean_inc(v_a_4790_);
                    lean_dec_ref_known(v_fst_4769_, 1);
                    if lean_obj_tag(v_a_4790_) == 0 {
                        v_snd_4791_ = lean_ctor_get(v_a_4765_, 1);
                        lean_inc(v_snd_4791_);
                        lean_dec(v_a_4765_);
                        v___x_4792_ = l_Lean_getDelayedMVarAssignment_x3f___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_elabRewrite_spec__2_spec__2_spec__6_spec__11___redArg(v_mvarId_x27_4752_, v_snd_4791_, v___y_4759_);
                        lean_dec(v_mvarId_x27_4752_);
                        if lean_obj_tag(v___x_4792_) == 0 {
                            v_a_4793_ = lean_ctor_get(v___x_4792_, 0);
                            v_isSharedCheck_4836_ = (!lean_is_exclusive(v___x_4792_)) as u8;
                            if v_isSharedCheck_4836_ == 0 {
                                v___x_4795_ = v___x_4792_;
                                v_isShared_4796_ = v_isSharedCheck_4836_;
                                state = 7;
                                continue;
                            } else {
                                lean_inc(v_a_4793_);
                                lean_dec(v___x_4792_);
                                v___x_4795_ = lean_box(0);
                                v_isShared_4796_ = v_isSharedCheck_4836_;
                                state = 7;
                                continue;
                            }
                        } else {
                            v_a_4837_ = lean_ctor_get(v___x_4792_, 0);
                            v_isSharedCheck_4844_ = (!lean_is_exclusive(v___x_4792_)) as u8;
                            if v_isSharedCheck_4844_ == 0 {
                                v___x_4839_ = v___x_4792_;
                                v_isShared_4840_ = v_isSharedCheck_4844_;
                                state = 16;
                                continue;
                            } else {
                                lean_inc(v_a_4837_);
                                lean_dec(v___x_4792_);
                                v___x_4839_ = lean_box(0);
                                v_isShared_4840_ = v_isSharedCheck_4844_;
                                state = 16;
                                continue;
                            }
                        }
                    } else {
                        lean_dec(v_mvarId_x27_4752_);
                        v_snd_4845_ = lean_ctor_get(v_a_4765_, 1);
                        lean_inc(v_snd_4845_);
                        lean_dec(v_a_4765_);
                        v_val_4846_ = lean_ctor_get(v_a_4790_, 0);
                        lean_inc(v_val_4846_);
                        lean_dec_ref_known(v_a_4790_, 1);
                        v___x_4847_ = l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_elabRewrite_spec__2_spec__2(v_mvarId_4751_, v_val_4846_, v_snd_4845_, v___y_4754_, v___y_4755_, v___y_4756_, v___y_4757_, v___y_4758_, v___y_4759_, v___y_4760_, v___y_4761_);
                        return v___x_4847_;
                    }
                }
            }
            2 => {
                v_a_4774_ = lean_ctor_get(v_fst_4769_, 0);
                v_isSharedCheck_4787_ = (!lean_is_exclusive(v_fst_4769_)) as u8;
                if v_isSharedCheck_4787_ == 0 {
                    v___x_4776_ = v_fst_4769_;
                    v_isShared_4777_ = v_isSharedCheck_4787_;
                    state = 3;
                    continue;
                } else {
                    lean_inc(v_a_4774_);
                    lean_dec(v_fst_4769_);
                    v___x_4776_ = lean_box(0);
                    v_isShared_4777_ = v_isSharedCheck_4787_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_4777_ == 0 {
                    v___x_4779_ = v___x_4776_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4786_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4786_, 0, v_a_4774_);
                    v___x_4779_ = v_reuseFailAlloc_4786_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                if v_isShared_4773_ == 0 {
                    lean_ctor_set(v___x_4772_, 0, v___x_4779_);
                    v___x_4781_ = v___x_4772_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_4785_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4785_, 0, v___x_4779_);
                    lean_ctor_set(v_reuseFailAlloc_4785_, 1, v_snd_4770_);
                    v___x_4781_ = v_reuseFailAlloc_4785_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                if v_isShared_4768_ == 0 {
                    lean_ctor_set(v___x_4767_, 0, v___x_4781_);
                    v___x_4783_ = v___x_4767_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_4784_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4784_, 0, v___x_4781_);
                    v___x_4783_ = v_reuseFailAlloc_4784_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_4783_;
            }
            7 => {
                v_fst_4797_ = lean_ctor_get(v_a_4793_, 0);
                lean_inc(v_fst_4797_);
                if lean_obj_tag(v_fst_4797_) == 0 {
                    v_snd_4798_ = lean_ctor_get(v_a_4793_, 1);
                    v_isSharedCheck_4816_ = (!lean_is_exclusive(v_a_4793_)) as u8;
                    if v_isSharedCheck_4816_ == 0 {
                        v_unused_4817_ = lean_ctor_get(v_a_4793_, 0);
                        lean_dec(v_unused_4817_);
                        v___x_4800_ = v_a_4793_;
                        v_isShared_4801_ = v_isSharedCheck_4816_;
                        state = 8;
                        continue;
                    } else {
                        lean_inc(v_snd_4798_);
                        lean_dec(v_a_4793_);
                        v___x_4800_ = lean_box(0);
                        v_isShared_4801_ = v_isSharedCheck_4816_;
                        state = 8;
                        continue;
                    }
                } else {
                    v_a_4818_ = lean_ctor_get(v_fst_4797_, 0);
                    lean_inc(v_a_4818_);
                    lean_dec_ref_known(v_fst_4797_, 1);
                    if lean_obj_tag(v_a_4818_) == 0 {
                        v_snd_4819_ = lean_ctor_get(v_a_4793_, 1);
                        v_isSharedCheck_4830_ = (!lean_is_exclusive(v_a_4793_)) as u8;
                        if v_isSharedCheck_4830_ == 0 {
                            v_unused_4831_ = lean_ctor_get(v_a_4793_, 0);
                            lean_dec(v_unused_4831_);
                            v___x_4821_ = v_a_4793_;
                            v_isShared_4822_ = v_isSharedCheck_4830_;
                            state = 13;
                            continue;
                        } else {
                            lean_inc(v_snd_4819_);
                            lean_dec(v_a_4793_);
                            v___x_4821_ = lean_box(0);
                            v_isShared_4822_ = v_isSharedCheck_4830_;
                            state = 13;
                            continue;
                        }
                    } else {
                        lean_del_object(v___x_4795_);
                        v_val_4832_ = lean_ctor_get(v_a_4818_, 0);
                        lean_inc(v_val_4832_);
                        lean_dec_ref_known(v_a_4818_, 1);
                        v_snd_4833_ = lean_ctor_get(v_a_4793_, 1);
                        lean_inc(v_snd_4833_);
                        lean_dec(v_a_4793_);
                        v_mvarIdPending_4834_ = lean_ctor_get(v_val_4832_, 1);
                        lean_inc(v_mvarIdPending_4834_);
                        lean_dec(v_val_4832_);
                        v_mvarId_x27_4752_ = v_mvarIdPending_4834_;
                        v_a_4753_ = v_snd_4833_;
                        state = 0;
                        continue;
                    }
                }
            }
            8 => {
                v_a_4802_ = lean_ctor_get(v_fst_4797_, 0);
                v_isSharedCheck_4815_ = (!lean_is_exclusive(v_fst_4797_)) as u8;
                if v_isSharedCheck_4815_ == 0 {
                    v___x_4804_ = v_fst_4797_;
                    v_isShared_4805_ = v_isSharedCheck_4815_;
                    state = 9;
                    continue;
                } else {
                    lean_inc(v_a_4802_);
                    lean_dec(v_fst_4797_);
                    v___x_4804_ = lean_box(0);
                    v_isShared_4805_ = v_isSharedCheck_4815_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                if v_isShared_4805_ == 0 {
                    v___x_4807_ = v___x_4804_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_4814_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4814_, 0, v_a_4802_);
                    v___x_4807_ = v_reuseFailAlloc_4814_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                if v_isShared_4801_ == 0 {
                    lean_ctor_set(v___x_4800_, 0, v___x_4807_);
                    v___x_4809_ = v___x_4800_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_4813_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4813_, 0, v___x_4807_);
                    lean_ctor_set(v_reuseFailAlloc_4813_, 1, v_snd_4798_);
                    v___x_4809_ = v_reuseFailAlloc_4813_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                if v_isShared_4796_ == 0 {
                    lean_ctor_set(v___x_4795_, 0, v___x_4809_);
                    v___x_4811_ = v___x_4795_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_4812_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4812_, 0, v___x_4809_);
                    v___x_4811_ = v_reuseFailAlloc_4812_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                return v___x_4811_;
            }
            13 => {
                v___x_4823_ = l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_elabRewrite_spec__2_spec__2_spec__6___closed__0;
                if v_isShared_4822_ == 0 {
                    lean_ctor_set(v___x_4821_, 0, v___x_4823_);
                    v___x_4825_ = v___x_4821_;
                    state = 14;
                    continue;
                } else {
                    v_reuseFailAlloc_4829_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4829_, 0, v___x_4823_);
                    lean_ctor_set(v_reuseFailAlloc_4829_, 1, v_snd_4819_);
                    v___x_4825_ = v_reuseFailAlloc_4829_;
                    state = 14;
                    continue;
                }
            }
            14 => {
                if v_isShared_4796_ == 0 {
                    lean_ctor_set(v___x_4795_, 0, v___x_4825_);
                    v___x_4827_ = v___x_4795_;
                    state = 15;
                    continue;
                } else {
                    v_reuseFailAlloc_4828_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4828_, 0, v___x_4825_);
                    v___x_4827_ = v_reuseFailAlloc_4828_;
                    state = 15;
                    continue;
                }
            }
            15 => {
                return v___x_4827_;
            }
            16 => {
                if v_isShared_4840_ == 0 {
                    v___x_4842_ = v___x_4839_;
                    state = 17;
                    continue;
                } else {
                    v_reuseFailAlloc_4843_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4843_, 0, v_a_4837_);
                    v___x_4842_ = v_reuseFailAlloc_4843_;
                    state = 17;
                    continue;
                }
            }
            17 => {
                return v___x_4842_;
            }
            18 => {
                if v_isShared_4852_ == 0 {
                    v___x_4854_ = v___x_4851_;
                    state = 19;
                    continue;
                } else {
                    v_reuseFailAlloc_4855_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4855_, 0, v_a_4849_);
                    v___x_4854_ = v_reuseFailAlloc_4855_;
                    state = 19;
                    continue;
                }
            }
            19 => {
                return v___x_4854_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_elabRewrite_spec__2_spec__2_spec__6___boxed(
    mut v_mvarId_4860_: *mut LeanObject,
    mut v_mvarId_x27_4861_: *mut LeanObject,
    mut v_a_4862_: *mut LeanObject,
    mut v___y_4863_: *mut LeanObject,
    mut v___y_4864_: *mut LeanObject,
    mut v___y_4865_: *mut LeanObject,
    mut v___y_4866_: *mut LeanObject,
    mut v___y_4867_: *mut LeanObject,
    mut v___y_4868_: *mut LeanObject,
    mut v___y_4869_: *mut LeanObject,
    mut v___y_4870_: *mut LeanObject,
    mut v___y_4871_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4872_: *mut LeanObject = core::ptr::null_mut();
    v_res_4872_ = l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_elabRewrite_spec__2_spec__2_spec__6(v_mvarId_4860_, v_mvarId_x27_4861_, v_a_4862_, v___y_4863_, v___y_4864_, v___y_4865_, v___y_4866_, v___y_4867_, v___y_4868_, v___y_4869_, v___y_4870_);
    lean_dec(v___y_4870_);
    lean_dec_ref(v___y_4869_);
    lean_dec(v___y_4868_);
    lean_dec_ref(v___y_4867_);
    lean_dec(v___y_4866_);
    lean_dec_ref(v___y_4865_);
    lean_dec(v___y_4864_);
    lean_dec_ref(v___y_4863_);
    lean_dec(v_mvarId_4860_);
    return v_res_4872_;
}
pub unsafe fn l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_elabRewrite_spec__2_spec__2___boxed(
    mut v_mvarId_4873_: *mut LeanObject,
    mut v_e_4874_: *mut LeanObject,
    mut v_a_4875_: *mut LeanObject,
    mut v___y_4876_: *mut LeanObject,
    mut v___y_4877_: *mut LeanObject,
    mut v___y_4878_: *mut LeanObject,
    mut v___y_4879_: *mut LeanObject,
    mut v___y_4880_: *mut LeanObject,
    mut v___y_4881_: *mut LeanObject,
    mut v___y_4882_: *mut LeanObject,
    mut v___y_4883_: *mut LeanObject,
    mut v___y_4884_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4885_: *mut LeanObject = core::ptr::null_mut();
    v_res_4885_ = l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_elabRewrite_spec__2_spec__2(v_mvarId_4873_, v_e_4874_, v_a_4875_, v___y_4876_, v___y_4877_, v___y_4878_, v___y_4879_, v___y_4880_, v___y_4881_, v___y_4882_, v___y_4883_);
    lean_dec(v___y_4883_);
    lean_dec_ref(v___y_4882_);
    lean_dec(v___y_4881_);
    lean_dec_ref(v___y_4880_);
    lean_dec(v___y_4879_);
    lean_dec_ref(v___y_4878_);
    lean_dec(v___y_4877_);
    lean_dec_ref(v___y_4876_);
    lean_dec(v_mvarId_4873_);
    return v_res_4885_;
}
pub unsafe fn _init_l_Lean_occursCheck___at___00Lean_Elab_Tactic_elabRewrite_spec__2___closed__0()
-> *mut LeanObject {
    let mut v___x_4886_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4887_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4888_: *mut LeanObject = core::ptr::null_mut();
    v___x_4886_ = lean_box(0);
    v___x_4887_ = lean_unsigned_to_nat(16);
    v___x_4888_ = lean_mk_array(v___x_4887_, v___x_4886_);
    return v___x_4888_;
}
pub unsafe fn _init_l_Lean_occursCheck___at___00Lean_Elab_Tactic_elabRewrite_spec__2___closed__1()
-> *mut LeanObject {
    let mut v___x_4889_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4890_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4891_: *mut LeanObject = core::ptr::null_mut();
    v___x_4889_ = lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_occursCheck___at___00Lean_Elab_Tactic_elabRewrite_spec__2___closed__0
        ),
        core::ptr::addr_of_mut!(
            l_Lean_occursCheck___at___00Lean_Elab_Tactic_elabRewrite_spec__2___closed__0_once
        ),
        _init_l_Lean_occursCheck___at___00Lean_Elab_Tactic_elabRewrite_spec__2___closed__0,
    );
    v___x_4890_ = lean_unsigned_to_nat(0);
    v___x_4891_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_4891_, 0, v___x_4890_);
    lean_ctor_set(v___x_4891_, 1, v___x_4889_);
    return v___x_4891_;
}
pub unsafe fn l_Lean_occursCheck___at___00Lean_Elab_Tactic_elabRewrite_spec__2(
    mut v_mvarId_4892_: *mut LeanObject,
    mut v_e_4893_: *mut LeanObject,
    mut v___y_4894_: *mut LeanObject,
    mut v___y_4895_: *mut LeanObject,
    mut v___y_4896_: *mut LeanObject,
    mut v___y_4897_: *mut LeanObject,
    mut v___y_4898_: *mut LeanObject,
    mut v___y_4899_: *mut LeanObject,
    mut v___y_4900_: *mut LeanObject,
    mut v___y_4901_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4903_: u8 = 0;
    let mut v___x_4904_: u8 = 0;
    let mut v___x_4905_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4906_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4907_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4908_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4909_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4911_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4912_: u8 = 0;
    let mut v_fst_4913_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4914_: u8 = 0;
    let mut v___x_4915_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4917_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4918_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4919_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4921_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4922_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4923_: u8 = 0;
    let mut v_a_4924_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4926_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4927_: u8 = 0;
    let mut v___x_4929_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4930_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4931_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4903_ = l_Lean_Expr_hasExprMVar(v_e_4893_);
                if v___x_4903_ == 0 {
                    lean_dec_ref(v_e_4893_);
                    v___x_4904_ = 1;
                    v___x_4905_ = lean_box((v___x_4904_) as usize);
                    v___x_4906_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_4906_, 0, v___x_4905_);
                    return v___x_4906_;
                } else {
                    v___x_4907_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_occursCheck___at___00Lean_Elab_Tactic_elabRewrite_spec__2___closed__1), core::ptr::addr_of_mut!(l_Lean_occursCheck___at___00Lean_Elab_Tactic_elabRewrite_spec__2___closed__1_once), _init_l_Lean_occursCheck___at___00Lean_Elab_Tactic_elabRewrite_spec__2___closed__1);
                    v___x_4908_ = l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_elabRewrite_spec__2_spec__2(v_mvarId_4892_, v_e_4893_, v___x_4907_, v___y_4894_, v___y_4895_, v___y_4896_, v___y_4897_, v___y_4898_, v___y_4899_, v___y_4900_, v___y_4901_);
                    if lean_obj_tag(v___x_4908_) == 0 {
                        v_a_4909_ = lean_ctor_get(v___x_4908_, 0);
                        v_isSharedCheck_4923_ = (!lean_is_exclusive(v___x_4908_)) as u8;
                        if v_isSharedCheck_4923_ == 0 {
                            v___x_4911_ = v___x_4908_;
                            v_isShared_4912_ = v_isSharedCheck_4923_;
                            state = 1;
                            continue;
                        } else {
                            lean_inc(v_a_4909_);
                            lean_dec(v___x_4908_);
                            v___x_4911_ = lean_box(0);
                            v_isShared_4912_ = v_isSharedCheck_4923_;
                            state = 1;
                            continue;
                        }
                    } else {
                        v_a_4924_ = lean_ctor_get(v___x_4908_, 0);
                        v_isSharedCheck_4931_ = (!lean_is_exclusive(v___x_4908_)) as u8;
                        if v_isSharedCheck_4931_ == 0 {
                            v___x_4926_ = v___x_4908_;
                            v_isShared_4927_ = v_isSharedCheck_4931_;
                            state = 4;
                            continue;
                        } else {
                            lean_inc(v_a_4924_);
                            lean_dec(v___x_4908_);
                            v___x_4926_ = lean_box(0);
                            v_isShared_4927_ = v_isSharedCheck_4931_;
                            state = 4;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v_fst_4913_ = lean_ctor_get(v_a_4909_, 0);
                lean_inc(v_fst_4913_);
                lean_dec(v_a_4909_);
                if lean_obj_tag(v_fst_4913_) == 0 {
                    lean_dec_ref_known(v_fst_4913_, 1);
                    v___x_4914_ = 0;
                    v___x_4915_ = lean_box((v___x_4914_) as usize);
                    if v_isShared_4912_ == 0 {
                        lean_ctor_set(v___x_4911_, 0, v___x_4915_);
                        v___x_4917_ = v___x_4911_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_4918_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_4918_, 0, v___x_4915_);
                        v___x_4917_ = v_reuseFailAlloc_4918_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_dec_ref_known(v_fst_4913_, 1);
                    v___x_4919_ = lean_box((v___x_4903_) as usize);
                    if v_isShared_4912_ == 0 {
                        lean_ctor_set(v___x_4911_, 0, v___x_4919_);
                        v___x_4921_ = v___x_4911_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_4922_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_4922_, 0, v___x_4919_);
                        v___x_4921_ = v_reuseFailAlloc_4922_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_4917_;
            }
            3 => {
                return v___x_4921_;
            }
            4 => {
                if v_isShared_4927_ == 0 {
                    v___x_4929_ = v___x_4926_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_4930_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4930_, 0, v_a_4924_);
                    v___x_4929_ = v_reuseFailAlloc_4930_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_4929_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_occursCheck___at___00Lean_Elab_Tactic_elabRewrite_spec__2___boxed(
    mut v_mvarId_4932_: *mut LeanObject,
    mut v_e_4933_: *mut LeanObject,
    mut v___y_4934_: *mut LeanObject,
    mut v___y_4935_: *mut LeanObject,
    mut v___y_4936_: *mut LeanObject,
    mut v___y_4937_: *mut LeanObject,
    mut v___y_4938_: *mut LeanObject,
    mut v___y_4939_: *mut LeanObject,
    mut v___y_4940_: *mut LeanObject,
    mut v___y_4941_: *mut LeanObject,
    mut v___y_4942_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4943_: *mut LeanObject = core::ptr::null_mut();
    v_res_4943_ = l_Lean_occursCheck___at___00Lean_Elab_Tactic_elabRewrite_spec__2(
        v_mvarId_4932_,
        v_e_4933_,
        v___y_4934_,
        v___y_4935_,
        v___y_4936_,
        v___y_4937_,
        v___y_4938_,
        v___y_4939_,
        v___y_4940_,
        v___y_4941_,
    );
    lean_dec(v___y_4941_);
    lean_dec_ref(v___y_4940_);
    lean_dec(v___y_4939_);
    lean_dec_ref(v___y_4938_);
    lean_dec(v___y_4937_);
    lean_dec_ref(v___y_4936_);
    lean_dec(v___y_4935_);
    lean_dec_ref(v___y_4934_);
    lean_dec(v_mvarId_4932_);
    return v_res_4943_;
}
pub unsafe fn l_List_filterTR_loop___at___00Lean_Elab_Tactic_elabRewrite_spec__1(
    mut v___x_4944_: *mut LeanObject,
    mut v___x_4945_: *mut LeanObject,
    mut v_a_4946_: *mut LeanObject,
    mut v_a_4947_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4948_: *mut LeanObject = core::ptr::null_mut();
    let mut v_head_4949_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_4950_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4952_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4953_: u8 = 0;
    let mut v___x_4954_: *mut LeanObject = core::ptr::null_mut();
    let mut v_index_4955_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4956_: u8 = 0;
    let mut v___x_4959_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4961_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4962_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_a_4946_) == 0 {
                    v___x_4948_ = l_List_reverse___redArg(v_a_4947_);
                    return v___x_4948_;
                } else {
                    v_head_4949_ = lean_ctor_get(v_a_4946_, 0);
                    v_tail_4950_ = lean_ctor_get(v_a_4946_, 1);
                    v_isSharedCheck_4962_ = (!lean_is_exclusive(v_a_4946_)) as u8;
                    if v_isSharedCheck_4962_ == 0 {
                        v___x_4952_ = v_a_4946_;
                        v_isShared_4953_ = v_isSharedCheck_4962_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_tail_4950_);
                        lean_inc(v_head_4949_);
                        lean_dec(v_a_4946_);
                        v___x_4952_ = lean_box(0);
                        v_isShared_4953_ = v_isSharedCheck_4962_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                lean_inc(v_head_4949_);
                v___x_4954_ = l_Lean_MetavarContext_getDecl(v___x_4944_, v_head_4949_);
                v_index_4955_ = lean_ctor_get(v___x_4954_, 6);
                lean_inc(v_index_4955_);
                lean_dec_ref(v___x_4954_);
                v___x_4956_ = lean_nat_dec_le(v___x_4945_, v_index_4955_);
                lean_dec(v_index_4955_);
                if v___x_4956_ == 0 {
                    lean_del_object(v___x_4952_);
                    lean_dec(v_head_4949_);
                    v_a_4946_ = v_tail_4950_;
                    state = 0;
                    continue;
                } else {
                    if v_isShared_4953_ == 0 {
                        lean_ctor_set(v___x_4952_, 1, v_a_4947_);
                        v___x_4959_ = v___x_4952_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_4961_ = lean_alloc_ctor(1, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_4961_, 0, v_head_4949_);
                        lean_ctor_set(v_reuseFailAlloc_4961_, 1, v_a_4947_);
                        v___x_4959_ = v_reuseFailAlloc_4961_;
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                v_a_4946_ = v_tail_4950_;
                v_a_4947_ = v___x_4959_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_filterTR_loop___at___00Lean_Elab_Tactic_elabRewrite_spec__1___boxed(
    mut v___x_4963_: *mut LeanObject,
    mut v___x_4964_: *mut LeanObject,
    mut v_a_4965_: *mut LeanObject,
    mut v_a_4966_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4967_: *mut LeanObject = core::ptr::null_mut();
    v_res_4967_ = l_List_filterTR_loop___at___00Lean_Elab_Tactic_elabRewrite_spec__1(
        v___x_4963_,
        v___x_4964_,
        v_a_4965_,
        v_a_4966_,
    );
    lean_dec(v___x_4964_);
    lean_dec_ref(v___x_4963_);
    return v_res_4967_;
}
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Tactic_elabRewrite_spec__3_spec__4_spec__9(
    mut v_msgData_4968_: *mut LeanObject,
    mut v___y_4969_: *mut LeanObject,
    mut v___y_4970_: *mut LeanObject,
    mut v___y_4971_: *mut LeanObject,
    mut v___y_4972_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4974_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_4975_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4976_: *mut LeanObject = core::ptr::null_mut();
    let mut v_mctx_4977_: *mut LeanObject = core::ptr::null_mut();
    let mut v_lctx_4978_: *mut LeanObject = core::ptr::null_mut();
    let mut v_options_4979_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4980_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4981_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4982_: *mut LeanObject = core::ptr::null_mut();
    v___x_4974_ = lean_st_ref_get(v___y_4972_);
    v_env_4975_ = lean_ctor_get(v___x_4974_, 0);
    lean_inc_ref(v_env_4975_);
    lean_dec(v___x_4974_);
    v___x_4976_ = lean_st_ref_get(v___y_4970_);
    v_mctx_4977_ = lean_ctor_get(v___x_4976_, 0);
    lean_inc_ref(v_mctx_4977_);
    lean_dec(v___x_4976_);
    v_lctx_4978_ = lean_ctor_get(v___y_4969_, 2);
    v_options_4979_ = lean_ctor_get(v___y_4971_, 2);
    lean_inc_ref(v_options_4979_);
    lean_inc_ref(v_lctx_4978_);
    v___x_4980_ = lean_alloc_ctor(0, 4, (0) as u32);
    lean_ctor_set(v___x_4980_, 0, v_env_4975_);
    lean_ctor_set(v___x_4980_, 1, v_mctx_4977_);
    lean_ctor_set(v___x_4980_, 2, v_lctx_4978_);
    lean_ctor_set(v___x_4980_, 3, v_options_4979_);
    v___x_4981_ = lean_alloc_ctor(3, 2, (0) as u32);
    lean_ctor_set(v___x_4981_, 0, v___x_4980_);
    lean_ctor_set(v___x_4981_, 1, v_msgData_4968_);
    v___x_4982_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_4982_, 0, v___x_4981_);
    return v___x_4982_;
}
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Tactic_elabRewrite_spec__3_spec__4_spec__9___boxed(
    mut v_msgData_4983_: *mut LeanObject,
    mut v___y_4984_: *mut LeanObject,
    mut v___y_4985_: *mut LeanObject,
    mut v___y_4986_: *mut LeanObject,
    mut v___y_4987_: *mut LeanObject,
    mut v___y_4988_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4989_: *mut LeanObject = core::ptr::null_mut();
    v_res_4989_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Tactic_elabRewrite_spec__3_spec__4_spec__9(v_msgData_4983_, v___y_4984_, v___y_4985_, v___y_4986_, v___y_4987_);
    lean_dec(v___y_4987_);
    lean_dec_ref(v___y_4986_);
    lean_dec(v___y_4985_);
    lean_dec_ref(v___y_4984_);
    return v_res_4989_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Tactic_elabRewrite_spec__3_spec__4___redArg(
    mut v_msg_4990_: *mut LeanObject,
    mut v___y_4991_: *mut LeanObject,
    mut v___y_4992_: *mut LeanObject,
    mut v___y_4993_: *mut LeanObject,
    mut v___y_4994_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_ref_4996_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4997_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4998_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5000_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5001_: u8 = 0;
    let mut v___x_5002_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5004_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5005_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5006_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ref_4996_ = lean_ctor_get(v___y_4993_, 5);
                v___x_4997_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Tactic_elabRewrite_spec__3_spec__4_spec__9(v_msg_4990_, v___y_4991_, v___y_4992_, v___y_4993_, v___y_4994_);
                v_a_4998_ = lean_ctor_get(v___x_4997_, 0);
                v_isSharedCheck_5006_ = (!lean_is_exclusive(v___x_4997_)) as u8;
                if v_isSharedCheck_5006_ == 0 {
                    v___x_5000_ = v___x_4997_;
                    v_isShared_5001_ = v_isSharedCheck_5006_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_a_4998_);
                    lean_dec(v___x_4997_);
                    v___x_5000_ = lean_box(0);
                    v_isShared_5001_ = v_isSharedCheck_5006_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                lean_inc(v_ref_4996_);
                v___x_5002_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_5002_, 0, v_ref_4996_);
                lean_ctor_set(v___x_5002_, 1, v_a_4998_);
                if v_isShared_5001_ == 0 {
                    lean_ctor_set_tag(v___x_5000_, 1);
                    lean_ctor_set(v___x_5000_, 0, v___x_5002_);
                    v___x_5004_ = v___x_5000_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5005_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5005_, 0, v___x_5002_);
                    v___x_5004_ = v_reuseFailAlloc_5005_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_5004_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Tactic_elabRewrite_spec__3_spec__4___redArg___boxed(
    mut v_msg_5007_: *mut LeanObject,
    mut v___y_5008_: *mut LeanObject,
    mut v___y_5009_: *mut LeanObject,
    mut v___y_5010_: *mut LeanObject,
    mut v___y_5011_: *mut LeanObject,
    mut v___y_5012_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5013_: *mut LeanObject = core::ptr::null_mut();
    v_res_5013_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Tactic_elabRewrite_spec__3_spec__4___redArg(v_msg_5007_, v___y_5008_, v___y_5009_, v___y_5010_, v___y_5011_);
    lean_dec(v___y_5011_);
    lean_dec_ref(v___y_5010_);
    lean_dec(v___y_5009_);
    lean_dec_ref(v___y_5008_);
    return v_res_5013_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00Lean_Elab_Tactic_elabRewrite_spec__3___redArg(
    mut v_ref_5014_: *mut LeanObject,
    mut v_msg_5015_: *mut LeanObject,
    mut v___y_5016_: *mut LeanObject,
    mut v___y_5017_: *mut LeanObject,
    mut v___y_5018_: *mut LeanObject,
    mut v___y_5019_: *mut LeanObject,
    mut v___y_5020_: *mut LeanObject,
    mut v___y_5021_: *mut LeanObject,
    mut v___y_5022_: *mut LeanObject,
    mut v___y_5023_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_fileName_5025_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fileMap_5026_: *mut LeanObject = core::ptr::null_mut();
    let mut v_options_5027_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currRecDepth_5028_: *mut LeanObject = core::ptr::null_mut();
    let mut v_maxRecDepth_5029_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ref_5030_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currNamespace_5031_: *mut LeanObject = core::ptr::null_mut();
    let mut v_openDecls_5032_: *mut LeanObject = core::ptr::null_mut();
    let mut v_initHeartbeats_5033_: *mut LeanObject = core::ptr::null_mut();
    let mut v_maxHeartbeats_5034_: *mut LeanObject = core::ptr::null_mut();
    let mut v_quotContext_5035_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currMacroScope_5036_: *mut LeanObject = core::ptr::null_mut();
    let mut v_diag_5037_: u8 = 0;
    let mut v_cancelTk_x3f_5038_: *mut LeanObject = core::ptr::null_mut();
    let mut v_suppressElabErrors_5039_: u8 = 0;
    let mut v_inheritedTraceOptions_5040_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ref_5041_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5042_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5043_: *mut LeanObject = core::ptr::null_mut();
    v_fileName_5025_ = lean_ctor_get(v___y_5022_, 0);
    v_fileMap_5026_ = lean_ctor_get(v___y_5022_, 1);
    v_options_5027_ = lean_ctor_get(v___y_5022_, 2);
    v_currRecDepth_5028_ = lean_ctor_get(v___y_5022_, 3);
    v_maxRecDepth_5029_ = lean_ctor_get(v___y_5022_, 4);
    v_ref_5030_ = lean_ctor_get(v___y_5022_, 5);
    v_currNamespace_5031_ = lean_ctor_get(v___y_5022_, 6);
    v_openDecls_5032_ = lean_ctor_get(v___y_5022_, 7);
    v_initHeartbeats_5033_ = lean_ctor_get(v___y_5022_, 8);
    v_maxHeartbeats_5034_ = lean_ctor_get(v___y_5022_, 9);
    v_quotContext_5035_ = lean_ctor_get(v___y_5022_, 10);
    v_currMacroScope_5036_ = lean_ctor_get(v___y_5022_, 11);
    v_diag_5037_ = lean_ctor_get_uint8(
        v___y_5022_,
        (core::mem::size_of::<*mut LeanObject>() * 14) as u32,
    );
    v_cancelTk_x3f_5038_ = lean_ctor_get(v___y_5022_, 12);
    v_suppressElabErrors_5039_ = lean_ctor_get_uint8(
        v___y_5022_,
        (core::mem::size_of::<*mut LeanObject>() * 14 + 1) as u32,
    );
    v_inheritedTraceOptions_5040_ = lean_ctor_get(v___y_5022_, 13);
    v_ref_5041_ = l_Lean_replaceRef(v_ref_5014_, v_ref_5030_);
    lean_inc_ref(v_inheritedTraceOptions_5040_);
    lean_inc(v_cancelTk_x3f_5038_);
    lean_inc(v_currMacroScope_5036_);
    lean_inc(v_quotContext_5035_);
    lean_inc(v_maxHeartbeats_5034_);
    lean_inc(v_initHeartbeats_5033_);
    lean_inc(v_openDecls_5032_);
    lean_inc(v_currNamespace_5031_);
    lean_inc(v_maxRecDepth_5029_);
    lean_inc(v_currRecDepth_5028_);
    lean_inc_ref(v_options_5027_);
    lean_inc_ref(v_fileMap_5026_);
    lean_inc_ref(v_fileName_5025_);
    v___x_5042_ = lean_alloc_ctor(0, 14, (2) as u32);
    lean_ctor_set(v___x_5042_, 0, v_fileName_5025_);
    lean_ctor_set(v___x_5042_, 1, v_fileMap_5026_);
    lean_ctor_set(v___x_5042_, 2, v_options_5027_);
    lean_ctor_set(v___x_5042_, 3, v_currRecDepth_5028_);
    lean_ctor_set(v___x_5042_, 4, v_maxRecDepth_5029_);
    lean_ctor_set(v___x_5042_, 5, v_ref_5041_);
    lean_ctor_set(v___x_5042_, 6, v_currNamespace_5031_);
    lean_ctor_set(v___x_5042_, 7, v_openDecls_5032_);
    lean_ctor_set(v___x_5042_, 8, v_initHeartbeats_5033_);
    lean_ctor_set(v___x_5042_, 9, v_maxHeartbeats_5034_);
    lean_ctor_set(v___x_5042_, 10, v_quotContext_5035_);
    lean_ctor_set(v___x_5042_, 11, v_currMacroScope_5036_);
    lean_ctor_set(v___x_5042_, 12, v_cancelTk_x3f_5038_);
    lean_ctor_set(v___x_5042_, 13, v_inheritedTraceOptions_5040_);
    lean_ctor_set_uint8(
        v___x_5042_,
        (core::mem::size_of::<*mut LeanObject>() * 14) as u32,
        v_diag_5037_,
    );
    lean_ctor_set_uint8(
        v___x_5042_,
        (core::mem::size_of::<*mut LeanObject>() * 14 + 1) as u32,
        v_suppressElabErrors_5039_,
    );
    v___x_5043_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Tactic_elabRewrite_spec__3_spec__4___redArg(v_msg_5015_, v___y_5020_, v___y_5021_, v___x_5042_, v___y_5023_);
    lean_dec_ref_known(v___x_5042_, 14);
    return v___x_5043_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00Lean_Elab_Tactic_elabRewrite_spec__3___redArg___boxed(
    mut v_ref_5044_: *mut LeanObject,
    mut v_msg_5045_: *mut LeanObject,
    mut v___y_5046_: *mut LeanObject,
    mut v___y_5047_: *mut LeanObject,
    mut v___y_5048_: *mut LeanObject,
    mut v___y_5049_: *mut LeanObject,
    mut v___y_5050_: *mut LeanObject,
    mut v___y_5051_: *mut LeanObject,
    mut v___y_5052_: *mut LeanObject,
    mut v___y_5053_: *mut LeanObject,
    mut v___y_5054_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5055_: *mut LeanObject = core::ptr::null_mut();
    v_res_5055_ = l_Lean_throwErrorAt___at___00Lean_Elab_Tactic_elabRewrite_spec__3___redArg(
        v_ref_5044_,
        v_msg_5045_,
        v___y_5046_,
        v___y_5047_,
        v___y_5048_,
        v___y_5049_,
        v___y_5050_,
        v___y_5051_,
        v___y_5052_,
        v___y_5053_,
    );
    lean_dec(v___y_5053_);
    lean_dec_ref(v___y_5052_);
    lean_dec(v___y_5051_);
    lean_dec_ref(v___y_5050_);
    lean_dec(v___y_5049_);
    lean_dec_ref(v___y_5048_);
    lean_dec(v___y_5047_);
    lean_dec_ref(v___y_5046_);
    lean_dec(v_ref_5044_);
    return v_res_5055_;
}
pub unsafe fn _init_l_Lean_Elab_Tactic_elabRewrite___closed__1() -> *mut LeanObject {
    let mut v___x_5057_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5058_: *mut LeanObject = core::ptr::null_mut();
    v___x_5057_ = l_Lean_Elab_Tactic_elabRewrite___closed__0;
    v___x_5058_ = l_Lean_stringToMessageData(v___x_5057_);
    return v___x_5058_;
}
pub unsafe fn _init_l_Lean_Elab_Tactic_elabRewrite___closed__3() -> *mut LeanObject {
    let mut v___x_5060_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5061_: *mut LeanObject = core::ptr::null_mut();
    v___x_5060_ = l_Lean_Elab_Tactic_elabRewrite___closed__2;
    v___x_5061_ = l_Lean_stringToMessageData(v___x_5060_);
    return v___x_5061_;
}
pub unsafe fn l_Lean_Elab_Tactic_elabRewrite(
    mut v_mvarId_5062_: *mut LeanObject,
    mut v_e_5063_: *mut LeanObject,
    mut v_stx_5064_: *mut LeanObject,
    mut v_symm_5065_: u8,
    mut v_config_5066_: *mut LeanObject,
    mut v_a_5067_: *mut LeanObject,
    mut v_a_5068_: *mut LeanObject,
    mut v_a_5069_: *mut LeanObject,
    mut v_a_5070_: *mut LeanObject,
    mut v_a_5071_: *mut LeanObject,
    mut v_a_5072_: *mut LeanObject,
    mut v_a_5073_: *mut LeanObject,
    mut v_a_5074_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5076_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5077_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5078_: u8 = 0;
    let mut v___x_5079_: *mut LeanObject = core::ptr::null_mut();
    let mut v_mctx_5080_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5081_: *mut LeanObject = core::ptr::null_mut();
    let mut v_mvarCounter_5082_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5083_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_5084_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5086_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5087_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5088_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5089_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5090_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5091_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5092_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5093_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5094_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5095_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5097_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5098_: u8 = 0;
    let mut v___x_5099_: *mut LeanObject = core::ptr::null_mut();
    let mut v_mctx_5100_: *mut LeanObject = core::ptr::null_mut();
    let mut v_eNew_5101_: *mut LeanObject = core::ptr::null_mut();
    let mut v_eqProof_5102_: *mut LeanObject = core::ptr::null_mut();
    let mut v_mvarIds_5103_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5105_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5106_: u8 = 0;
    let mut v___x_5107_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5108_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5110_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5112_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5113_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5114_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5115_: u8 = 0;
    let mut v_isSharedCheck_5116_: u8 = 0;
    let mut v___y_5118_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5119_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5120_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5121_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5122_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5123_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5124_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5125_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5126_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5127_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5128_: u8 = 0;
    let mut v___x_5129_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5130_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5131_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5132_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5133_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5134_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5135_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5136_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5137_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5138_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5140_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5141_: u8 = 0;
    let mut v___x_5143_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5144_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5145_: u8 = 0;
    let mut v_a_5146_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5148_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5149_: u8 = 0;
    let mut v___x_5151_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5152_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5153_: u8 = 0;
    let mut v___x_5154_: u8 = 0;
    let mut v___x_5155_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5156_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5158_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5159_: u8 = 0;
    let mut v___x_5161_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5162_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5163_: u8 = 0;
    let mut v_a_5164_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5166_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5167_: u8 = 0;
    let mut v___x_5169_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5170_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5171_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5076_ = lean_st_ref_get(v_a_5072_);
                v___x_5077_ = lean_box(0);
                v___x_5078_ = 1;
                lean_inc(v_stx_5064_);
                v___x_5079_ = l_Lean_Elab_Tactic_elabTerm(
                    v_stx_5064_,
                    v___x_5077_,
                    v___x_5078_,
                    v_a_5067_,
                    v_a_5068_,
                    v_a_5069_,
                    v_a_5070_,
                    v_a_5071_,
                    v_a_5072_,
                    v_a_5073_,
                    v_a_5074_,
                );
                if lean_obj_tag(v___x_5079_) == 0 {
                    v_mctx_5080_ = lean_ctor_get(v___x_5076_, 0);
                    lean_inc_ref(v_mctx_5080_);
                    lean_dec(v___x_5076_);
                    v_a_5081_ = lean_ctor_get(v___x_5079_, 0);
                    lean_inc_n(v_a_5081_, 2);
                    lean_dec_ref_known(v___x_5079_, 1);
                    v_mvarCounter_5082_ = lean_ctor_get(v_mctx_5080_, 3);
                    lean_inc(v_mvarCounter_5082_);
                    lean_dec_ref(v_mctx_5080_);
                    v___x_5083_ = lean_box((v_symm_5065_) as usize);
                    lean_inc_ref(v_e_5063_);
                    lean_inc(v_mvarId_5062_);
                    v___f_5084_ = lean_alloc_closure(
                        l_Lean_Elab_Tactic_elabRewrite___lam__0___boxed as *mut core::ffi::c_void,
                        14,
                        5,
                    );
                    lean_closure_set(v___f_5084_, 0, v_mvarId_5062_);
                    lean_closure_set(v___f_5084_, 1, v_e_5063_);
                    lean_closure_set(v___f_5084_, 2, v_a_5081_);
                    lean_closure_set(v___f_5084_, 3, v___x_5083_);
                    lean_closure_set(v___f_5084_, 4, v_config_5066_);
                    v___x_5154_ = l_Lean_Expr_hasSyntheticSorry(v_a_5081_);
                    if v___x_5154_ == 0 {
                        v___y_5118_ = v_a_5067_;
                        v___y_5119_ = v_a_5068_;
                        v___y_5120_ = v_a_5069_;
                        v___y_5121_ = v_a_5070_;
                        v___y_5122_ = v_a_5071_;
                        v___y_5123_ = v_a_5072_;
                        v___y_5124_ = v_a_5073_;
                        v___y_5125_ = v_a_5074_;
                        state = 6;
                        continue;
                    } else {
                        lean_dec_ref(v___f_5084_);
                        lean_dec(v_mvarCounter_5082_);
                        lean_dec(v_a_5081_);
                        lean_dec(v_stx_5064_);
                        lean_dec_ref(v_e_5063_);
                        lean_dec(v_mvarId_5062_);
                        v___x_5155_ = l_Lean_Elab_throwAbortTactic___at___00Lean_Elab_Tactic_elabRewrite_spec__4___redArg();
                        v_a_5156_ = lean_ctor_get(v___x_5155_, 0);
                        v_isSharedCheck_5163_ = (!lean_is_exclusive(v___x_5155_)) as u8;
                        if v_isSharedCheck_5163_ == 0 {
                            v___x_5158_ = v___x_5155_;
                            v_isShared_5159_ = v_isSharedCheck_5163_;
                            state = 11;
                            continue;
                        } else {
                            lean_inc(v_a_5156_);
                            lean_dec(v___x_5155_);
                            v___x_5158_ = lean_box(0);
                            v_isShared_5159_ = v_isSharedCheck_5163_;
                            state = 11;
                            continue;
                        }
                    }
                } else {
                    lean_dec(v___x_5076_);
                    lean_dec_ref(v_config_5066_);
                    lean_dec(v_stx_5064_);
                    lean_dec_ref(v_e_5063_);
                    lean_dec(v_mvarId_5062_);
                    v_a_5164_ = lean_ctor_get(v___x_5079_, 0);
                    v_isSharedCheck_5171_ = (!lean_is_exclusive(v___x_5079_)) as u8;
                    if v_isSharedCheck_5171_ == 0 {
                        v___x_5166_ = v___x_5079_;
                        v_isShared_5167_ = v_isSharedCheck_5171_;
                        state = 13;
                        continue;
                    } else {
                        lean_inc(v_a_5164_);
                        lean_dec(v___x_5079_);
                        v___x_5166_ = lean_box(0);
                        v_isShared_5167_ = v_isSharedCheck_5171_;
                        state = 13;
                        continue;
                    }
                }
            }
            1 => {
                v___x_5094_ = l_Lean_Meta_withInstancesTypeCheckNote___at___00Lean_Elab_Tactic_elabRewrite_spec__0___redArg(v_e_5063_, v___f_5084_, v___y_5086_, v___y_5087_, v___y_5088_, v___y_5089_, v___y_5090_, v___y_5091_, v___y_5092_, v___y_5093_);
                if lean_obj_tag(v___x_5094_) == 0 {
                    v_a_5095_ = lean_ctor_get(v___x_5094_, 0);
                    v_isSharedCheck_5116_ = (!lean_is_exclusive(v___x_5094_)) as u8;
                    if v_isSharedCheck_5116_ == 0 {
                        v___x_5097_ = v___x_5094_;
                        v_isShared_5098_ = v_isSharedCheck_5116_;
                        state = 2;
                        continue;
                    } else {
                        lean_inc(v_a_5095_);
                        lean_dec(v___x_5094_);
                        v___x_5097_ = lean_box(0);
                        v_isShared_5098_ = v_isSharedCheck_5116_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_dec(v_mvarCounter_5082_);
                    return v___x_5094_;
                }
            }
            2 => {
                v___x_5099_ = lean_st_ref_get(v___y_5091_);
                v_mctx_5100_ = lean_ctor_get(v___x_5099_, 0);
                lean_inc_ref(v_mctx_5100_);
                lean_dec(v___x_5099_);
                v_eNew_5101_ = lean_ctor_get(v_a_5095_, 0);
                v_eqProof_5102_ = lean_ctor_get(v_a_5095_, 1);
                v_mvarIds_5103_ = lean_ctor_get(v_a_5095_, 2);
                v_isSharedCheck_5115_ = (!lean_is_exclusive(v_a_5095_)) as u8;
                if v_isSharedCheck_5115_ == 0 {
                    v___x_5105_ = v_a_5095_;
                    v_isShared_5106_ = v_isSharedCheck_5115_;
                    state = 3;
                    continue;
                } else {
                    lean_inc(v_mvarIds_5103_);
                    lean_inc(v_eqProof_5102_);
                    lean_inc(v_eNew_5101_);
                    lean_dec(v_a_5095_);
                    v___x_5105_ = lean_box(0);
                    v_isShared_5106_ = v_isSharedCheck_5115_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_5107_ = lean_box(0);
                v___x_5108_ = l_List_filterTR_loop___at___00Lean_Elab_Tactic_elabRewrite_spec__1(
                    v_mctx_5100_,
                    v_mvarCounter_5082_,
                    v_mvarIds_5103_,
                    v___x_5107_,
                );
                lean_dec(v_mvarCounter_5082_);
                lean_dec_ref(v_mctx_5100_);
                if v_isShared_5106_ == 0 {
                    lean_ctor_set(v___x_5105_, 2, v___x_5108_);
                    v___x_5110_ = v___x_5105_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_5114_ = lean_alloc_ctor(0, 3, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5114_, 0, v_eNew_5101_);
                    lean_ctor_set(v_reuseFailAlloc_5114_, 1, v_eqProof_5102_);
                    lean_ctor_set(v_reuseFailAlloc_5114_, 2, v___x_5108_);
                    v___x_5110_ = v_reuseFailAlloc_5114_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                if v_isShared_5098_ == 0 {
                    lean_ctor_set(v___x_5097_, 0, v___x_5110_);
                    v___x_5112_ = v___x_5097_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_5113_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5113_, 0, v___x_5110_);
                    v___x_5112_ = v_reuseFailAlloc_5113_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_5112_;
            }
            6 => {
                lean_inc(v_a_5081_);
                v___x_5126_ = l_Lean_occursCheck___at___00Lean_Elab_Tactic_elabRewrite_spec__2(
                    v_mvarId_5062_,
                    v_a_5081_,
                    v___y_5118_,
                    v___y_5119_,
                    v___y_5120_,
                    v___y_5121_,
                    v___y_5122_,
                    v___y_5123_,
                    v___y_5124_,
                    v___y_5125_,
                );
                if lean_obj_tag(v___x_5126_) == 0 {
                    v_a_5127_ = lean_ctor_get(v___x_5126_, 0);
                    lean_inc(v_a_5127_);
                    lean_dec_ref_known(v___x_5126_, 1);
                    v___x_5128_ = (lean_unbox(v_a_5127_) as u8);
                    lean_dec(v_a_5127_);
                    if v___x_5128_ == 0 {
                        lean_dec_ref(v___f_5084_);
                        lean_dec(v_mvarCounter_5082_);
                        lean_dec_ref(v_e_5063_);
                        v___x_5129_ = lean_obj_once(
                            core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_elabRewrite___closed__1),
                            core::ptr::addr_of_mut!(
                                l_Lean_Elab_Tactic_elabRewrite___closed__1_once
                            ),
                            _init_l_Lean_Elab_Tactic_elabRewrite___closed__1,
                        );
                        v___x_5130_ = l_Lean_indentExpr(v_a_5081_);
                        v___x_5131_ = lean_alloc_ctor(7, 2, (0) as u32);
                        lean_ctor_set(v___x_5131_, 0, v___x_5129_);
                        lean_ctor_set(v___x_5131_, 1, v___x_5130_);
                        v___x_5132_ = lean_obj_once(
                            core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_elabRewrite___closed__3),
                            core::ptr::addr_of_mut!(
                                l_Lean_Elab_Tactic_elabRewrite___closed__3_once
                            ),
                            _init_l_Lean_Elab_Tactic_elabRewrite___closed__3,
                        );
                        v___x_5133_ = lean_alloc_ctor(7, 2, (0) as u32);
                        lean_ctor_set(v___x_5133_, 0, v___x_5131_);
                        lean_ctor_set(v___x_5133_, 1, v___x_5132_);
                        v___x_5134_ = l_Lean_Expr_mvar___override(v_mvarId_5062_);
                        v___x_5135_ = l_Lean_MessageData_ofExpr(v___x_5134_);
                        v___x_5136_ = lean_alloc_ctor(7, 2, (0) as u32);
                        lean_ctor_set(v___x_5136_, 0, v___x_5133_);
                        lean_ctor_set(v___x_5136_, 1, v___x_5135_);
                        v___x_5137_ = l_Lean_throwErrorAt___at___00Lean_Elab_Tactic_elabRewrite_spec__3___redArg(v_stx_5064_, v___x_5136_, v___y_5118_, v___y_5119_, v___y_5120_, v___y_5121_, v___y_5122_, v___y_5123_, v___y_5124_, v___y_5125_);
                        lean_dec(v_stx_5064_);
                        v_a_5138_ = lean_ctor_get(v___x_5137_, 0);
                        v_isSharedCheck_5145_ = (!lean_is_exclusive(v___x_5137_)) as u8;
                        if v_isSharedCheck_5145_ == 0 {
                            v___x_5140_ = v___x_5137_;
                            v_isShared_5141_ = v_isSharedCheck_5145_;
                            state = 7;
                            continue;
                        } else {
                            lean_inc(v_a_5138_);
                            lean_dec(v___x_5137_);
                            v___x_5140_ = lean_box(0);
                            v_isShared_5141_ = v_isSharedCheck_5145_;
                            state = 7;
                            continue;
                        }
                    } else {
                        lean_dec(v_a_5081_);
                        lean_dec(v_stx_5064_);
                        lean_dec(v_mvarId_5062_);
                        v___y_5086_ = v___y_5118_;
                        v___y_5087_ = v___y_5119_;
                        v___y_5088_ = v___y_5120_;
                        v___y_5089_ = v___y_5121_;
                        v___y_5090_ = v___y_5122_;
                        v___y_5091_ = v___y_5123_;
                        v___y_5092_ = v___y_5124_;
                        v___y_5093_ = v___y_5125_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec_ref(v___f_5084_);
                    lean_dec(v_mvarCounter_5082_);
                    lean_dec(v_a_5081_);
                    lean_dec(v_stx_5064_);
                    lean_dec_ref(v_e_5063_);
                    lean_dec(v_mvarId_5062_);
                    v_a_5146_ = lean_ctor_get(v___x_5126_, 0);
                    v_isSharedCheck_5153_ = (!lean_is_exclusive(v___x_5126_)) as u8;
                    if v_isSharedCheck_5153_ == 0 {
                        v___x_5148_ = v___x_5126_;
                        v_isShared_5149_ = v_isSharedCheck_5153_;
                        state = 9;
                        continue;
                    } else {
                        lean_inc(v_a_5146_);
                        lean_dec(v___x_5126_);
                        v___x_5148_ = lean_box(0);
                        v_isShared_5149_ = v_isSharedCheck_5153_;
                        state = 9;
                        continue;
                    }
                }
            }
            7 => {
                if v_isShared_5141_ == 0 {
                    v___x_5143_ = v___x_5140_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_5144_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5144_, 0, v_a_5138_);
                    v___x_5143_ = v_reuseFailAlloc_5144_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_5143_;
            }
            9 => {
                if v_isShared_5149_ == 0 {
                    v___x_5151_ = v___x_5148_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_5152_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5152_, 0, v_a_5146_);
                    v___x_5151_ = v_reuseFailAlloc_5152_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_5151_;
            }
            11 => {
                if v_isShared_5159_ == 0 {
                    v___x_5161_ = v___x_5158_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_5162_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5162_, 0, v_a_5156_);
                    v___x_5161_ = v_reuseFailAlloc_5162_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                return v___x_5161_;
            }
            13 => {
                if v_isShared_5167_ == 0 {
                    v___x_5169_ = v___x_5166_;
                    state = 14;
                    continue;
                } else {
                    v_reuseFailAlloc_5170_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5170_, 0, v_a_5164_);
                    v___x_5169_ = v_reuseFailAlloc_5170_;
                    state = 14;
                    continue;
                }
            }
            14 => {
                return v___x_5169_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_Tactic_elabRewrite___boxed(
    mut v_mvarId_5172_: *mut LeanObject,
    mut v_e_5173_: *mut LeanObject,
    mut v_stx_5174_: *mut LeanObject,
    mut v_symm_5175_: *mut LeanObject,
    mut v_config_5176_: *mut LeanObject,
    mut v_a_5177_: *mut LeanObject,
    mut v_a_5178_: *mut LeanObject,
    mut v_a_5179_: *mut LeanObject,
    mut v_a_5180_: *mut LeanObject,
    mut v_a_5181_: *mut LeanObject,
    mut v_a_5182_: *mut LeanObject,
    mut v_a_5183_: *mut LeanObject,
    mut v_a_5184_: *mut LeanObject,
    mut v_a_5185_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_symm_boxed_5186_: u8 = 0;
    let mut v_res_5187_: *mut LeanObject = core::ptr::null_mut();
    v_symm_boxed_5186_ = (lean_unbox(v_symm_5175_) as u8);
    v_res_5187_ = l_Lean_Elab_Tactic_elabRewrite(
        v_mvarId_5172_,
        v_e_5173_,
        v_stx_5174_,
        v_symm_boxed_5186_,
        v_config_5176_,
        v_a_5177_,
        v_a_5178_,
        v_a_5179_,
        v_a_5180_,
        v_a_5181_,
        v_a_5182_,
        v_a_5183_,
        v_a_5184_,
    );
    lean_dec(v_a_5184_);
    lean_dec_ref(v_a_5183_);
    lean_dec(v_a_5182_);
    lean_dec_ref(v_a_5181_);
    lean_dec(v_a_5180_);
    lean_dec_ref(v_a_5179_);
    lean_dec(v_a_5178_);
    lean_dec_ref(v_a_5177_);
    return v_res_5187_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00Lean_Elab_Tactic_elabRewrite_spec__3(
    mut v_00_u03b1_5188_: *mut LeanObject,
    mut v_ref_5189_: *mut LeanObject,
    mut v_msg_5190_: *mut LeanObject,
    mut v___y_5191_: *mut LeanObject,
    mut v___y_5192_: *mut LeanObject,
    mut v___y_5193_: *mut LeanObject,
    mut v___y_5194_: *mut LeanObject,
    mut v___y_5195_: *mut LeanObject,
    mut v___y_5196_: *mut LeanObject,
    mut v___y_5197_: *mut LeanObject,
    mut v___y_5198_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5200_: *mut LeanObject = core::ptr::null_mut();
    v___x_5200_ = l_Lean_throwErrorAt___at___00Lean_Elab_Tactic_elabRewrite_spec__3___redArg(
        v_ref_5189_,
        v_msg_5190_,
        v___y_5191_,
        v___y_5192_,
        v___y_5193_,
        v___y_5194_,
        v___y_5195_,
        v___y_5196_,
        v___y_5197_,
        v___y_5198_,
    );
    return v___x_5200_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00Lean_Elab_Tactic_elabRewrite_spec__3___boxed(
    mut v_00_u03b1_5201_: *mut LeanObject,
    mut v_ref_5202_: *mut LeanObject,
    mut v_msg_5203_: *mut LeanObject,
    mut v___y_5204_: *mut LeanObject,
    mut v___y_5205_: *mut LeanObject,
    mut v___y_5206_: *mut LeanObject,
    mut v___y_5207_: *mut LeanObject,
    mut v___y_5208_: *mut LeanObject,
    mut v___y_5209_: *mut LeanObject,
    mut v___y_5210_: *mut LeanObject,
    mut v___y_5211_: *mut LeanObject,
    mut v___y_5212_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5213_: *mut LeanObject = core::ptr::null_mut();
    v_res_5213_ = l_Lean_throwErrorAt___at___00Lean_Elab_Tactic_elabRewrite_spec__3(
        v_00_u03b1_5201_,
        v_ref_5202_,
        v_msg_5203_,
        v___y_5204_,
        v___y_5205_,
        v___y_5206_,
        v___y_5207_,
        v___y_5208_,
        v___y_5209_,
        v___y_5210_,
        v___y_5211_,
    );
    lean_dec(v___y_5211_);
    lean_dec_ref(v___y_5210_);
    lean_dec(v___y_5209_);
    lean_dec_ref(v___y_5208_);
    lean_dec(v___y_5207_);
    lean_dec_ref(v___y_5206_);
    lean_dec(v___y_5205_);
    lean_dec_ref(v___y_5204_);
    lean_dec(v_ref_5202_);
    return v_res_5213_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Tactic_elabRewrite_spec__3_spec__4(
    mut v_00_u03b1_5214_: *mut LeanObject,
    mut v_msg_5215_: *mut LeanObject,
    mut v___y_5216_: *mut LeanObject,
    mut v___y_5217_: *mut LeanObject,
    mut v___y_5218_: *mut LeanObject,
    mut v___y_5219_: *mut LeanObject,
    mut v___y_5220_: *mut LeanObject,
    mut v___y_5221_: *mut LeanObject,
    mut v___y_5222_: *mut LeanObject,
    mut v___y_5223_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5225_: *mut LeanObject = core::ptr::null_mut();
    v___x_5225_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Tactic_elabRewrite_spec__3_spec__4___redArg(v_msg_5215_, v___y_5220_, v___y_5221_, v___y_5222_, v___y_5223_);
    return v___x_5225_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Tactic_elabRewrite_spec__3_spec__4___boxed(
    mut v_00_u03b1_5226_: *mut LeanObject,
    mut v_msg_5227_: *mut LeanObject,
    mut v___y_5228_: *mut LeanObject,
    mut v___y_5229_: *mut LeanObject,
    mut v___y_5230_: *mut LeanObject,
    mut v___y_5231_: *mut LeanObject,
    mut v___y_5232_: *mut LeanObject,
    mut v___y_5233_: *mut LeanObject,
    mut v___y_5234_: *mut LeanObject,
    mut v___y_5235_: *mut LeanObject,
    mut v___y_5236_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5237_: *mut LeanObject = core::ptr::null_mut();
    v_res_5237_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Tactic_elabRewrite_spec__3_spec__4(v_00_u03b1_5226_, v_msg_5227_, v___y_5228_, v___y_5229_, v___y_5230_, v___y_5231_, v___y_5232_, v___y_5233_, v___y_5234_, v___y_5235_);
    lean_dec(v___y_5235_);
    lean_dec_ref(v___y_5234_);
    lean_dec(v___y_5233_);
    lean_dec_ref(v___y_5232_);
    lean_dec(v___y_5231_);
    lean_dec_ref(v___y_5230_);
    lean_dec(v___y_5229_);
    lean_dec_ref(v___y_5228_);
    return v_res_5237_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_elabRewrite_spec__2_spec__2_spec__4(
    mut v_00_u03b2_5238_: *mut LeanObject,
    mut v_m_5239_: *mut LeanObject,
    mut v_a_5240_: *mut LeanObject,
) -> u8 {
    let mut v___x_5241_: u8 = 0;
    v___x_5241_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_elabRewrite_spec__2_spec__2_spec__4___redArg(v_m_5239_, v_a_5240_);
    return v___x_5241_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_elabRewrite_spec__2_spec__2_spec__4___boxed(
    mut v_00_u03b2_5242_: *mut LeanObject,
    mut v_m_5243_: *mut LeanObject,
    mut v_a_5244_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5245_: u8 = 0;
    let mut v_r_5246_: *mut LeanObject = core::ptr::null_mut();
    v_res_5245_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_elabRewrite_spec__2_spec__2_spec__4(v_00_u03b2_5242_, v_m_5243_, v_a_5244_);
    lean_dec_ref(v_a_5244_);
    lean_dec_ref(v_m_5243_);
    v_r_5246_ = lean_box((v_res_5245_) as usize);
    return v_r_5246_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_elabRewrite_spec__2_spec__2_spec__5(
    mut v_00_u03b2_5247_: *mut LeanObject,
    mut v_m_5248_: *mut LeanObject,
    mut v_a_5249_: *mut LeanObject,
    mut v_b_5250_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5251_: *mut LeanObject = core::ptr::null_mut();
    v___x_5251_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_elabRewrite_spec__2_spec__2_spec__5___redArg(v_m_5248_, v_a_5249_, v_b_5250_);
    return v___x_5251_;
}
pub unsafe fn l_Lean_getExprMVarAssignment_x3f___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_elabRewrite_spec__2_spec__2_spec__6_spec__10(
    mut v_mvarId_5252_: *mut LeanObject,
    mut v___y_5253_: *mut LeanObject,
    mut v___y_5254_: *mut LeanObject,
    mut v___y_5255_: *mut LeanObject,
    mut v___y_5256_: *mut LeanObject,
    mut v___y_5257_: *mut LeanObject,
    mut v___y_5258_: *mut LeanObject,
    mut v___y_5259_: *mut LeanObject,
    mut v___y_5260_: *mut LeanObject,
    mut v___y_5261_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5263_: *mut LeanObject = core::ptr::null_mut();
    v___x_5263_ = l_Lean_getExprMVarAssignment_x3f___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_elabRewrite_spec__2_spec__2_spec__6_spec__10___redArg(v_mvarId_5252_, v___y_5253_, v___y_5259_);
    return v___x_5263_;
}
pub unsafe fn l_Lean_getExprMVarAssignment_x3f___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_elabRewrite_spec__2_spec__2_spec__6_spec__10___boxed(
    mut v_mvarId_5264_: *mut LeanObject,
    mut v___y_5265_: *mut LeanObject,
    mut v___y_5266_: *mut LeanObject,
    mut v___y_5267_: *mut LeanObject,
    mut v___y_5268_: *mut LeanObject,
    mut v___y_5269_: *mut LeanObject,
    mut v___y_5270_: *mut LeanObject,
    mut v___y_5271_: *mut LeanObject,
    mut v___y_5272_: *mut LeanObject,
    mut v___y_5273_: *mut LeanObject,
    mut v___y_5274_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5275_: *mut LeanObject = core::ptr::null_mut();
    v_res_5275_ = l_Lean_getExprMVarAssignment_x3f___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_elabRewrite_spec__2_spec__2_spec__6_spec__10(v_mvarId_5264_, v___y_5265_, v___y_5266_, v___y_5267_, v___y_5268_, v___y_5269_, v___y_5270_, v___y_5271_, v___y_5272_, v___y_5273_);
    lean_dec(v___y_5273_);
    lean_dec_ref(v___y_5272_);
    lean_dec(v___y_5271_);
    lean_dec_ref(v___y_5270_);
    lean_dec(v___y_5269_);
    lean_dec_ref(v___y_5268_);
    lean_dec(v___y_5267_);
    lean_dec_ref(v___y_5266_);
    lean_dec(v_mvarId_5264_);
    return v_res_5275_;
}
pub unsafe fn l_Lean_getDelayedMVarAssignment_x3f___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_elabRewrite_spec__2_spec__2_spec__6_spec__11(
    mut v_mvarId_5276_: *mut LeanObject,
    mut v___y_5277_: *mut LeanObject,
    mut v___y_5278_: *mut LeanObject,
    mut v___y_5279_: *mut LeanObject,
    mut v___y_5280_: *mut LeanObject,
    mut v___y_5281_: *mut LeanObject,
    mut v___y_5282_: *mut LeanObject,
    mut v___y_5283_: *mut LeanObject,
    mut v___y_5284_: *mut LeanObject,
    mut v___y_5285_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5287_: *mut LeanObject = core::ptr::null_mut();
    v___x_5287_ = l_Lean_getDelayedMVarAssignment_x3f___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_elabRewrite_spec__2_spec__2_spec__6_spec__11___redArg(v_mvarId_5276_, v___y_5277_, v___y_5283_);
    return v___x_5287_;
}
pub unsafe fn l_Lean_getDelayedMVarAssignment_x3f___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_elabRewrite_spec__2_spec__2_spec__6_spec__11___boxed(
    mut v_mvarId_5288_: *mut LeanObject,
    mut v___y_5289_: *mut LeanObject,
    mut v___y_5290_: *mut LeanObject,
    mut v___y_5291_: *mut LeanObject,
    mut v___y_5292_: *mut LeanObject,
    mut v___y_5293_: *mut LeanObject,
    mut v___y_5294_: *mut LeanObject,
    mut v___y_5295_: *mut LeanObject,
    mut v___y_5296_: *mut LeanObject,
    mut v___y_5297_: *mut LeanObject,
    mut v___y_5298_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5299_: *mut LeanObject = core::ptr::null_mut();
    v_res_5299_ = l_Lean_getDelayedMVarAssignment_x3f___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_elabRewrite_spec__2_spec__2_spec__6_spec__11(v_mvarId_5288_, v___y_5289_, v___y_5290_, v___y_5291_, v___y_5292_, v___y_5293_, v___y_5294_, v___y_5295_, v___y_5296_, v___y_5297_);
    lean_dec(v___y_5297_);
    lean_dec_ref(v___y_5296_);
    lean_dec(v___y_5295_);
    lean_dec_ref(v___y_5294_);
    lean_dec(v___y_5293_);
    lean_dec_ref(v___y_5292_);
    lean_dec(v___y_5291_);
    lean_dec_ref(v___y_5290_);
    lean_dec(v_mvarId_5288_);
    return v_res_5299_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_elabRewrite_spec__2_spec__2_spec__4_spec__6(
    mut v_00_u03b2_5300_: *mut LeanObject,
    mut v_a_5301_: *mut LeanObject,
    mut v_x_5302_: *mut LeanObject,
) -> u8 {
    let mut v___x_5303_: u8 = 0;
    v___x_5303_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_elabRewrite_spec__2_spec__2_spec__4_spec__6___redArg(v_a_5301_, v_x_5302_);
    return v___x_5303_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_elabRewrite_spec__2_spec__2_spec__4_spec__6___boxed(
    mut v_00_u03b2_5304_: *mut LeanObject,
    mut v_a_5305_: *mut LeanObject,
    mut v_x_5306_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5307_: u8 = 0;
    let mut v_r_5308_: *mut LeanObject = core::ptr::null_mut();
    v_res_5307_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_elabRewrite_spec__2_spec__2_spec__4_spec__6(v_00_u03b2_5304_, v_a_5305_, v_x_5306_);
    lean_dec(v_x_5306_);
    lean_dec_ref(v_a_5305_);
    v_r_5308_ = lean_box((v_res_5307_) as usize);
    return v_r_5308_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_elabRewrite_spec__2_spec__2_spec__5_spec__8(
    mut v_00_u03b2_5309_: *mut LeanObject,
    mut v_data_5310_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5311_: *mut LeanObject = core::ptr::null_mut();
    v___x_5311_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_elabRewrite_spec__2_spec__2_spec__5_spec__8___redArg(v_data_5310_);
    return v___x_5311_;
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_elabRewrite_spec__2_spec__2_spec__5_spec__8_spec__11(
    mut v_00_u03b2_5312_: *mut LeanObject,
    mut v_i_5313_: *mut LeanObject,
    mut v_source_5314_: *mut LeanObject,
    mut v_target_5315_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5316_: *mut LeanObject = core::ptr::null_mut();
    v___x_5316_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_elabRewrite_spec__2_spec__2_spec__5_spec__8_spec__11___redArg(v_i_5313_, v_source_5314_, v_target_5315_);
    return v___x_5316_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_elabRewrite_spec__2_spec__2_spec__5_spec__8_spec__11_spec__15(
    mut v_00_u03b2_5317_: *mut LeanObject,
    mut v_x_5318_: *mut LeanObject,
    mut v_x_5319_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5320_: *mut LeanObject = core::ptr::null_mut();
    v___x_5320_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00Lean_Elab_Tactic_elabRewrite_spec__2_spec__2_spec__5_spec__8_spec__11_spec__15___redArg(v_x_5318_, v_x_5319_);
    return v___x_5320_;
}
pub unsafe fn l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_finishElabRewrite_spec__1___redArg(
    mut v_mvarId_5321_: *mut LeanObject,
    mut v_x_5322_: *mut LeanObject,
    mut v___y_5323_: *mut LeanObject,
    mut v___y_5324_: *mut LeanObject,
    mut v___y_5325_: *mut LeanObject,
    mut v___y_5326_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5328_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5329_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5331_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5332_: u8 = 0;
    let mut v___x_5334_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5335_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5336_: u8 = 0;
    let mut v_a_5337_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5339_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5340_: u8 = 0;
    let mut v___x_5342_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5343_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5344_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5328_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(
                    lean_box(0),
                    v_mvarId_5321_,
                    v_x_5322_,
                    v___y_5323_,
                    v___y_5324_,
                    v___y_5325_,
                    v___y_5326_,
                );
                if lean_obj_tag(v___x_5328_) == 0 {
                    v_a_5329_ = lean_ctor_get(v___x_5328_, 0);
                    v_isSharedCheck_5336_ = (!lean_is_exclusive(v___x_5328_)) as u8;
                    if v_isSharedCheck_5336_ == 0 {
                        v___x_5331_ = v___x_5328_;
                        v_isShared_5332_ = v_isSharedCheck_5336_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_5329_);
                        lean_dec(v___x_5328_);
                        v___x_5331_ = lean_box(0);
                        v_isShared_5332_ = v_isSharedCheck_5336_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_5337_ = lean_ctor_get(v___x_5328_, 0);
                    v_isSharedCheck_5344_ = (!lean_is_exclusive(v___x_5328_)) as u8;
                    if v_isSharedCheck_5344_ == 0 {
                        v___x_5339_ = v___x_5328_;
                        v_isShared_5340_ = v_isSharedCheck_5344_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_5337_);
                        lean_dec(v___x_5328_);
                        v___x_5339_ = lean_box(0);
                        v_isShared_5340_ = v_isSharedCheck_5344_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_5332_ == 0 {
                    v___x_5334_ = v___x_5331_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5335_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5335_, 0, v_a_5329_);
                    v___x_5334_ = v_reuseFailAlloc_5335_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_5334_;
            }
            3 => {
                if v_isShared_5340_ == 0 {
                    v___x_5342_ = v___x_5339_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_5343_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5343_, 0, v_a_5337_);
                    v___x_5342_ = v_reuseFailAlloc_5343_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_5342_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_finishElabRewrite_spec__1___redArg___boxed(
    mut v_mvarId_5345_: *mut LeanObject,
    mut v_x_5346_: *mut LeanObject,
    mut v___y_5347_: *mut LeanObject,
    mut v___y_5348_: *mut LeanObject,
    mut v___y_5349_: *mut LeanObject,
    mut v___y_5350_: *mut LeanObject,
    mut v___y_5351_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5352_: *mut LeanObject = core::ptr::null_mut();
    v_res_5352_ =
        l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_finishElabRewrite_spec__1___redArg(
            v_mvarId_5345_,
            v_x_5346_,
            v___y_5347_,
            v___y_5348_,
            v___y_5349_,
            v___y_5350_,
        );
    lean_dec(v___y_5350_);
    lean_dec_ref(v___y_5349_);
    lean_dec(v___y_5348_);
    lean_dec_ref(v___y_5347_);
    return v_res_5352_;
}
pub unsafe fn l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_finishElabRewrite_spec__1(
    mut v_00_u03b1_5353_: *mut LeanObject,
    mut v_mvarId_5354_: *mut LeanObject,
    mut v_x_5355_: *mut LeanObject,
    mut v___y_5356_: *mut LeanObject,
    mut v___y_5357_: *mut LeanObject,
    mut v___y_5358_: *mut LeanObject,
    mut v___y_5359_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5361_: *mut LeanObject = core::ptr::null_mut();
    v___x_5361_ =
        l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_finishElabRewrite_spec__1___redArg(
            v_mvarId_5354_,
            v_x_5355_,
            v___y_5356_,
            v___y_5357_,
            v___y_5358_,
            v___y_5359_,
        );
    return v___x_5361_;
}
pub unsafe fn l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_finishElabRewrite_spec__1___boxed(
    mut v_00_u03b1_5362_: *mut LeanObject,
    mut v_mvarId_5363_: *mut LeanObject,
    mut v_x_5364_: *mut LeanObject,
    mut v___y_5365_: *mut LeanObject,
    mut v___y_5366_: *mut LeanObject,
    mut v___y_5367_: *mut LeanObject,
    mut v___y_5368_: *mut LeanObject,
    mut v___y_5369_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5370_: *mut LeanObject = core::ptr::null_mut();
    v_res_5370_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_finishElabRewrite_spec__1(
        v_00_u03b1_5362_,
        v_mvarId_5363_,
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
    return v_res_5370_;
}
pub unsafe fn l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_finishElabRewrite_spec__0_spec__0_spec__2_spec__5___redArg(
    mut v_keys_5371_: *mut LeanObject,
    mut v_i_5372_: *mut LeanObject,
    mut v_k_5373_: *mut LeanObject,
) -> u8 {
    let mut v___x_5374_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5375_: u8 = 0;
    let mut v_k_x27_5376_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5377_: u8 = 0;
    let mut v___x_5378_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5379_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5374_ = lean_array_get_size(v_keys_5371_);
                v___x_5375_ = lean_nat_dec_lt(v_i_5372_, v___x_5374_);
                if v___x_5375_ == 0 {
                    lean_dec(v_i_5372_);
                    return v___x_5375_;
                } else {
                    v_k_x27_5376_ = lean_array_fget_borrowed(v_keys_5371_, v_i_5372_);
                    v___x_5377_ = l_Lean_instBEqMVarId_beq(v_k_5373_, v_k_x27_5376_);
                    if v___x_5377_ == 0 {
                        v___x_5378_ = lean_unsigned_to_nat(1);
                        v___x_5379_ = lean_nat_add(v_i_5372_, v___x_5378_);
                        lean_dec(v_i_5372_);
                        v_i_5372_ = v___x_5379_;
                        state = 0;
                        continue;
                    } else {
                        lean_dec(v_i_5372_);
                        return v___x_5377_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_finishElabRewrite_spec__0_spec__0_spec__2_spec__5___redArg___boxed(
    mut v_keys_5381_: *mut LeanObject,
    mut v_i_5382_: *mut LeanObject,
    mut v_k_5383_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5384_: u8 = 0;
    let mut v_r_5385_: *mut LeanObject = core::ptr::null_mut();
    v_res_5384_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_finishElabRewrite_spec__0_spec__0_spec__2_spec__5___redArg(v_keys_5381_, v_i_5382_, v_k_5383_);
    lean_dec(v_k_5383_);
    lean_dec_ref(v_keys_5381_);
    v_r_5385_ = lean_box((v_res_5384_) as usize);
    return v_r_5385_;
}
pub unsafe fn _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_finishElabRewrite_spec__0_spec__0_spec__2___redArg___closed__0()
-> usize {
    let mut v___x_5386_: usize = 0;
    let mut v___x_5387_: usize = 0;
    let mut v___x_5388_: usize = 0;
    v___x_5386_ = 5usize;
    v___x_5387_ = 1usize;
    v___x_5388_ = lean_usize_shift_left(v___x_5387_, v___x_5386_);
    return v___x_5388_;
}
pub unsafe fn _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_finishElabRewrite_spec__0_spec__0_spec__2___redArg___closed__1()
-> usize {
    let mut v___x_5389_: usize = 0;
    let mut v___x_5390_: usize = 0;
    let mut v___x_5391_: usize = 0;
    v___x_5389_ = 1usize;
    v___x_5390_ = lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_finishElabRewrite_spec__0_spec__0_spec__2___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_finishElabRewrite_spec__0_spec__0_spec__2___redArg___closed__0_once), _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_finishElabRewrite_spec__0_spec__0_spec__2___redArg___closed__0);
    v___x_5391_ = lean_usize_sub(v___x_5390_, v___x_5389_);
    return v___x_5391_;
}
pub unsafe fn l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_finishElabRewrite_spec__0_spec__0_spec__2___redArg(
    mut v_x_5392_: *mut LeanObject,
    mut v_x_5393_: usize,
    mut v_x_5394_: *mut LeanObject,
) -> u8 {
    let mut v_es_5395_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5396_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5397_: usize = 0;
    let mut v___x_5398_: usize = 0;
    let mut v___x_5399_: usize = 0;
    let mut v_j_5400_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5401_: *mut LeanObject = core::ptr::null_mut();
    let mut v_key_5402_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5403_: u8 = 0;
    let mut v_node_5404_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5405_: usize = 0;
    let mut v___x_5407_: u8 = 0;
    let mut v_ks_5408_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5409_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5410_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_5392_) == 0 {
                    v_es_5395_ = lean_ctor_get(v_x_5392_, 0);
                    v___x_5396_ = lean_box(2);
                    v___x_5397_ = 5usize;
                    v___x_5398_ = lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_finishElabRewrite_spec__0_spec__0_spec__2___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_finishElabRewrite_spec__0_spec__0_spec__2___redArg___closed__1_once), _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_finishElabRewrite_spec__0_spec__0_spec__2___redArg___closed__1);
                    v___x_5399_ = lean_usize_land(v_x_5393_, v___x_5398_);
                    v_j_5400_ = lean_usize_to_nat(v___x_5399_);
                    v___x_5401_ = lean_array_get_borrowed(v___x_5396_, v_es_5395_, v_j_5400_);
                    lean_dec(v_j_5400_);
                    match lean_obj_tag(v___x_5401_) {
                        0 => {
                            v_key_5402_ = lean_ctor_get(v___x_5401_, 0);
                            v___x_5403_ = l_Lean_instBEqMVarId_beq(v_x_5394_, v_key_5402_);
                            return v___x_5403_;
                        }
                        1 => {
                            v_node_5404_ = lean_ctor_get(v___x_5401_, 0);
                            v___x_5405_ = lean_usize_shift_right(v_x_5393_, v___x_5397_);
                            v_x_5392_ = v_node_5404_;
                            v_x_5393_ = v___x_5405_;
                            state = 0;
                            continue;
                        }
                        _ => {
                            v___x_5407_ = 0;
                            return v___x_5407_;
                        }
                    }
                } else {
                    v_ks_5408_ = lean_ctor_get(v_x_5392_, 0);
                    v___x_5409_ = lean_unsigned_to_nat(0);
                    v___x_5410_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_finishElabRewrite_spec__0_spec__0_spec__2_spec__5___redArg(v_ks_5408_, v___x_5409_, v_x_5394_);
                    return v___x_5410_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_finishElabRewrite_spec__0_spec__0_spec__2___redArg___boxed(
    mut v_x_5411_: *mut LeanObject,
    mut v_x_5412_: *mut LeanObject,
    mut v_x_5413_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_x_1972__boxed_5414_: usize = 0;
    let mut v_res_5415_: u8 = 0;
    let mut v_r_5416_: *mut LeanObject = core::ptr::null_mut();
    v_x_1972__boxed_5414_ = lean_unbox_usize(v_x_5412_);
    lean_dec(v_x_5412_);
    v_res_5415_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_finishElabRewrite_spec__0_spec__0_spec__2___redArg(v_x_5411_, v_x_1972__boxed_5414_, v_x_5413_);
    lean_dec(v_x_5413_);
    lean_dec_ref(v_x_5411_);
    v_r_5416_ = lean_box((v_res_5415_) as usize);
    return v_r_5416_;
}
pub unsafe fn l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_finishElabRewrite_spec__0_spec__0___redArg(
    mut v_x_5417_: *mut LeanObject,
    mut v_x_5418_: *mut LeanObject,
) -> u8 {
    let mut v___x_5419_: u64 = 0;
    let mut v___x_5420_: usize = 0;
    let mut v___x_5421_: u8 = 0;
    v___x_5419_ = l_Lean_instHashableMVarId_hash(v_x_5418_);
    v___x_5420_ = lean_uint64_to_usize(v___x_5419_);
    v___x_5421_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_finishElabRewrite_spec__0_spec__0_spec__2___redArg(v_x_5417_, v___x_5420_, v_x_5418_);
    return v___x_5421_;
}
pub unsafe fn l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_finishElabRewrite_spec__0_spec__0___redArg___boxed(
    mut v_x_5422_: *mut LeanObject,
    mut v_x_5423_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5424_: u8 = 0;
    let mut v_r_5425_: *mut LeanObject = core::ptr::null_mut();
    v_res_5424_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_finishElabRewrite_spec__0_spec__0___redArg(v_x_5422_, v_x_5423_);
    lean_dec(v_x_5423_);
    lean_dec_ref(v_x_5422_);
    v_r_5425_ = lean_box((v_res_5424_) as usize);
    return v_r_5425_;
}
pub unsafe fn l_Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_finishElabRewrite_spec__0___redArg(
    mut v_mvarId_5426_: *mut LeanObject,
    mut v___y_5427_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5429_: *mut LeanObject = core::ptr::null_mut();
    let mut v_mctx_5430_: *mut LeanObject = core::ptr::null_mut();
    let mut v_eAssignment_5431_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5432_: u8 = 0;
    let mut v___x_5433_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5434_: *mut LeanObject = core::ptr::null_mut();
    v___x_5429_ = lean_st_ref_get(v___y_5427_);
    v_mctx_5430_ = lean_ctor_get(v___x_5429_, 0);
    lean_inc_ref(v_mctx_5430_);
    lean_dec(v___x_5429_);
    v_eAssignment_5431_ = lean_ctor_get(v_mctx_5430_, 8);
    lean_inc_ref(v_eAssignment_5431_);
    lean_dec_ref(v_mctx_5430_);
    v___x_5432_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_finishElabRewrite_spec__0_spec__0___redArg(v_eAssignment_5431_, v_mvarId_5426_);
    lean_dec_ref(v_eAssignment_5431_);
    v___x_5433_ = lean_box((v___x_5432_) as usize);
    v___x_5434_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_5434_, 0, v___x_5433_);
    return v___x_5434_;
}
pub unsafe fn l_Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_finishElabRewrite_spec__0___redArg___boxed(
    mut v_mvarId_5435_: *mut LeanObject,
    mut v___y_5436_: *mut LeanObject,
    mut v___y_5437_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5438_: *mut LeanObject = core::ptr::null_mut();
    v_res_5438_ =
        l_Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_finishElabRewrite_spec__0___redArg(
            v_mvarId_5435_,
            v___y_5436_,
        );
    lean_dec(v___y_5436_);
    lean_dec(v_mvarId_5435_);
    return v_res_5438_;
}
pub unsafe fn l_List_filterAuxM___at___00Lean_Elab_Tactic_finishElabRewrite_spec__3(
    mut v_x_5439_: *mut LeanObject,
    mut v_x_5440_: *mut LeanObject,
    mut v___y_5441_: *mut LeanObject,
    mut v___y_5442_: *mut LeanObject,
    mut v___y_5443_: *mut LeanObject,
    mut v___y_5444_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5446_: *mut LeanObject = core::ptr::null_mut();
    let mut v_head_5447_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_5448_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5450_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5451_: u8 = 0;
    let mut v___x_5454_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5456_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5457_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5458_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5459_: u8 = 0;
    let mut v_isSharedCheck_5461_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_5439_) == 0 {
                    v___x_5446_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_5446_, 0, v_x_5440_);
                    return v___x_5446_;
                } else {
                    v_head_5447_ = lean_ctor_get(v_x_5439_, 0);
                    v_tail_5448_ = lean_ctor_get(v_x_5439_, 1);
                    v_isSharedCheck_5461_ = (!lean_is_exclusive(v_x_5439_)) as u8;
                    if v_isSharedCheck_5461_ == 0 {
                        v___x_5450_ = v_x_5439_;
                        v_isShared_5451_ = v_isSharedCheck_5461_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_tail_5448_);
                        lean_inc(v_head_5447_);
                        lean_dec(v_x_5439_);
                        v___x_5450_ = lean_box(0);
                        v_isShared_5451_ = v_isSharedCheck_5461_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_5457_ = l_Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_finishElabRewrite_spec__0___redArg(v_head_5447_, v___y_5442_);
                v_a_5458_ = lean_ctor_get(v___x_5457_, 0);
                lean_inc(v_a_5458_);
                lean_dec_ref(v___x_5457_);
                v___x_5459_ = (lean_unbox(v_a_5458_) as u8);
                lean_dec(v_a_5458_);
                if v___x_5459_ == 0 {
                    state = 2;
                    continue;
                } else {
                    lean_del_object(v___x_5450_);
                    lean_dec(v_head_5447_);
                    v_x_5439_ = v_tail_5448_;
                    state = 0;
                    continue;
                }
            }
            2 => {
                if v_isShared_5451_ == 0 {
                    lean_ctor_set(v___x_5450_, 1, v_x_5440_);
                    v___x_5454_ = v___x_5450_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_5456_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5456_, 0, v_head_5447_);
                    lean_ctor_set(v_reuseFailAlloc_5456_, 1, v_x_5440_);
                    v___x_5454_ = v_reuseFailAlloc_5456_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v_x_5439_ = v_tail_5448_;
                v_x_5440_ = v___x_5454_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_filterAuxM___at___00Lean_Elab_Tactic_finishElabRewrite_spec__3___boxed(
    mut v_x_5462_: *mut LeanObject,
    mut v_x_5463_: *mut LeanObject,
    mut v___y_5464_: *mut LeanObject,
    mut v___y_5465_: *mut LeanObject,
    mut v___y_5466_: *mut LeanObject,
    mut v___y_5467_: *mut LeanObject,
    mut v___y_5468_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5469_: *mut LeanObject = core::ptr::null_mut();
    v_res_5469_ = l_List_filterAuxM___at___00Lean_Elab_Tactic_finishElabRewrite_spec__3(
        v_x_5462_,
        v_x_5463_,
        v___y_5464_,
        v___y_5465_,
        v___y_5466_,
        v___y_5467_,
    );
    lean_dec(v___y_5467_);
    lean_dec_ref(v___y_5466_);
    lean_dec(v___y_5465_);
    lean_dec_ref(v___y_5464_);
    return v_res_5469_;
}
pub unsafe fn l_List_forM___at___00Lean_Elab_Tactic_finishElabRewrite_spec__2___lam__0(
    mut v_head_5470_: *mut LeanObject,
    mut v___y_5471_: *mut LeanObject,
    mut v___y_5472_: *mut LeanObject,
    mut v___y_5473_: *mut LeanObject,
    mut v___y_5474_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5476_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5477_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5478_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5479_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5481_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5482_: u8 = 0;
    let mut v___x_5483_: u8 = 0;
    let mut v___x_5484_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5486_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5487_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5488_: u8 = 0;
    let mut v___x_5489_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5490_: u8 = 0;
    let mut v_a_5491_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5493_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5494_: u8 = 0;
    let mut v___x_5496_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5497_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5498_: u8 = 0;
    let mut v_a_5499_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5501_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5502_: u8 = 0;
    let mut v___x_5504_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5505_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5506_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                lean_inc(v_head_5470_);
                v___x_5476_ = l_Lean_MVarId_getType(
                    v_head_5470_,
                    v___y_5471_,
                    v___y_5472_,
                    v___y_5473_,
                    v___y_5474_,
                );
                if lean_obj_tag(v___x_5476_) == 0 {
                    v_a_5477_ = lean_ctor_get(v___x_5476_, 0);
                    lean_inc(v_a_5477_);
                    lean_dec_ref_known(v___x_5476_, 1);
                    v___x_5478_ = l_Lean_Meta_isProp(
                        v_a_5477_,
                        v___y_5471_,
                        v___y_5472_,
                        v___y_5473_,
                        v___y_5474_,
                    );
                    if lean_obj_tag(v___x_5478_) == 0 {
                        v_a_5479_ = lean_ctor_get(v___x_5478_, 0);
                        v_isSharedCheck_5490_ = (!lean_is_exclusive(v___x_5478_)) as u8;
                        if v_isSharedCheck_5490_ == 0 {
                            v___x_5481_ = v___x_5478_;
                            v_isShared_5482_ = v_isSharedCheck_5490_;
                            state = 1;
                            continue;
                        } else {
                            lean_inc(v_a_5479_);
                            lean_dec(v___x_5478_);
                            v___x_5481_ = lean_box(0);
                            v_isShared_5482_ = v_isSharedCheck_5490_;
                            state = 1;
                            continue;
                        }
                    } else {
                        lean_dec(v_head_5470_);
                        v_a_5491_ = lean_ctor_get(v___x_5478_, 0);
                        v_isSharedCheck_5498_ = (!lean_is_exclusive(v___x_5478_)) as u8;
                        if v_isSharedCheck_5498_ == 0 {
                            v___x_5493_ = v___x_5478_;
                            v_isShared_5494_ = v_isSharedCheck_5498_;
                            state = 3;
                            continue;
                        } else {
                            lean_inc(v_a_5491_);
                            lean_dec(v___x_5478_);
                            v___x_5493_ = lean_box(0);
                            v_isShared_5494_ = v_isSharedCheck_5498_;
                            state = 3;
                            continue;
                        }
                    }
                } else {
                    lean_dec(v_head_5470_);
                    v_a_5499_ = lean_ctor_get(v___x_5476_, 0);
                    v_isSharedCheck_5506_ = (!lean_is_exclusive(v___x_5476_)) as u8;
                    if v_isSharedCheck_5506_ == 0 {
                        v___x_5501_ = v___x_5476_;
                        v_isShared_5502_ = v_isSharedCheck_5506_;
                        state = 5;
                        continue;
                    } else {
                        lean_inc(v_a_5499_);
                        lean_dec(v___x_5476_);
                        v___x_5501_ = lean_box(0);
                        v_isShared_5502_ = v_isSharedCheck_5506_;
                        state = 5;
                        continue;
                    }
                }
            }
            1 => {
                v___x_5483_ = (lean_unbox(v_a_5479_) as u8);
                lean_dec(v_a_5479_);
                if v___x_5483_ == 0 {
                    lean_dec(v_head_5470_);
                    v___x_5484_ = lean_box(0);
                    if v_isShared_5482_ == 0 {
                        lean_ctor_set(v___x_5481_, 0, v___x_5484_);
                        v___x_5486_ = v___x_5481_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_5487_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_5487_, 0, v___x_5484_);
                        v___x_5486_ = v_reuseFailAlloc_5487_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_5481_);
                    v___x_5488_ = 2;
                    v___x_5489_ =
                        l_Lean_MVarId_setKind___redArg(v_head_5470_, v___x_5488_, v___y_5472_);
                    return v___x_5489_;
                }
            }
            2 => {
                return v___x_5486_;
            }
            3 => {
                if v_isShared_5494_ == 0 {
                    v___x_5496_ = v___x_5493_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_5497_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5497_, 0, v_a_5491_);
                    v___x_5496_ = v_reuseFailAlloc_5497_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_5496_;
            }
            5 => {
                if v_isShared_5502_ == 0 {
                    v___x_5504_ = v___x_5501_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_5505_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5505_, 0, v_a_5499_);
                    v___x_5504_ = v_reuseFailAlloc_5505_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_5504_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_forM___at___00Lean_Elab_Tactic_finishElabRewrite_spec__2___lam__0___boxed(
    mut v_head_5507_: *mut LeanObject,
    mut v___y_5508_: *mut LeanObject,
    mut v___y_5509_: *mut LeanObject,
    mut v___y_5510_: *mut LeanObject,
    mut v___y_5511_: *mut LeanObject,
    mut v___y_5512_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5513_: *mut LeanObject = core::ptr::null_mut();
    v_res_5513_ = l_List_forM___at___00Lean_Elab_Tactic_finishElabRewrite_spec__2___lam__0(
        v_head_5507_,
        v___y_5508_,
        v___y_5509_,
        v___y_5510_,
        v___y_5511_,
    );
    lean_dec(v___y_5511_);
    lean_dec_ref(v___y_5510_);
    lean_dec(v___y_5509_);
    lean_dec_ref(v___y_5508_);
    return v_res_5513_;
}
pub unsafe fn l_List_forM___at___00Lean_Elab_Tactic_finishElabRewrite_spec__2(
    mut v_as_5514_: *mut LeanObject,
    mut v___y_5515_: *mut LeanObject,
    mut v___y_5516_: *mut LeanObject,
    mut v___y_5517_: *mut LeanObject,
    mut v___y_5518_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5520_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5521_: *mut LeanObject = core::ptr::null_mut();
    let mut v_head_5522_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_5523_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_5524_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5525_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_as_5514_) == 0 {
                    v___x_5520_ = lean_box(0);
                    v___x_5521_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_5521_, 0, v___x_5520_);
                    return v___x_5521_;
                } else {
                    v_head_5522_ = lean_ctor_get(v_as_5514_, 0);
                    lean_inc_n(v_head_5522_, 2);
                    v_tail_5523_ = lean_ctor_get(v_as_5514_, 1);
                    lean_inc(v_tail_5523_);
                    lean_dec_ref_known(v_as_5514_, 2);
                    v___f_5524_ = lean_alloc_closure(l_List_forM___at___00Lean_Elab_Tactic_finishElabRewrite_spec__2___lam__0___boxed as *mut core::ffi::c_void, 6, 1);
                    lean_closure_set(v___f_5524_, 0, v_head_5522_);
                    v___x_5525_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_finishElabRewrite_spec__1___redArg(v_head_5522_, v___f_5524_, v___y_5515_, v___y_5516_, v___y_5517_, v___y_5518_);
                    if lean_obj_tag(v___x_5525_) == 0 {
                        lean_dec_ref_known(v___x_5525_, 1);
                        v_as_5514_ = v_tail_5523_;
                        state = 0;
                        continue;
                    } else {
                        lean_dec(v_tail_5523_);
                        return v___x_5525_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_forM___at___00Lean_Elab_Tactic_finishElabRewrite_spec__2___boxed(
    mut v_as_5527_: *mut LeanObject,
    mut v___y_5528_: *mut LeanObject,
    mut v___y_5529_: *mut LeanObject,
    mut v___y_5530_: *mut LeanObject,
    mut v___y_5531_: *mut LeanObject,
    mut v___y_5532_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5533_: *mut LeanObject = core::ptr::null_mut();
    v_res_5533_ = l_List_forM___at___00Lean_Elab_Tactic_finishElabRewrite_spec__2(
        v_as_5527_,
        v___y_5528_,
        v___y_5529_,
        v___y_5530_,
        v___y_5531_,
    );
    lean_dec(v___y_5531_);
    lean_dec_ref(v___y_5530_);
    lean_dec(v___y_5529_);
    lean_dec_ref(v___y_5528_);
    return v_res_5533_;
}
pub unsafe fn l_Lean_Elab_Tactic_finishElabRewrite(
    mut v_r_5534_: *mut LeanObject,
    mut v_a_5535_: *mut LeanObject,
    mut v_a_5536_: *mut LeanObject,
    mut v_a_5537_: *mut LeanObject,
    mut v_a_5538_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_eNew_5540_: *mut LeanObject = core::ptr::null_mut();
    let mut v_eqProof_5541_: *mut LeanObject = core::ptr::null_mut();
    let mut v_mvarIds_5542_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5544_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5545_: u8 = 0;
    let mut v_a_5547_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5548_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5550_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5551_: u8 = 0;
    let mut v___x_5553_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5555_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5556_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5557_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5558_: u8 = 0;
    let mut v_unused_5559_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5560_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5562_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5563_: u8 = 0;
    let mut v___x_5565_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5566_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5567_: u8 = 0;
    let mut v___x_5568_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5569_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5570_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5571_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5572_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5573_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5575_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5576_: u8 = 0;
    let mut v___x_5578_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5579_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5580_: u8 = 0;
    let mut v_isSharedCheck_5581_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_eNew_5540_ = lean_ctor_get(v_r_5534_, 0);
                v_eqProof_5541_ = lean_ctor_get(v_r_5534_, 1);
                v_mvarIds_5542_ = lean_ctor_get(v_r_5534_, 2);
                v_isSharedCheck_5581_ = (!lean_is_exclusive(v_r_5534_)) as u8;
                if v_isSharedCheck_5581_ == 0 {
                    v___x_5544_ = v_r_5534_;
                    v_isShared_5545_ = v_isSharedCheck_5581_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_mvarIds_5542_);
                    lean_inc(v_eqProof_5541_);
                    lean_inc(v_eNew_5540_);
                    lean_dec(v_r_5534_);
                    v___x_5544_ = lean_box(0);
                    v_isShared_5545_ = v_isSharedCheck_5581_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_5568_ = lean_box(0);
                v___x_5569_ = l_List_filterAuxM___at___00Lean_Elab_Tactic_finishElabRewrite_spec__3(
                    v_mvarIds_5542_,
                    v___x_5568_,
                    v_a_5535_,
                    v_a_5536_,
                    v_a_5537_,
                    v_a_5538_,
                );
                if lean_obj_tag(v___x_5569_) == 0 {
                    v_a_5570_ = lean_ctor_get(v___x_5569_, 0);
                    lean_inc(v_a_5570_);
                    lean_dec_ref_known(v___x_5569_, 1);
                    v___x_5571_ = l_List_reverse___redArg(v_a_5570_);
                    v_a_5547_ = v___x_5571_;
                    state = 2;
                    continue;
                } else {
                    if lean_obj_tag(v___x_5569_) == 0 {
                        v_a_5572_ = lean_ctor_get(v___x_5569_, 0);
                        lean_inc(v_a_5572_);
                        lean_dec_ref_known(v___x_5569_, 1);
                        v_a_5547_ = v_a_5572_;
                        state = 2;
                        continue;
                    } else {
                        lean_del_object(v___x_5544_);
                        lean_dec_ref(v_eqProof_5541_);
                        lean_dec_ref(v_eNew_5540_);
                        v_a_5573_ = lean_ctor_get(v___x_5569_, 0);
                        v_isSharedCheck_5580_ = (!lean_is_exclusive(v___x_5569_)) as u8;
                        if v_isSharedCheck_5580_ == 0 {
                            v___x_5575_ = v___x_5569_;
                            v_isShared_5576_ = v_isSharedCheck_5580_;
                            state = 8;
                            continue;
                        } else {
                            lean_inc(v_a_5573_);
                            lean_dec(v___x_5569_);
                            v___x_5575_ = lean_box(0);
                            v_isShared_5576_ = v_isSharedCheck_5580_;
                            state = 8;
                            continue;
                        }
                    }
                }
            }
            2 => {
                lean_inc(v_a_5547_);
                v___x_5548_ = l_List_forM___at___00Lean_Elab_Tactic_finishElabRewrite_spec__2(
                    v_a_5547_, v_a_5535_, v_a_5536_, v_a_5537_, v_a_5538_,
                );
                if lean_obj_tag(v___x_5548_) == 0 {
                    v_isSharedCheck_5558_ = (!lean_is_exclusive(v___x_5548_)) as u8;
                    if v_isSharedCheck_5558_ == 0 {
                        v_unused_5559_ = lean_ctor_get(v___x_5548_, 0);
                        lean_dec(v_unused_5559_);
                        v___x_5550_ = v___x_5548_;
                        v_isShared_5551_ = v_isSharedCheck_5558_;
                        state = 3;
                        continue;
                    } else {
                        lean_dec(v___x_5548_);
                        v___x_5550_ = lean_box(0);
                        v_isShared_5551_ = v_isSharedCheck_5558_;
                        state = 3;
                        continue;
                    }
                } else {
                    lean_dec(v_a_5547_);
                    lean_del_object(v___x_5544_);
                    lean_dec_ref(v_eqProof_5541_);
                    lean_dec_ref(v_eNew_5540_);
                    v_a_5560_ = lean_ctor_get(v___x_5548_, 0);
                    v_isSharedCheck_5567_ = (!lean_is_exclusive(v___x_5548_)) as u8;
                    if v_isSharedCheck_5567_ == 0 {
                        v___x_5562_ = v___x_5548_;
                        v_isShared_5563_ = v_isSharedCheck_5567_;
                        state = 6;
                        continue;
                    } else {
                        lean_inc(v_a_5560_);
                        lean_dec(v___x_5548_);
                        v___x_5562_ = lean_box(0);
                        v_isShared_5563_ = v_isSharedCheck_5567_;
                        state = 6;
                        continue;
                    }
                }
            }
            3 => {
                if v_isShared_5545_ == 0 {
                    lean_ctor_set(v___x_5544_, 2, v_a_5547_);
                    v___x_5553_ = v___x_5544_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_5557_ = lean_alloc_ctor(0, 3, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5557_, 0, v_eNew_5540_);
                    lean_ctor_set(v_reuseFailAlloc_5557_, 1, v_eqProof_5541_);
                    lean_ctor_set(v_reuseFailAlloc_5557_, 2, v_a_5547_);
                    v___x_5553_ = v_reuseFailAlloc_5557_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                if v_isShared_5551_ == 0 {
                    lean_ctor_set(v___x_5550_, 0, v___x_5553_);
                    v___x_5555_ = v___x_5550_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_5556_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5556_, 0, v___x_5553_);
                    v___x_5555_ = v_reuseFailAlloc_5556_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_5555_;
            }
            6 => {
                if v_isShared_5563_ == 0 {
                    v___x_5565_ = v___x_5562_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_5566_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5566_, 0, v_a_5560_);
                    v___x_5565_ = v_reuseFailAlloc_5566_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_5565_;
            }
            8 => {
                if v_isShared_5576_ == 0 {
                    v___x_5578_ = v___x_5575_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_5579_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5579_, 0, v_a_5573_);
                    v___x_5578_ = v_reuseFailAlloc_5579_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_5578_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_Tactic_finishElabRewrite___boxed(
    mut v_r_5582_: *mut LeanObject,
    mut v_a_5583_: *mut LeanObject,
    mut v_a_5584_: *mut LeanObject,
    mut v_a_5585_: *mut LeanObject,
    mut v_a_5586_: *mut LeanObject,
    mut v_a_5587_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5588_: *mut LeanObject = core::ptr::null_mut();
    v_res_5588_ =
        l_Lean_Elab_Tactic_finishElabRewrite(v_r_5582_, v_a_5583_, v_a_5584_, v_a_5585_, v_a_5586_);
    lean_dec(v_a_5586_);
    lean_dec_ref(v_a_5585_);
    lean_dec(v_a_5584_);
    lean_dec_ref(v_a_5583_);
    return v_res_5588_;
}
pub unsafe fn l_Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_finishElabRewrite_spec__0(
    mut v_mvarId_5589_: *mut LeanObject,
    mut v___y_5590_: *mut LeanObject,
    mut v___y_5591_: *mut LeanObject,
    mut v___y_5592_: *mut LeanObject,
    mut v___y_5593_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5595_: *mut LeanObject = core::ptr::null_mut();
    v___x_5595_ =
        l_Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_finishElabRewrite_spec__0___redArg(
            v_mvarId_5589_,
            v___y_5591_,
        );
    return v___x_5595_;
}
pub unsafe fn l_Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_finishElabRewrite_spec__0___boxed(
    mut v_mvarId_5596_: *mut LeanObject,
    mut v___y_5597_: *mut LeanObject,
    mut v___y_5598_: *mut LeanObject,
    mut v___y_5599_: *mut LeanObject,
    mut v___y_5600_: *mut LeanObject,
    mut v___y_5601_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5602_: *mut LeanObject = core::ptr::null_mut();
    v_res_5602_ = l_Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_finishElabRewrite_spec__0(
        v_mvarId_5596_,
        v___y_5597_,
        v___y_5598_,
        v___y_5599_,
        v___y_5600_,
    );
    lean_dec(v___y_5600_);
    lean_dec_ref(v___y_5599_);
    lean_dec(v___y_5598_);
    lean_dec_ref(v___y_5597_);
    lean_dec(v_mvarId_5596_);
    return v_res_5602_;
}
pub unsafe fn l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_finishElabRewrite_spec__0_spec__0(
    mut v_00_u03b2_5603_: *mut LeanObject,
    mut v_x_5604_: *mut LeanObject,
    mut v_x_5605_: *mut LeanObject,
) -> u8 {
    let mut v___x_5606_: u8 = 0;
    v___x_5606_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_finishElabRewrite_spec__0_spec__0___redArg(v_x_5604_, v_x_5605_);
    return v___x_5606_;
}
pub unsafe fn l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_finishElabRewrite_spec__0_spec__0___boxed(
    mut v_00_u03b2_5607_: *mut LeanObject,
    mut v_x_5608_: *mut LeanObject,
    mut v_x_5609_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5610_: u8 = 0;
    let mut v_r_5611_: *mut LeanObject = core::ptr::null_mut();
    v_res_5610_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_finishElabRewrite_spec__0_spec__0(v_00_u03b2_5607_, v_x_5608_, v_x_5609_);
    lean_dec(v_x_5609_);
    lean_dec_ref(v_x_5608_);
    v_r_5611_ = lean_box((v_res_5610_) as usize);
    return v_r_5611_;
}
pub unsafe fn l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_finishElabRewrite_spec__0_spec__0_spec__2(
    mut v_00_u03b2_5612_: *mut LeanObject,
    mut v_x_5613_: *mut LeanObject,
    mut v_x_5614_: usize,
    mut v_x_5615_: *mut LeanObject,
) -> u8 {
    let mut v___x_5616_: u8 = 0;
    v___x_5616_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_finishElabRewrite_spec__0_spec__0_spec__2___redArg(v_x_5613_, v_x_5614_, v_x_5615_);
    return v___x_5616_;
}
pub unsafe fn l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_finishElabRewrite_spec__0_spec__0_spec__2___boxed(
    mut v_00_u03b2_5617_: *mut LeanObject,
    mut v_x_5618_: *mut LeanObject,
    mut v_x_5619_: *mut LeanObject,
    mut v_x_5620_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_x_2317__boxed_5621_: usize = 0;
    let mut v_res_5622_: u8 = 0;
    let mut v_r_5623_: *mut LeanObject = core::ptr::null_mut();
    v_x_2317__boxed_5621_ = lean_unbox_usize(v_x_5619_);
    lean_dec(v_x_5619_);
    v_res_5622_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_finishElabRewrite_spec__0_spec__0_spec__2(v_00_u03b2_5617_, v_x_5618_, v_x_2317__boxed_5621_, v_x_5620_);
    lean_dec(v_x_5620_);
    lean_dec_ref(v_x_5618_);
    v_r_5623_ = lean_box((v_res_5622_) as usize);
    return v_r_5623_;
}
pub unsafe fn l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_finishElabRewrite_spec__0_spec__0_spec__2_spec__5(
    mut v_00_u03b2_5624_: *mut LeanObject,
    mut v_keys_5625_: *mut LeanObject,
    mut v_vals_5626_: *mut LeanObject,
    mut v_heq_5627_: *mut LeanObject,
    mut v_i_5628_: *mut LeanObject,
    mut v_k_5629_: *mut LeanObject,
) -> u8 {
    let mut v___x_5630_: u8 = 0;
    v___x_5630_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_finishElabRewrite_spec__0_spec__0_spec__2_spec__5___redArg(v_keys_5625_, v_i_5628_, v_k_5629_);
    return v___x_5630_;
}
pub unsafe fn l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_finishElabRewrite_spec__0_spec__0_spec__2_spec__5___boxed(
    mut v_00_u03b2_5631_: *mut LeanObject,
    mut v_keys_5632_: *mut LeanObject,
    mut v_vals_5633_: *mut LeanObject,
    mut v_heq_5634_: *mut LeanObject,
    mut v_i_5635_: *mut LeanObject,
    mut v_k_5636_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5637_: u8 = 0;
    let mut v_r_5638_: *mut LeanObject = core::ptr::null_mut();
    v_res_5637_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Elab_Tactic_finishElabRewrite_spec__0_spec__0_spec__2_spec__5(v_00_u03b2_5631_, v_keys_5632_, v_vals_5633_, v_heq_5634_, v_i_5635_, v_k_5636_);
    lean_dec(v_k_5636_);
    lean_dec_ref(v_vals_5633_);
    lean_dec_ref(v_keys_5632_);
    v_r_5638_ = lean_box((v_res_5637_) as usize);
    return v_r_5638_;
}
pub unsafe fn l_Lean_Elab_Tactic_rewriteTarget___lam__0(
    mut v_stx_5639_: *mut LeanObject,
    mut v_symm_5640_: u8,
    mut v_config_5641_: *mut LeanObject,
    mut v___y_5642_: *mut LeanObject,
    mut v___y_5643_: *mut LeanObject,
    mut v___y_5644_: *mut LeanObject,
    mut v___y_5645_: *mut LeanObject,
    mut v___y_5646_: *mut LeanObject,
    mut v___y_5647_: *mut LeanObject,
    mut v___y_5648_: *mut LeanObject,
    mut v___y_5649_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5651_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5652_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5653_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5654_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5655_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5656_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5658_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5659_: u8 = 0;
    let mut v___x_5661_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5662_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5663_: u8 = 0;
    let mut v_a_5664_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5666_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5667_: u8 = 0;
    let mut v___x_5669_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5670_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5671_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5651_ = l_Lean_Elab_Tactic_getMainGoal___redArg(
                    v___y_5643_,
                    v___y_5646_,
                    v___y_5647_,
                    v___y_5648_,
                    v___y_5649_,
                );
                if lean_obj_tag(v___x_5651_) == 0 {
                    v_a_5652_ = lean_ctor_get(v___x_5651_, 0);
                    lean_inc(v_a_5652_);
                    lean_dec_ref_known(v___x_5651_, 1);
                    v___x_5653_ = l_Lean_Elab_Tactic_getMainTarget(
                        v___y_5642_,
                        v___y_5643_,
                        v___y_5644_,
                        v___y_5645_,
                        v___y_5646_,
                        v___y_5647_,
                        v___y_5648_,
                        v___y_5649_,
                    );
                    if lean_obj_tag(v___x_5653_) == 0 {
                        v_a_5654_ = lean_ctor_get(v___x_5653_, 0);
                        lean_inc(v_a_5654_);
                        lean_dec_ref_known(v___x_5653_, 1);
                        v___x_5655_ = l_Lean_Elab_Tactic_elabRewrite(
                            v_a_5652_,
                            v_a_5654_,
                            v_stx_5639_,
                            v_symm_5640_,
                            v_config_5641_,
                            v___y_5642_,
                            v___y_5643_,
                            v___y_5644_,
                            v___y_5645_,
                            v___y_5646_,
                            v___y_5647_,
                            v___y_5648_,
                            v___y_5649_,
                        );
                        return v___x_5655_;
                    } else {
                        lean_dec(v_a_5652_);
                        lean_dec_ref(v_config_5641_);
                        lean_dec(v_stx_5639_);
                        v_a_5656_ = lean_ctor_get(v___x_5653_, 0);
                        v_isSharedCheck_5663_ = (!lean_is_exclusive(v___x_5653_)) as u8;
                        if v_isSharedCheck_5663_ == 0 {
                            v___x_5658_ = v___x_5653_;
                            v_isShared_5659_ = v_isSharedCheck_5663_;
                            state = 1;
                            continue;
                        } else {
                            lean_inc(v_a_5656_);
                            lean_dec(v___x_5653_);
                            v___x_5658_ = lean_box(0);
                            v_isShared_5659_ = v_isSharedCheck_5663_;
                            state = 1;
                            continue;
                        }
                    }
                } else {
                    lean_dec_ref(v_config_5641_);
                    lean_dec(v_stx_5639_);
                    v_a_5664_ = lean_ctor_get(v___x_5651_, 0);
                    v_isSharedCheck_5671_ = (!lean_is_exclusive(v___x_5651_)) as u8;
                    if v_isSharedCheck_5671_ == 0 {
                        v___x_5666_ = v___x_5651_;
                        v_isShared_5667_ = v_isSharedCheck_5671_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_5664_);
                        lean_dec(v___x_5651_);
                        v___x_5666_ = lean_box(0);
                        v_isShared_5667_ = v_isSharedCheck_5671_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_5659_ == 0 {
                    v___x_5661_ = v___x_5658_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5662_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5662_, 0, v_a_5656_);
                    v___x_5661_ = v_reuseFailAlloc_5662_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_5661_;
            }
            3 => {
                if v_isShared_5667_ == 0 {
                    v___x_5669_ = v___x_5666_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_5670_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5670_, 0, v_a_5664_);
                    v___x_5669_ = v_reuseFailAlloc_5670_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_5669_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_Tactic_rewriteTarget___lam__0___boxed(
    mut v_stx_5672_: *mut LeanObject,
    mut v_symm_5673_: *mut LeanObject,
    mut v_config_5674_: *mut LeanObject,
    mut v___y_5675_: *mut LeanObject,
    mut v___y_5676_: *mut LeanObject,
    mut v___y_5677_: *mut LeanObject,
    mut v___y_5678_: *mut LeanObject,
    mut v___y_5679_: *mut LeanObject,
    mut v___y_5680_: *mut LeanObject,
    mut v___y_5681_: *mut LeanObject,
    mut v___y_5682_: *mut LeanObject,
    mut v___y_5683_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_symm_boxed_5684_: u8 = 0;
    let mut v_res_5685_: *mut LeanObject = core::ptr::null_mut();
    v_symm_boxed_5684_ = (lean_unbox(v_symm_5673_) as u8);
    v_res_5685_ = l_Lean_Elab_Tactic_rewriteTarget___lam__0(
        v_stx_5672_,
        v_symm_boxed_5684_,
        v_config_5674_,
        v___y_5675_,
        v___y_5676_,
        v___y_5677_,
        v___y_5678_,
        v___y_5679_,
        v___y_5680_,
        v___y_5681_,
        v___y_5682_,
    );
    lean_dec(v___y_5682_);
    lean_dec_ref(v___y_5681_);
    lean_dec(v___y_5680_);
    lean_dec_ref(v___y_5679_);
    lean_dec(v___y_5678_);
    lean_dec_ref(v___y_5677_);
    lean_dec(v___y_5676_);
    lean_dec_ref(v___y_5675_);
    return v_res_5685_;
}
pub unsafe fn l_Lean_Elab_Tactic_rewriteTarget(
    mut v_stx_5686_: *mut LeanObject,
    mut v_symm_5687_: u8,
    mut v_config_5688_: *mut LeanObject,
    mut v_a_5689_: *mut LeanObject,
    mut v_a_5690_: *mut LeanObject,
    mut v_a_5691_: *mut LeanObject,
    mut v_a_5692_: *mut LeanObject,
    mut v_a_5693_: *mut LeanObject,
    mut v_a_5694_: *mut LeanObject,
    mut v_a_5695_: *mut LeanObject,
    mut v_a_5696_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5698_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_5699_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5700_: u8 = 0;
    let mut v___x_5701_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5702_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5703_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5704_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5705_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5706_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5707_: *mut LeanObject = core::ptr::null_mut();
    let mut v_eNew_5708_: *mut LeanObject = core::ptr::null_mut();
    let mut v_eqProof_5709_: *mut LeanObject = core::ptr::null_mut();
    let mut v_mvarIds_5710_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5711_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5712_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5713_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5714_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5715_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5717_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5718_: u8 = 0;
    let mut v___x_5720_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5721_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5722_: u8 = 0;
    let mut v_a_5723_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5725_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5726_: u8 = 0;
    let mut v___x_5728_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5729_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5730_: u8 = 0;
    let mut v_a_5731_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5733_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5734_: u8 = 0;
    let mut v___x_5736_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5737_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5738_: u8 = 0;
    let mut v_a_5739_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5741_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5742_: u8 = 0;
    let mut v___x_5744_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5745_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5746_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5698_ = lean_box((v_symm_5687_) as usize);
                v___f_5699_ = lean_alloc_closure(
                    l_Lean_Elab_Tactic_rewriteTarget___lam__0___boxed as *mut core::ffi::c_void,
                    12,
                    3,
                );
                lean_closure_set(v___f_5699_, 0, v_stx_5686_);
                lean_closure_set(v___f_5699_, 1, v___x_5698_);
                lean_closure_set(v___f_5699_, 2, v_config_5688_);
                v___x_5700_ = 1;
                lean_inc(v_a_5690_);
                lean_inc_ref(v_a_5689_);
                v___x_5701_ = lean_alloc_closure(
                    l_Lean_Elab_Tactic_withMainContext___boxed as *mut core::ffi::c_void,
                    11,
                    4,
                );
                lean_closure_set(v___x_5701_, 0, lean_box(0));
                lean_closure_set(v___x_5701_, 1, v___f_5699_);
                lean_closure_set(v___x_5701_, 2, v_a_5689_);
                lean_closure_set(v___x_5701_, 3, v_a_5690_);
                v___x_5702_ =
                    l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_withSynthesizeImp(
                        lean_box(0),
                        v___x_5701_,
                        v___x_5700_,
                        v_a_5691_,
                        v_a_5692_,
                        v_a_5693_,
                        v_a_5694_,
                        v_a_5695_,
                        v_a_5696_,
                    );
                if lean_obj_tag(v___x_5702_) == 0 {
                    v_a_5703_ = lean_ctor_get(v___x_5702_, 0);
                    lean_inc(v_a_5703_);
                    lean_dec_ref_known(v___x_5702_, 1);
                    v___x_5704_ = l_Lean_Elab_Tactic_finishElabRewrite(
                        v_a_5703_, v_a_5693_, v_a_5694_, v_a_5695_, v_a_5696_,
                    );
                    if lean_obj_tag(v___x_5704_) == 0 {
                        v_a_5705_ = lean_ctor_get(v___x_5704_, 0);
                        lean_inc(v_a_5705_);
                        lean_dec_ref_known(v___x_5704_, 1);
                        v___x_5706_ = l_Lean_Elab_Tactic_getMainGoal___redArg(
                            v_a_5690_, v_a_5693_, v_a_5694_, v_a_5695_, v_a_5696_,
                        );
                        if lean_obj_tag(v___x_5706_) == 0 {
                            v_a_5707_ = lean_ctor_get(v___x_5706_, 0);
                            lean_inc(v_a_5707_);
                            lean_dec_ref_known(v___x_5706_, 1);
                            v_eNew_5708_ = lean_ctor_get(v_a_5705_, 0);
                            lean_inc_ref(v_eNew_5708_);
                            v_eqProof_5709_ = lean_ctor_get(v_a_5705_, 1);
                            lean_inc_ref(v_eqProof_5709_);
                            v_mvarIds_5710_ = lean_ctor_get(v_a_5705_, 2);
                            lean_inc(v_mvarIds_5710_);
                            lean_dec(v_a_5705_);
                            v___x_5711_ = l_Lean_MVarId_replaceTargetEq(
                                v_a_5707_,
                                v_eNew_5708_,
                                v_eqProof_5709_,
                                v_a_5693_,
                                v_a_5694_,
                                v_a_5695_,
                                v_a_5696_,
                            );
                            if lean_obj_tag(v___x_5711_) == 0 {
                                v_a_5712_ = lean_ctor_get(v___x_5711_, 0);
                                lean_inc(v_a_5712_);
                                lean_dec_ref_known(v___x_5711_, 1);
                                v___x_5713_ = lean_alloc_ctor(1, 2, (0) as u32);
                                lean_ctor_set(v___x_5713_, 0, v_a_5712_);
                                lean_ctor_set(v___x_5713_, 1, v_mvarIds_5710_);
                                v___x_5714_ = l_Lean_Elab_Tactic_replaceMainGoal___redArg(
                                    v___x_5713_,
                                    v_a_5690_,
                                    v_a_5693_,
                                    v_a_5694_,
                                    v_a_5695_,
                                    v_a_5696_,
                                );
                                return v___x_5714_;
                            } else {
                                lean_dec(v_mvarIds_5710_);
                                v_a_5715_ = lean_ctor_get(v___x_5711_, 0);
                                v_isSharedCheck_5722_ = (!lean_is_exclusive(v___x_5711_)) as u8;
                                if v_isSharedCheck_5722_ == 0 {
                                    v___x_5717_ = v___x_5711_;
                                    v_isShared_5718_ = v_isSharedCheck_5722_;
                                    state = 1;
                                    continue;
                                } else {
                                    lean_inc(v_a_5715_);
                                    lean_dec(v___x_5711_);
                                    v___x_5717_ = lean_box(0);
                                    v_isShared_5718_ = v_isSharedCheck_5722_;
                                    state = 1;
                                    continue;
                                }
                            }
                        } else {
                            lean_dec(v_a_5705_);
                            v_a_5723_ = lean_ctor_get(v___x_5706_, 0);
                            v_isSharedCheck_5730_ = (!lean_is_exclusive(v___x_5706_)) as u8;
                            if v_isSharedCheck_5730_ == 0 {
                                v___x_5725_ = v___x_5706_;
                                v_isShared_5726_ = v_isSharedCheck_5730_;
                                state = 3;
                                continue;
                            } else {
                                lean_inc(v_a_5723_);
                                lean_dec(v___x_5706_);
                                v___x_5725_ = lean_box(0);
                                v_isShared_5726_ = v_isSharedCheck_5730_;
                                state = 3;
                                continue;
                            }
                        }
                    } else {
                        v_a_5731_ = lean_ctor_get(v___x_5704_, 0);
                        v_isSharedCheck_5738_ = (!lean_is_exclusive(v___x_5704_)) as u8;
                        if v_isSharedCheck_5738_ == 0 {
                            v___x_5733_ = v___x_5704_;
                            v_isShared_5734_ = v_isSharedCheck_5738_;
                            state = 5;
                            continue;
                        } else {
                            lean_inc(v_a_5731_);
                            lean_dec(v___x_5704_);
                            v___x_5733_ = lean_box(0);
                            v_isShared_5734_ = v_isSharedCheck_5738_;
                            state = 5;
                            continue;
                        }
                    }
                } else {
                    v_a_5739_ = lean_ctor_get(v___x_5702_, 0);
                    v_isSharedCheck_5746_ = (!lean_is_exclusive(v___x_5702_)) as u8;
                    if v_isSharedCheck_5746_ == 0 {
                        v___x_5741_ = v___x_5702_;
                        v_isShared_5742_ = v_isSharedCheck_5746_;
                        state = 7;
                        continue;
                    } else {
                        lean_inc(v_a_5739_);
                        lean_dec(v___x_5702_);
                        v___x_5741_ = lean_box(0);
                        v_isShared_5742_ = v_isSharedCheck_5746_;
                        state = 7;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_5718_ == 0 {
                    v___x_5720_ = v___x_5717_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5721_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5721_, 0, v_a_5715_);
                    v___x_5720_ = v_reuseFailAlloc_5721_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_5720_;
            }
            3 => {
                if v_isShared_5726_ == 0 {
                    v___x_5728_ = v___x_5725_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_5729_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5729_, 0, v_a_5723_);
                    v___x_5728_ = v_reuseFailAlloc_5729_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_5728_;
            }
            5 => {
                if v_isShared_5734_ == 0 {
                    v___x_5736_ = v___x_5733_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_5737_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5737_, 0, v_a_5731_);
                    v___x_5736_ = v_reuseFailAlloc_5737_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_5736_;
            }
            7 => {
                if v_isShared_5742_ == 0 {
                    v___x_5744_ = v___x_5741_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_5745_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5745_, 0, v_a_5739_);
                    v___x_5744_ = v_reuseFailAlloc_5745_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_5744_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_Tactic_rewriteTarget___boxed(
    mut v_stx_5747_: *mut LeanObject,
    mut v_symm_5748_: *mut LeanObject,
    mut v_config_5749_: *mut LeanObject,
    mut v_a_5750_: *mut LeanObject,
    mut v_a_5751_: *mut LeanObject,
    mut v_a_5752_: *mut LeanObject,
    mut v_a_5753_: *mut LeanObject,
    mut v_a_5754_: *mut LeanObject,
    mut v_a_5755_: *mut LeanObject,
    mut v_a_5756_: *mut LeanObject,
    mut v_a_5757_: *mut LeanObject,
    mut v_a_5758_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_symm_boxed_5759_: u8 = 0;
    let mut v_res_5760_: *mut LeanObject = core::ptr::null_mut();
    v_symm_boxed_5759_ = (lean_unbox(v_symm_5748_) as u8);
    v_res_5760_ = l_Lean_Elab_Tactic_rewriteTarget(
        v_stx_5747_,
        v_symm_boxed_5759_,
        v_config_5749_,
        v_a_5750_,
        v_a_5751_,
        v_a_5752_,
        v_a_5753_,
        v_a_5754_,
        v_a_5755_,
        v_a_5756_,
        v_a_5757_,
    );
    lean_dec(v_a_5757_);
    lean_dec_ref(v_a_5756_);
    lean_dec(v_a_5755_);
    lean_dec_ref(v_a_5754_);
    lean_dec(v_a_5753_);
    lean_dec_ref(v_a_5752_);
    lean_dec(v_a_5751_);
    lean_dec_ref(v_a_5750_);
    return v_res_5760_;
}
pub unsafe fn l_Lean_Elab_Tactic_rewriteLocalDecl___lam__0(
    mut v_fvarId_5761_: *mut LeanObject,
    mut v_stx_5762_: *mut LeanObject,
    mut v_symm_5763_: u8,
    mut v_config_5764_: *mut LeanObject,
    mut v___y_5765_: *mut LeanObject,
    mut v___y_5766_: *mut LeanObject,
    mut v___y_5767_: *mut LeanObject,
    mut v___y_5768_: *mut LeanObject,
    mut v___y_5769_: *mut LeanObject,
    mut v___y_5770_: *mut LeanObject,
    mut v___y_5771_: *mut LeanObject,
    mut v___y_5772_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5774_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5775_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5776_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5777_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5778_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5779_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5780_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5782_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5783_: u8 = 0;
    let mut v___x_5785_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5786_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5787_: u8 = 0;
    let mut v_a_5788_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5790_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5791_: u8 = 0;
    let mut v___x_5793_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5794_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5795_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5774_ = l_Lean_FVarId_getDecl___redArg(
                    v_fvarId_5761_,
                    v___y_5769_,
                    v___y_5771_,
                    v___y_5772_,
                );
                if lean_obj_tag(v___x_5774_) == 0 {
                    v_a_5775_ = lean_ctor_get(v___x_5774_, 0);
                    lean_inc(v_a_5775_);
                    lean_dec_ref_known(v___x_5774_, 1);
                    v___x_5776_ = l_Lean_Elab_Tactic_getMainGoal___redArg(
                        v___y_5766_,
                        v___y_5769_,
                        v___y_5770_,
                        v___y_5771_,
                        v___y_5772_,
                    );
                    if lean_obj_tag(v___x_5776_) == 0 {
                        v_a_5777_ = lean_ctor_get(v___x_5776_, 0);
                        lean_inc(v_a_5777_);
                        lean_dec_ref_known(v___x_5776_, 1);
                        v___x_5778_ = l_Lean_LocalDecl_type(v_a_5775_);
                        lean_dec(v_a_5775_);
                        v___x_5779_ = l_Lean_Elab_Tactic_elabRewrite(
                            v_a_5777_,
                            v___x_5778_,
                            v_stx_5762_,
                            v_symm_5763_,
                            v_config_5764_,
                            v___y_5765_,
                            v___y_5766_,
                            v___y_5767_,
                            v___y_5768_,
                            v___y_5769_,
                            v___y_5770_,
                            v___y_5771_,
                            v___y_5772_,
                        );
                        return v___x_5779_;
                    } else {
                        lean_dec(v_a_5775_);
                        lean_dec_ref(v_config_5764_);
                        lean_dec(v_stx_5762_);
                        v_a_5780_ = lean_ctor_get(v___x_5776_, 0);
                        v_isSharedCheck_5787_ = (!lean_is_exclusive(v___x_5776_)) as u8;
                        if v_isSharedCheck_5787_ == 0 {
                            v___x_5782_ = v___x_5776_;
                            v_isShared_5783_ = v_isSharedCheck_5787_;
                            state = 1;
                            continue;
                        } else {
                            lean_inc(v_a_5780_);
                            lean_dec(v___x_5776_);
                            v___x_5782_ = lean_box(0);
                            v_isShared_5783_ = v_isSharedCheck_5787_;
                            state = 1;
                            continue;
                        }
                    }
                } else {
                    lean_dec_ref(v_config_5764_);
                    lean_dec(v_stx_5762_);
                    v_a_5788_ = lean_ctor_get(v___x_5774_, 0);
                    v_isSharedCheck_5795_ = (!lean_is_exclusive(v___x_5774_)) as u8;
                    if v_isSharedCheck_5795_ == 0 {
                        v___x_5790_ = v___x_5774_;
                        v_isShared_5791_ = v_isSharedCheck_5795_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_5788_);
                        lean_dec(v___x_5774_);
                        v___x_5790_ = lean_box(0);
                        v_isShared_5791_ = v_isSharedCheck_5795_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_5783_ == 0 {
                    v___x_5785_ = v___x_5782_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5786_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5786_, 0, v_a_5780_);
                    v___x_5785_ = v_reuseFailAlloc_5786_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_5785_;
            }
            3 => {
                if v_isShared_5791_ == 0 {
                    v___x_5793_ = v___x_5790_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_5794_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5794_, 0, v_a_5788_);
                    v___x_5793_ = v_reuseFailAlloc_5794_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_5793_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_Tactic_rewriteLocalDecl___lam__0___boxed(
    mut v_fvarId_5796_: *mut LeanObject,
    mut v_stx_5797_: *mut LeanObject,
    mut v_symm_5798_: *mut LeanObject,
    mut v_config_5799_: *mut LeanObject,
    mut v___y_5800_: *mut LeanObject,
    mut v___y_5801_: *mut LeanObject,
    mut v___y_5802_: *mut LeanObject,
    mut v___y_5803_: *mut LeanObject,
    mut v___y_5804_: *mut LeanObject,
    mut v___y_5805_: *mut LeanObject,
    mut v___y_5806_: *mut LeanObject,
    mut v___y_5807_: *mut LeanObject,
    mut v___y_5808_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_symm_boxed_5809_: u8 = 0;
    let mut v_res_5810_: *mut LeanObject = core::ptr::null_mut();
    v_symm_boxed_5809_ = (lean_unbox(v_symm_5798_) as u8);
    v_res_5810_ = l_Lean_Elab_Tactic_rewriteLocalDecl___lam__0(
        v_fvarId_5796_,
        v_stx_5797_,
        v_symm_boxed_5809_,
        v_config_5799_,
        v___y_5800_,
        v___y_5801_,
        v___y_5802_,
        v___y_5803_,
        v___y_5804_,
        v___y_5805_,
        v___y_5806_,
        v___y_5807_,
    );
    lean_dec(v___y_5807_);
    lean_dec_ref(v___y_5806_);
    lean_dec(v___y_5805_);
    lean_dec_ref(v___y_5804_);
    lean_dec(v___y_5803_);
    lean_dec_ref(v___y_5802_);
    lean_dec(v___y_5801_);
    lean_dec_ref(v___y_5800_);
    return v_res_5810_;
}
pub unsafe fn l_Lean_Elab_Tactic_rewriteLocalDecl___lam__1(
    mut v_eqProof_5811_: *mut LeanObject,
    mut v___x_5812_: *mut LeanObject,
    mut v_eNew_5813_: *mut LeanObject,
    mut v_a_5814_: *mut LeanObject,
    mut v_fvarId_5815_: *mut LeanObject,
    mut v___y_5816_: *mut LeanObject,
    mut v___y_5817_: *mut LeanObject,
    mut v___y_5818_: *mut LeanObject,
    mut v___y_5819_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5821_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5822_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5823_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5824_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5825_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5826_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5828_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5829_: u8 = 0;
    let mut v___x_5831_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5832_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5833_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5821_ = l_Lean_Meta_mkEqMP(
                    v_eqProof_5811_,
                    v___x_5812_,
                    v___y_5816_,
                    v___y_5817_,
                    v___y_5818_,
                    v___y_5819_,
                );
                if lean_obj_tag(v___x_5821_) == 0 {
                    v_a_5822_ = lean_ctor_get(v___x_5821_, 0);
                    lean_inc(v_a_5822_);
                    lean_dec_ref_known(v___x_5821_, 1);
                    v___x_5823_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v___x_5823_, 0, v_eNew_5813_);
                    v___x_5824_ = lean_box(0);
                    v___x_5825_ = l_Lean_MVarId_replace(
                        v_a_5814_,
                        v_fvarId_5815_,
                        v_a_5822_,
                        v___x_5823_,
                        v___x_5824_,
                        v___y_5816_,
                        v___y_5817_,
                        v___y_5818_,
                        v___y_5819_,
                    );
                    return v___x_5825_;
                } else {
                    lean_dec(v_fvarId_5815_);
                    lean_dec(v_a_5814_);
                    lean_dec_ref(v_eNew_5813_);
                    v_a_5826_ = lean_ctor_get(v___x_5821_, 0);
                    v_isSharedCheck_5833_ = (!lean_is_exclusive(v___x_5821_)) as u8;
                    if v_isSharedCheck_5833_ == 0 {
                        v___x_5828_ = v___x_5821_;
                        v_isShared_5829_ = v_isSharedCheck_5833_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_5826_);
                        lean_dec(v___x_5821_);
                        v___x_5828_ = lean_box(0);
                        v_isShared_5829_ = v_isSharedCheck_5833_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_5829_ == 0 {
                    v___x_5831_ = v___x_5828_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5832_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5832_, 0, v_a_5826_);
                    v___x_5831_ = v_reuseFailAlloc_5832_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_5831_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_Tactic_rewriteLocalDecl___lam__1___boxed(
    mut v_eqProof_5834_: *mut LeanObject,
    mut v___x_5835_: *mut LeanObject,
    mut v_eNew_5836_: *mut LeanObject,
    mut v_a_5837_: *mut LeanObject,
    mut v_fvarId_5838_: *mut LeanObject,
    mut v___y_5839_: *mut LeanObject,
    mut v___y_5840_: *mut LeanObject,
    mut v___y_5841_: *mut LeanObject,
    mut v___y_5842_: *mut LeanObject,
    mut v___y_5843_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5844_: *mut LeanObject = core::ptr::null_mut();
    v_res_5844_ = l_Lean_Elab_Tactic_rewriteLocalDecl___lam__1(
        v_eqProof_5834_,
        v___x_5835_,
        v_eNew_5836_,
        v_a_5837_,
        v_fvarId_5838_,
        v___y_5839_,
        v___y_5840_,
        v___y_5841_,
        v___y_5842_,
    );
    lean_dec(v___y_5842_);
    lean_dec_ref(v___y_5841_);
    lean_dec(v___y_5840_);
    lean_dec_ref(v___y_5839_);
    return v_res_5844_;
}
pub unsafe fn l_Lean_Elab_Tactic_rewriteLocalDecl___lam__2(
    mut v___f_5845_: *mut LeanObject,
    mut v___x_5846_: u8,
    mut v_fvarId_5847_: *mut LeanObject,
    mut v___y_5848_: *mut LeanObject,
    mut v___y_5849_: *mut LeanObject,
    mut v___y_5850_: *mut LeanObject,
    mut v___y_5851_: *mut LeanObject,
    mut v___y_5852_: *mut LeanObject,
    mut v___y_5853_: *mut LeanObject,
    mut v___y_5854_: *mut LeanObject,
    mut v___y_5855_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5857_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5858_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5859_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5860_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5861_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5862_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5863_: *mut LeanObject = core::ptr::null_mut();
    let mut v_eNew_5864_: *mut LeanObject = core::ptr::null_mut();
    let mut v_eqProof_5865_: *mut LeanObject = core::ptr::null_mut();
    let mut v_mvarIds_5866_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5867_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_5868_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5869_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5870_: *mut LeanObject = core::ptr::null_mut();
    let mut v_mvarId_5871_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5872_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5873_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5874_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5876_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5877_: u8 = 0;
    let mut v___x_5879_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5880_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5881_: u8 = 0;
    let mut v_a_5882_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5884_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5885_: u8 = 0;
    let mut v___x_5887_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5888_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5889_: u8 = 0;
    let mut v_a_5890_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5892_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5893_: u8 = 0;
    let mut v___x_5895_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5896_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5897_: u8 = 0;
    let mut v_a_5898_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5900_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5901_: u8 = 0;
    let mut v___x_5903_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5904_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5905_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                lean_inc(v___y_5849_);
                v___x_5857_ = lean_alloc_closure(
                    l_Lean_Elab_Tactic_withMainContext___boxed as *mut core::ffi::c_void,
                    11,
                    4,
                );
                lean_closure_set(v___x_5857_, 0, lean_box(0));
                lean_closure_set(v___x_5857_, 1, v___f_5845_);
                lean_closure_set(v___x_5857_, 2, v___y_5848_);
                lean_closure_set(v___x_5857_, 3, v___y_5849_);
                v___x_5858_ =
                    l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_withSynthesizeImp(
                        lean_box(0),
                        v___x_5857_,
                        v___x_5846_,
                        v___y_5850_,
                        v___y_5851_,
                        v___y_5852_,
                        v___y_5853_,
                        v___y_5854_,
                        v___y_5855_,
                    );
                if lean_obj_tag(v___x_5858_) == 0 {
                    v_a_5859_ = lean_ctor_get(v___x_5858_, 0);
                    lean_inc(v_a_5859_);
                    lean_dec_ref_known(v___x_5858_, 1);
                    v___x_5860_ = l_Lean_Elab_Tactic_finishElabRewrite(
                        v_a_5859_,
                        v___y_5852_,
                        v___y_5853_,
                        v___y_5854_,
                        v___y_5855_,
                    );
                    if lean_obj_tag(v___x_5860_) == 0 {
                        v_a_5861_ = lean_ctor_get(v___x_5860_, 0);
                        lean_inc(v_a_5861_);
                        lean_dec_ref_known(v___x_5860_, 1);
                        v___x_5862_ = l_Lean_Elab_Tactic_getMainGoal___redArg(
                            v___y_5849_,
                            v___y_5852_,
                            v___y_5853_,
                            v___y_5854_,
                            v___y_5855_,
                        );
                        if lean_obj_tag(v___x_5862_) == 0 {
                            v_a_5863_ = lean_ctor_get(v___x_5862_, 0);
                            lean_inc_n(v_a_5863_, 2);
                            lean_dec_ref_known(v___x_5862_, 1);
                            v_eNew_5864_ = lean_ctor_get(v_a_5861_, 0);
                            lean_inc_ref(v_eNew_5864_);
                            v_eqProof_5865_ = lean_ctor_get(v_a_5861_, 1);
                            lean_inc_ref(v_eqProof_5865_);
                            v_mvarIds_5866_ = lean_ctor_get(v_a_5861_, 2);
                            lean_inc(v_mvarIds_5866_);
                            lean_dec(v_a_5861_);
                            lean_inc(v_fvarId_5847_);
                            v___x_5867_ = l_Lean_mkFVar(v_fvarId_5847_);
                            v___f_5868_ = lean_alloc_closure(
                                l_Lean_Elab_Tactic_rewriteLocalDecl___lam__1___boxed
                                    as *mut core::ffi::c_void,
                                10,
                                5,
                            );
                            lean_closure_set(v___f_5868_, 0, v_eqProof_5865_);
                            lean_closure_set(v___f_5868_, 1, v___x_5867_);
                            lean_closure_set(v___f_5868_, 2, v_eNew_5864_);
                            lean_closure_set(v___f_5868_, 3, v_a_5863_);
                            lean_closure_set(v___f_5868_, 4, v_fvarId_5847_);
                            v___x_5869_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_finishElabRewrite_spec__1___redArg(v_a_5863_, v___f_5868_, v___y_5852_, v___y_5853_, v___y_5854_, v___y_5855_);
                            if lean_obj_tag(v___x_5869_) == 0 {
                                v_a_5870_ = lean_ctor_get(v___x_5869_, 0);
                                lean_inc(v_a_5870_);
                                lean_dec_ref_known(v___x_5869_, 1);
                                v_mvarId_5871_ = lean_ctor_get(v_a_5870_, 1);
                                lean_inc(v_mvarId_5871_);
                                lean_dec(v_a_5870_);
                                v___x_5872_ = lean_alloc_ctor(1, 2, (0) as u32);
                                lean_ctor_set(v___x_5872_, 0, v_mvarId_5871_);
                                lean_ctor_set(v___x_5872_, 1, v_mvarIds_5866_);
                                v___x_5873_ = l_Lean_Elab_Tactic_replaceMainGoal___redArg(
                                    v___x_5872_,
                                    v___y_5849_,
                                    v___y_5852_,
                                    v___y_5853_,
                                    v___y_5854_,
                                    v___y_5855_,
                                );
                                lean_dec(v___y_5849_);
                                return v___x_5873_;
                            } else {
                                lean_dec(v_mvarIds_5866_);
                                lean_dec(v___y_5849_);
                                v_a_5874_ = lean_ctor_get(v___x_5869_, 0);
                                v_isSharedCheck_5881_ = (!lean_is_exclusive(v___x_5869_)) as u8;
                                if v_isSharedCheck_5881_ == 0 {
                                    v___x_5876_ = v___x_5869_;
                                    v_isShared_5877_ = v_isSharedCheck_5881_;
                                    state = 1;
                                    continue;
                                } else {
                                    lean_inc(v_a_5874_);
                                    lean_dec(v___x_5869_);
                                    v___x_5876_ = lean_box(0);
                                    v_isShared_5877_ = v_isSharedCheck_5881_;
                                    state = 1;
                                    continue;
                                }
                            }
                        } else {
                            lean_dec(v_a_5861_);
                            lean_dec(v___y_5849_);
                            lean_dec(v_fvarId_5847_);
                            v_a_5882_ = lean_ctor_get(v___x_5862_, 0);
                            v_isSharedCheck_5889_ = (!lean_is_exclusive(v___x_5862_)) as u8;
                            if v_isSharedCheck_5889_ == 0 {
                                v___x_5884_ = v___x_5862_;
                                v_isShared_5885_ = v_isSharedCheck_5889_;
                                state = 3;
                                continue;
                            } else {
                                lean_inc(v_a_5882_);
                                lean_dec(v___x_5862_);
                                v___x_5884_ = lean_box(0);
                                v_isShared_5885_ = v_isSharedCheck_5889_;
                                state = 3;
                                continue;
                            }
                        }
                    } else {
                        lean_dec(v___y_5849_);
                        lean_dec(v_fvarId_5847_);
                        v_a_5890_ = lean_ctor_get(v___x_5860_, 0);
                        v_isSharedCheck_5897_ = (!lean_is_exclusive(v___x_5860_)) as u8;
                        if v_isSharedCheck_5897_ == 0 {
                            v___x_5892_ = v___x_5860_;
                            v_isShared_5893_ = v_isSharedCheck_5897_;
                            state = 5;
                            continue;
                        } else {
                            lean_inc(v_a_5890_);
                            lean_dec(v___x_5860_);
                            v___x_5892_ = lean_box(0);
                            v_isShared_5893_ = v_isSharedCheck_5897_;
                            state = 5;
                            continue;
                        }
                    }
                } else {
                    lean_dec(v___y_5849_);
                    lean_dec(v_fvarId_5847_);
                    v_a_5898_ = lean_ctor_get(v___x_5858_, 0);
                    v_isSharedCheck_5905_ = (!lean_is_exclusive(v___x_5858_)) as u8;
                    if v_isSharedCheck_5905_ == 0 {
                        v___x_5900_ = v___x_5858_;
                        v_isShared_5901_ = v_isSharedCheck_5905_;
                        state = 7;
                        continue;
                    } else {
                        lean_inc(v_a_5898_);
                        lean_dec(v___x_5858_);
                        v___x_5900_ = lean_box(0);
                        v_isShared_5901_ = v_isSharedCheck_5905_;
                        state = 7;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_5877_ == 0 {
                    v___x_5879_ = v___x_5876_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5880_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5880_, 0, v_a_5874_);
                    v___x_5879_ = v_reuseFailAlloc_5880_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_5879_;
            }
            3 => {
                if v_isShared_5885_ == 0 {
                    v___x_5887_ = v___x_5884_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_5888_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5888_, 0, v_a_5882_);
                    v___x_5887_ = v_reuseFailAlloc_5888_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_5887_;
            }
            5 => {
                if v_isShared_5893_ == 0 {
                    v___x_5895_ = v___x_5892_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_5896_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5896_, 0, v_a_5890_);
                    v___x_5895_ = v_reuseFailAlloc_5896_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_5895_;
            }
            7 => {
                if v_isShared_5901_ == 0 {
                    v___x_5903_ = v___x_5900_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_5904_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5904_, 0, v_a_5898_);
                    v___x_5903_ = v_reuseFailAlloc_5904_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_5903_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_Tactic_rewriteLocalDecl___lam__2___boxed(
    mut v___f_5906_: *mut LeanObject,
    mut v___x_5907_: *mut LeanObject,
    mut v_fvarId_5908_: *mut LeanObject,
    mut v___y_5909_: *mut LeanObject,
    mut v___y_5910_: *mut LeanObject,
    mut v___y_5911_: *mut LeanObject,
    mut v___y_5912_: *mut LeanObject,
    mut v___y_5913_: *mut LeanObject,
    mut v___y_5914_: *mut LeanObject,
    mut v___y_5915_: *mut LeanObject,
    mut v___y_5916_: *mut LeanObject,
    mut v___y_5917_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1374__boxed_5918_: u8 = 0;
    let mut v_res_5919_: *mut LeanObject = core::ptr::null_mut();
    v___x_1374__boxed_5918_ = (lean_unbox(v___x_5907_) as u8);
    v_res_5919_ = l_Lean_Elab_Tactic_rewriteLocalDecl___lam__2(
        v___f_5906_,
        v___x_1374__boxed_5918_,
        v_fvarId_5908_,
        v___y_5909_,
        v___y_5910_,
        v___y_5911_,
        v___y_5912_,
        v___y_5913_,
        v___y_5914_,
        v___y_5915_,
        v___y_5916_,
    );
    lean_dec(v___y_5916_);
    lean_dec_ref(v___y_5915_);
    lean_dec(v___y_5914_);
    lean_dec_ref(v___y_5913_);
    lean_dec(v___y_5912_);
    lean_dec_ref(v___y_5911_);
    return v_res_5919_;
}
pub unsafe fn l_Lean_Elab_Tactic_rewriteLocalDecl(
    mut v_stx_5920_: *mut LeanObject,
    mut v_symm_5921_: u8,
    mut v_fvarId_5922_: *mut LeanObject,
    mut v_config_5923_: *mut LeanObject,
    mut v_a_5924_: *mut LeanObject,
    mut v_a_5925_: *mut LeanObject,
    mut v_a_5926_: *mut LeanObject,
    mut v_a_5927_: *mut LeanObject,
    mut v_a_5928_: *mut LeanObject,
    mut v_a_5929_: *mut LeanObject,
    mut v_a_5930_: *mut LeanObject,
    mut v_a_5931_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5933_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_5934_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5935_: u8 = 0;
    let mut v___x_5936_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_5937_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5938_: *mut LeanObject = core::ptr::null_mut();
    v___x_5933_ = lean_box((v_symm_5921_) as usize);
    lean_inc(v_fvarId_5922_);
    v___f_5934_ = lean_alloc_closure(
        l_Lean_Elab_Tactic_rewriteLocalDecl___lam__0___boxed as *mut core::ffi::c_void,
        13,
        4,
    );
    lean_closure_set(v___f_5934_, 0, v_fvarId_5922_);
    lean_closure_set(v___f_5934_, 1, v_stx_5920_);
    lean_closure_set(v___f_5934_, 2, v___x_5933_);
    lean_closure_set(v___f_5934_, 3, v_config_5923_);
    v___x_5935_ = 1;
    v___x_5936_ = lean_box((v___x_5935_) as usize);
    v___f_5937_ = lean_alloc_closure(
        l_Lean_Elab_Tactic_rewriteLocalDecl___lam__2___boxed as *mut core::ffi::c_void,
        12,
        3,
    );
    lean_closure_set(v___f_5937_, 0, v___f_5934_);
    lean_closure_set(v___f_5937_, 1, v___x_5936_);
    lean_closure_set(v___f_5937_, 2, v_fvarId_5922_);
    v___x_5938_ = l_Lean_Elab_Tactic_withMainContext___redArg(
        v___f_5937_,
        v_a_5924_,
        v_a_5925_,
        v_a_5926_,
        v_a_5927_,
        v_a_5928_,
        v_a_5929_,
        v_a_5930_,
        v_a_5931_,
    );
    return v___x_5938_;
}
pub unsafe fn l_Lean_Elab_Tactic_rewriteLocalDecl___boxed(
    mut v_stx_5939_: *mut LeanObject,
    mut v_symm_5940_: *mut LeanObject,
    mut v_fvarId_5941_: *mut LeanObject,
    mut v_config_5942_: *mut LeanObject,
    mut v_a_5943_: *mut LeanObject,
    mut v_a_5944_: *mut LeanObject,
    mut v_a_5945_: *mut LeanObject,
    mut v_a_5946_: *mut LeanObject,
    mut v_a_5947_: *mut LeanObject,
    mut v_a_5948_: *mut LeanObject,
    mut v_a_5949_: *mut LeanObject,
    mut v_a_5950_: *mut LeanObject,
    mut v_a_5951_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_symm_boxed_5952_: u8 = 0;
    let mut v_res_5953_: *mut LeanObject = core::ptr::null_mut();
    v_symm_boxed_5952_ = (lean_unbox(v_symm_5940_) as u8);
    v_res_5953_ = l_Lean_Elab_Tactic_rewriteLocalDecl(
        v_stx_5939_,
        v_symm_boxed_5952_,
        v_fvarId_5941_,
        v_config_5942_,
        v_a_5943_,
        v_a_5944_,
        v_a_5945_,
        v_a_5946_,
        v_a_5947_,
        v_a_5948_,
        v_a_5949_,
        v_a_5950_,
    );
    lean_dec(v_a_5950_);
    lean_dec_ref(v_a_5949_);
    lean_dec(v_a_5948_);
    lean_dec_ref(v_a_5947_);
    lean_dec(v_a_5946_);
    lean_dec_ref(v_a_5945_);
    lean_dec(v_a_5944_);
    lean_dec_ref(v_a_5943_);
    return v_res_5953_;
}
pub unsafe fn _init_l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_withRWRulesSeq_go___closed__1()
-> *mut LeanObject {
    let mut v___x_5955_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5956_: *mut LeanObject = core::ptr::null_mut();
    v___x_5955_ =
        l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_withRWRulesSeq_go___closed__0;
    v___x_5956_ = l_Lean_stringToMessageData(v___x_5955_);
    return v___x_5956_;
}
pub unsafe fn _init_l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_withRWRulesSeq_go___closed__3()
-> *mut LeanObject {
    let mut v___x_5958_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5959_: *mut LeanObject = core::ptr::null_mut();
    v___x_5958_ =
        l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_withRWRulesSeq_go___closed__2;
    v___x_5959_ = l_Lean_stringToMessageData(v___x_5958_);
    return v___x_5959_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_withRWRulesSeq_go(
    mut v_x_5960_: *mut LeanObject,
    mut v_symm_5961_: u8,
    mut v_id_5962_: *mut LeanObject,
    mut v_declName_5963_: *mut LeanObject,
    mut v_hint_5964_: *mut LeanObject,
    mut v_a_5965_: *mut LeanObject,
    mut v_a_5966_: *mut LeanObject,
    mut v_a_5967_: *mut LeanObject,
    mut v_a_5968_: *mut LeanObject,
    mut v_a_5969_: *mut LeanObject,
    mut v_a_5970_: *mut LeanObject,
    mut v_a_5971_: *mut LeanObject,
    mut v_a_5972_: *mut LeanObject,
    mut v_a_5973_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5975_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5976_: u8 = 0;
    let mut v___x_5977_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5978_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5979_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5980_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5981_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5982_: *mut LeanObject = core::ptr::null_mut();
    let mut v_head_5983_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_5984_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5985_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5986_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5987_: u8 = 0;
    let mut v___x_5988_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5989_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5990_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5991_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5992_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5994_: u8 = 0;
    let mut v___x_5995_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5997_: u8 = 0;
    let mut v___x_5998_: u8 = 0;
    let mut v_a_5999_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6001_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6002_: u8 = 0;
    let mut v___x_6004_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6005_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6006_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_a_5965_) == 0 {
                    lean_dec_ref(v_x_5960_);
                    v___x_5975_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_withRWRulesSeq_go___closed__1), core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_withRWRulesSeq_go___closed__1_once), _init_l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_withRWRulesSeq_go___closed__1);
                    v___x_5976_ = 0;
                    v___x_5977_ = l_Lean_MessageData_ofConstName(v_declName_5963_, v___x_5976_);
                    v___x_5978_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_5978_, 0, v___x_5975_);
                    lean_ctor_set(v___x_5978_, 1, v___x_5977_);
                    v___x_5979_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_withRWRulesSeq_go___closed__3), core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_withRWRulesSeq_go___closed__3_once), _init_l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_withRWRulesSeq_go___closed__3);
                    v___x_5980_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_5980_, 0, v___x_5978_);
                    lean_ctor_set(v___x_5980_, 1, v___x_5979_);
                    v___x_5981_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_5981_, 0, v___x_5980_);
                    lean_ctor_set(v___x_5981_, 1, v_hint_5964_);
                    v___x_5982_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Tactic_elabRewrite_spec__3_spec__4___redArg(v___x_5981_, v_a_5970_, v_a_5971_, v_a_5972_, v_a_5973_);
                    return v___x_5982_;
                } else {
                    v_head_5983_ = lean_ctor_get(v_a_5965_, 0);
                    lean_inc(v_head_5983_);
                    v_tail_5984_ = lean_ctor_get(v_a_5965_, 1);
                    lean_inc(v_tail_5984_);
                    lean_dec_ref_known(v_a_5965_, 2);
                    v___x_5985_ = l_Lean_Elab_Tactic_saveState___redArg(
                        v_a_5967_, v_a_5969_, v_a_5971_, v_a_5973_,
                    );
                    if lean_obj_tag(v___x_5985_) == 0 {
                        v_a_5986_ = lean_ctor_get(v___x_5985_, 0);
                        lean_inc(v_a_5986_);
                        lean_dec_ref_known(v___x_5985_, 1);
                        v___x_5987_ = 0;
                        v___x_5988_ = l_Lean_mkCIdentFrom(v_id_5962_, v_head_5983_, v___x_5987_);
                        v___x_5989_ = lean_box((v_symm_5961_) as usize);
                        lean_inc_ref(v_x_5960_);
                        v___x_5990_ = lean_apply_2(v_x_5960_, v___x_5989_, v___x_5988_);
                        v___x_5991_ = l_Lean_Elab_Tactic_withoutRecover___redArg(
                            v___x_5990_,
                            v_a_5966_,
                            v_a_5967_,
                            v_a_5968_,
                            v_a_5969_,
                            v_a_5970_,
                            v_a_5971_,
                            v_a_5972_,
                            v_a_5973_,
                        );
                        if lean_obj_tag(v___x_5991_) == 0 {
                            lean_dec(v_a_5986_);
                            lean_dec(v_tail_5984_);
                            lean_dec_ref(v_hint_5964_);
                            lean_dec(v_declName_5963_);
                            lean_dec_ref(v_x_5960_);
                            return v___x_5991_;
                        } else {
                            v_a_5992_ = lean_ctor_get(v___x_5991_, 0);
                            lean_inc(v_a_5992_);
                            v___x_5997_ = l_Lean_Exception_isInterrupt(v_a_5992_);
                            if v___x_5997_ == 0 {
                                v___x_5998_ = l_Lean_Exception_isRuntime(v_a_5992_);
                                v___y_5994_ = v___x_5998_;
                                state = 1;
                                continue;
                            } else {
                                lean_dec(v_a_5992_);
                                v___y_5994_ = v___x_5997_;
                                state = 1;
                                continue;
                            }
                        }
                    } else {
                        lean_dec(v_tail_5984_);
                        lean_dec(v_head_5983_);
                        lean_dec_ref(v_hint_5964_);
                        lean_dec(v_declName_5963_);
                        lean_dec_ref(v_x_5960_);
                        v_a_5999_ = lean_ctor_get(v___x_5985_, 0);
                        v_isSharedCheck_6006_ = (!lean_is_exclusive(v___x_5985_)) as u8;
                        if v_isSharedCheck_6006_ == 0 {
                            v___x_6001_ = v___x_5985_;
                            v_isShared_6002_ = v_isSharedCheck_6006_;
                            state = 2;
                            continue;
                        } else {
                            lean_inc(v_a_5999_);
                            lean_dec(v___x_5985_);
                            v___x_6001_ = lean_box(0);
                            v_isShared_6002_ = v_isSharedCheck_6006_;
                            state = 2;
                            continue;
                        }
                    }
                }
            }
            1 => {
                if v___y_5994_ == 0 {
                    lean_dec_ref_known(v___x_5991_, 1);
                    v___x_5995_ = l_Lean_Elab_Tactic_SavedState_restore___redArg(
                        v_a_5986_,
                        v___y_5994_,
                        v_a_5967_,
                        v_a_5968_,
                        v_a_5969_,
                        v_a_5970_,
                        v_a_5971_,
                        v_a_5972_,
                        v_a_5973_,
                    );
                    if lean_obj_tag(v___x_5995_) == 0 {
                        lean_dec_ref_known(v___x_5995_, 1);
                        v_a_5965_ = v_tail_5984_;
                        state = 0;
                        continue;
                    } else {
                        lean_dec(v_tail_5984_);
                        lean_dec_ref(v_hint_5964_);
                        lean_dec(v_declName_5963_);
                        lean_dec_ref(v_x_5960_);
                        return v___x_5995_;
                    }
                } else {
                    lean_dec(v_a_5986_);
                    lean_dec(v_tail_5984_);
                    lean_dec_ref(v_hint_5964_);
                    lean_dec(v_declName_5963_);
                    lean_dec_ref(v_x_5960_);
                    return v___x_5991_;
                }
            }
            2 => {
                if v_isShared_6002_ == 0 {
                    v___x_6004_ = v___x_6001_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_6005_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6005_, 0, v_a_5999_);
                    v___x_6004_ = v_reuseFailAlloc_6005_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_6004_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_withRWRulesSeq_go___boxed(
    mut v_x_6007_: *mut LeanObject,
    mut v_symm_6008_: *mut LeanObject,
    mut v_id_6009_: *mut LeanObject,
    mut v_declName_6010_: *mut LeanObject,
    mut v_hint_6011_: *mut LeanObject,
    mut v_a_6012_: *mut LeanObject,
    mut v_a_6013_: *mut LeanObject,
    mut v_a_6014_: *mut LeanObject,
    mut v_a_6015_: *mut LeanObject,
    mut v_a_6016_: *mut LeanObject,
    mut v_a_6017_: *mut LeanObject,
    mut v_a_6018_: *mut LeanObject,
    mut v_a_6019_: *mut LeanObject,
    mut v_a_6020_: *mut LeanObject,
    mut v_a_6021_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_symm_boxed_6022_: u8 = 0;
    let mut v_res_6023_: *mut LeanObject = core::ptr::null_mut();
    v_symm_boxed_6022_ = (lean_unbox(v_symm_6008_) as u8);
    v_res_6023_ = l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_withRWRulesSeq_go(
        v_x_6007_,
        v_symm_boxed_6022_,
        v_id_6009_,
        v_declName_6010_,
        v_hint_6011_,
        v_a_6012_,
        v_a_6013_,
        v_a_6014_,
        v_a_6015_,
        v_a_6016_,
        v_a_6017_,
        v_a_6018_,
        v_a_6019_,
        v_a_6020_,
    );
    lean_dec(v_a_6020_);
    lean_dec_ref(v_a_6019_);
    lean_dec(v_a_6018_);
    lean_dec_ref(v_a_6017_);
    lean_dec(v_a_6016_);
    lean_dec_ref(v_a_6015_);
    lean_dec(v_a_6014_);
    lean_dec_ref(v_a_6013_);
    lean_dec(v_id_6009_);
    return v_res_6023_;
}
pub unsafe fn l_Lean_Elab_Tactic_withRWRulesSeq___lam__0(
    mut v_a_6024_: *mut LeanObject,
    mut v_trees_6025_: *mut LeanObject,
    mut v___y_6026_: *mut LeanObject,
    mut v___y_6027_: *mut LeanObject,
    mut v___y_6028_: *mut LeanObject,
    mut v___y_6029_: *mut LeanObject,
    mut v___y_6030_: *mut LeanObject,
    mut v___y_6031_: *mut LeanObject,
    mut v___y_6032_: *mut LeanObject,
    mut v___y_6033_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6035_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6036_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6038_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6039_: u8 = 0;
    let mut v___x_6040_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6042_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6043_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6044_: u8 = 0;
    let mut v_a_6045_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6047_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6048_: u8 = 0;
    let mut v___x_6050_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6051_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6052_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                lean_inc(v___y_6033_);
                lean_inc_ref(v___y_6032_);
                lean_inc(v___y_6031_);
                lean_inc_ref(v___y_6030_);
                lean_inc(v___y_6029_);
                lean_inc_ref(v___y_6028_);
                lean_inc(v___y_6027_);
                lean_inc_ref(v___y_6026_);
                v___x_6035_ = lean_apply_9(
                    v_a_6024_,
                    v___y_6026_,
                    v___y_6027_,
                    v___y_6028_,
                    v___y_6029_,
                    v___y_6030_,
                    v___y_6031_,
                    v___y_6032_,
                    v___y_6033_,
                    lean_box(0),
                );
                if lean_obj_tag(v___x_6035_) == 0 {
                    v_a_6036_ = lean_ctor_get(v___x_6035_, 0);
                    v_isSharedCheck_6044_ = (!lean_is_exclusive(v___x_6035_)) as u8;
                    if v_isSharedCheck_6044_ == 0 {
                        v___x_6038_ = v___x_6035_;
                        v_isShared_6039_ = v_isSharedCheck_6044_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_6036_);
                        lean_dec(v___x_6035_);
                        v___x_6038_ = lean_box(0);
                        v_isShared_6039_ = v_isSharedCheck_6044_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec_ref(v_trees_6025_);
                    v_a_6045_ = lean_ctor_get(v___x_6035_, 0);
                    v_isSharedCheck_6052_ = (!lean_is_exclusive(v___x_6035_)) as u8;
                    if v_isSharedCheck_6052_ == 0 {
                        v___x_6047_ = v___x_6035_;
                        v_isShared_6048_ = v_isSharedCheck_6052_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_6045_);
                        lean_dec(v___x_6035_);
                        v___x_6047_ = lean_box(0);
                        v_isShared_6048_ = v_isSharedCheck_6052_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v___x_6040_ = lean_alloc_ctor(1, 2, (0) as u32);
                lean_ctor_set(v___x_6040_, 0, v_a_6036_);
                lean_ctor_set(v___x_6040_, 1, v_trees_6025_);
                if v_isShared_6039_ == 0 {
                    lean_ctor_set(v___x_6038_, 0, v___x_6040_);
                    v___x_6042_ = v___x_6038_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_6043_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6043_, 0, v___x_6040_);
                    v___x_6042_ = v_reuseFailAlloc_6043_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_6042_;
            }
            3 => {
                if v_isShared_6048_ == 0 {
                    v___x_6050_ = v___x_6047_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_6051_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6051_, 0, v_a_6045_);
                    v___x_6050_ = v_reuseFailAlloc_6051_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_6050_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_Tactic_withRWRulesSeq___lam__0___boxed(
    mut v_a_6053_: *mut LeanObject,
    mut v_trees_6054_: *mut LeanObject,
    mut v___y_6055_: *mut LeanObject,
    mut v___y_6056_: *mut LeanObject,
    mut v___y_6057_: *mut LeanObject,
    mut v___y_6058_: *mut LeanObject,
    mut v___y_6059_: *mut LeanObject,
    mut v___y_6060_: *mut LeanObject,
    mut v___y_6061_: *mut LeanObject,
    mut v___y_6062_: *mut LeanObject,
    mut v___y_6063_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6064_: *mut LeanObject = core::ptr::null_mut();
    v_res_6064_ = l_Lean_Elab_Tactic_withRWRulesSeq___lam__0(
        v_a_6053_,
        v_trees_6054_,
        v___y_6055_,
        v___y_6056_,
        v___y_6057_,
        v___y_6058_,
        v___y_6059_,
        v___y_6060_,
        v___y_6061_,
        v___y_6062_,
    );
    lean_dec(v___y_6062_);
    lean_dec_ref(v___y_6061_);
    lean_dec(v___y_6060_);
    lean_dec_ref(v___y_6059_);
    lean_dec(v___y_6058_);
    lean_dec_ref(v___y_6057_);
    lean_dec(v___y_6056_);
    lean_dec_ref(v___y_6055_);
    return v_res_6064_;
}
pub unsafe fn l_Lean_Elab_Tactic_withRWRulesSeq___lam__1(
    mut v___x_6065_: *mut LeanObject,
    mut v___y_6066_: *mut LeanObject,
    mut v___y_6067_: *mut LeanObject,
    mut v___y_6068_: *mut LeanObject,
    mut v___y_6069_: *mut LeanObject,
    mut v___y_6070_: *mut LeanObject,
    mut v___y_6071_: *mut LeanObject,
    mut v___y_6072_: *mut LeanObject,
    mut v___y_6073_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6075_: *mut LeanObject = core::ptr::null_mut();
    v___x_6075_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_6075_, 0, v___x_6065_);
    return v___x_6075_;
}
pub unsafe fn l_Lean_Elab_Tactic_withRWRulesSeq___lam__1___boxed(
    mut v___x_6076_: *mut LeanObject,
    mut v___y_6077_: *mut LeanObject,
    mut v___y_6078_: *mut LeanObject,
    mut v___y_6079_: *mut LeanObject,
    mut v___y_6080_: *mut LeanObject,
    mut v___y_6081_: *mut LeanObject,
    mut v___y_6082_: *mut LeanObject,
    mut v___y_6083_: *mut LeanObject,
    mut v___y_6084_: *mut LeanObject,
    mut v___y_6085_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6086_: *mut LeanObject = core::ptr::null_mut();
    v_res_6086_ = l_Lean_Elab_Tactic_withRWRulesSeq___lam__1(
        v___x_6076_,
        v___y_6077_,
        v___y_6078_,
        v___y_6079_,
        v___y_6080_,
        v___y_6081_,
        v___y_6082_,
        v___y_6083_,
        v___y_6084_,
    );
    lean_dec(v___y_6084_);
    lean_dec_ref(v___y_6083_);
    lean_dec(v___y_6082_);
    lean_dec_ref(v___y_6081_);
    lean_dec(v___y_6080_);
    lean_dec_ref(v___y_6079_);
    lean_dec(v___y_6078_);
    lean_dec_ref(v___y_6077_);
    return v_res_6086_;
}
pub unsafe fn l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_withRWRulesSeq_spec__0___redArg___lam__0(
    mut v___y_6087_: *mut LeanObject,
    mut v_mkInfoTree_6088_: *mut LeanObject,
    mut v___y_6089_: *mut LeanObject,
    mut v___y_6090_: *mut LeanObject,
    mut v___y_6091_: *mut LeanObject,
    mut v___y_6092_: *mut LeanObject,
    mut v___y_6093_: *mut LeanObject,
    mut v___y_6094_: *mut LeanObject,
    mut v___y_6095_: *mut LeanObject,
    mut v_a_6096_: *mut LeanObject,
    mut v_a_x3f_6097_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6099_: *mut LeanObject = core::ptr::null_mut();
    let mut v_infoState_6100_: *mut LeanObject = core::ptr::null_mut();
    let mut v_trees_6101_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6102_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6103_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6105_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6106_: u8 = 0;
    let mut v___x_6107_: *mut LeanObject = core::ptr::null_mut();
    let mut v_infoState_6108_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_6109_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_6110_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ngen_6111_: *mut LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_6112_: *mut LeanObject = core::ptr::null_mut();
    let mut v_traceState_6113_: *mut LeanObject = core::ptr::null_mut();
    let mut v_cache_6114_: *mut LeanObject = core::ptr::null_mut();
    let mut v_messages_6115_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_6116_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6118_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6119_: u8 = 0;
    let mut v_enabled_6120_: u8 = 0;
    let mut v_assignment_6121_: *mut LeanObject = core::ptr::null_mut();
    let mut v_lazyAssignment_6122_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6124_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6125_: u8 = 0;
    let mut v___x_6126_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6128_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6130_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6131_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6132_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6134_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6135_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6136_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6137_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6138_: u8 = 0;
    let mut v_unused_6139_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6140_: u8 = 0;
    let mut v_isSharedCheck_6141_: u8 = 0;
    let mut v_a_6142_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6144_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6145_: u8 = 0;
    let mut v___x_6147_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6148_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6149_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_6099_ = lean_st_ref_get(v___y_6087_);
                v_infoState_6100_ = lean_ctor_get(v___x_6099_, 7);
                lean_inc_ref(v_infoState_6100_);
                lean_dec(v___x_6099_);
                v_trees_6101_ = lean_ctor_get(v_infoState_6100_, 2);
                lean_inc_ref(v_trees_6101_);
                lean_dec_ref(v_infoState_6100_);
                lean_inc(v___y_6087_);
                lean_inc_ref(v___y_6095_);
                lean_inc(v___y_6094_);
                lean_inc_ref(v___y_6093_);
                lean_inc(v___y_6092_);
                lean_inc_ref(v___y_6091_);
                lean_inc(v___y_6090_);
                lean_inc_ref(v___y_6089_);
                v___x_6102_ = lean_apply_10(
                    v_mkInfoTree_6088_,
                    v_trees_6101_,
                    v___y_6089_,
                    v___y_6090_,
                    v___y_6091_,
                    v___y_6092_,
                    v___y_6093_,
                    v___y_6094_,
                    v___y_6095_,
                    v___y_6087_,
                    lean_box(0),
                );
                if lean_obj_tag(v___x_6102_) == 0 {
                    v_a_6103_ = lean_ctor_get(v___x_6102_, 0);
                    v_isSharedCheck_6141_ = (!lean_is_exclusive(v___x_6102_)) as u8;
                    if v_isSharedCheck_6141_ == 0 {
                        v___x_6105_ = v___x_6102_;
                        v_isShared_6106_ = v_isSharedCheck_6141_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_6103_);
                        lean_dec(v___x_6102_);
                        v___x_6105_ = lean_box(0);
                        v_isShared_6106_ = v_isSharedCheck_6141_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec_ref(v_a_6096_);
                    v_a_6142_ = lean_ctor_get(v___x_6102_, 0);
                    v_isSharedCheck_6149_ = (!lean_is_exclusive(v___x_6102_)) as u8;
                    if v_isSharedCheck_6149_ == 0 {
                        v___x_6144_ = v___x_6102_;
                        v_isShared_6145_ = v_isSharedCheck_6149_;
                        state = 7;
                        continue;
                    } else {
                        lean_inc(v_a_6142_);
                        lean_dec(v___x_6102_);
                        v___x_6144_ = lean_box(0);
                        v_isShared_6145_ = v_isSharedCheck_6149_;
                        state = 7;
                        continue;
                    }
                }
            }
            1 => {
                v___x_6107_ = lean_st_ref_take(v___y_6087_);
                v_infoState_6108_ = lean_ctor_get(v___x_6107_, 7);
                v_env_6109_ = lean_ctor_get(v___x_6107_, 0);
                v_nextMacroScope_6110_ = lean_ctor_get(v___x_6107_, 1);
                v_ngen_6111_ = lean_ctor_get(v___x_6107_, 2);
                v_auxDeclNGen_6112_ = lean_ctor_get(v___x_6107_, 3);
                v_traceState_6113_ = lean_ctor_get(v___x_6107_, 4);
                v_cache_6114_ = lean_ctor_get(v___x_6107_, 5);
                v_messages_6115_ = lean_ctor_get(v___x_6107_, 6);
                v_snapshotTasks_6116_ = lean_ctor_get(v___x_6107_, 8);
                v_isSharedCheck_6140_ = (!lean_is_exclusive(v___x_6107_)) as u8;
                if v_isSharedCheck_6140_ == 0 {
                    v___x_6118_ = v___x_6107_;
                    v_isShared_6119_ = v_isSharedCheck_6140_;
                    state = 2;
                    continue;
                } else {
                    lean_inc(v_snapshotTasks_6116_);
                    lean_inc(v_infoState_6108_);
                    lean_inc(v_messages_6115_);
                    lean_inc(v_cache_6114_);
                    lean_inc(v_traceState_6113_);
                    lean_inc(v_auxDeclNGen_6112_);
                    lean_inc(v_ngen_6111_);
                    lean_inc(v_nextMacroScope_6110_);
                    lean_inc(v_env_6109_);
                    lean_dec(v___x_6107_);
                    v___x_6118_ = lean_box(0);
                    v_isShared_6119_ = v_isSharedCheck_6140_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_enabled_6120_ = lean_ctor_get_uint8(
                    v_infoState_6108_,
                    (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
                );
                v_assignment_6121_ = lean_ctor_get(v_infoState_6108_, 0);
                v_lazyAssignment_6122_ = lean_ctor_get(v_infoState_6108_, 1);
                v_isSharedCheck_6138_ = (!lean_is_exclusive(v_infoState_6108_)) as u8;
                if v_isSharedCheck_6138_ == 0 {
                    v_unused_6139_ = lean_ctor_get(v_infoState_6108_, 2);
                    lean_dec(v_unused_6139_);
                    v___x_6124_ = v_infoState_6108_;
                    v_isShared_6125_ = v_isSharedCheck_6138_;
                    state = 3;
                    continue;
                } else {
                    lean_inc(v_lazyAssignment_6122_);
                    lean_inc(v_assignment_6121_);
                    lean_dec(v_infoState_6108_);
                    v___x_6124_ = lean_box(0);
                    v_isShared_6125_ = v_isSharedCheck_6138_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_6126_ = l_Lean_PersistentArray_push___redArg(v_a_6096_, v_a_6103_);
                if v_isShared_6125_ == 0 {
                    lean_ctor_set(v___x_6124_, 2, v___x_6126_);
                    v___x_6128_ = v___x_6124_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_6137_ = lean_alloc_ctor(0, 3, (1) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6137_, 0, v_assignment_6121_);
                    lean_ctor_set(v_reuseFailAlloc_6137_, 1, v_lazyAssignment_6122_);
                    lean_ctor_set(v_reuseFailAlloc_6137_, 2, v___x_6126_);
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_6137_,
                        (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
                        v_enabled_6120_,
                    );
                    v___x_6128_ = v_reuseFailAlloc_6137_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                if v_isShared_6119_ == 0 {
                    lean_ctor_set(v___x_6118_, 7, v___x_6128_);
                    v___x_6130_ = v___x_6118_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_6136_ = lean_alloc_ctor(0, 9, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6136_, 0, v_env_6109_);
                    lean_ctor_set(v_reuseFailAlloc_6136_, 1, v_nextMacroScope_6110_);
                    lean_ctor_set(v_reuseFailAlloc_6136_, 2, v_ngen_6111_);
                    lean_ctor_set(v_reuseFailAlloc_6136_, 3, v_auxDeclNGen_6112_);
                    lean_ctor_set(v_reuseFailAlloc_6136_, 4, v_traceState_6113_);
                    lean_ctor_set(v_reuseFailAlloc_6136_, 5, v_cache_6114_);
                    lean_ctor_set(v_reuseFailAlloc_6136_, 6, v_messages_6115_);
                    lean_ctor_set(v_reuseFailAlloc_6136_, 7, v___x_6128_);
                    lean_ctor_set(v_reuseFailAlloc_6136_, 8, v_snapshotTasks_6116_);
                    v___x_6130_ = v_reuseFailAlloc_6136_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v___x_6131_ = lean_st_ref_set(v___y_6087_, v___x_6130_);
                v___x_6132_ = lean_box(0);
                if v_isShared_6106_ == 0 {
                    lean_ctor_set(v___x_6105_, 0, v___x_6132_);
                    v___x_6134_ = v___x_6105_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_6135_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6135_, 0, v___x_6132_);
                    v___x_6134_ = v_reuseFailAlloc_6135_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_6134_;
            }
            7 => {
                if v_isShared_6145_ == 0 {
                    v___x_6147_ = v___x_6144_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_6148_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6148_, 0, v_a_6142_);
                    v___x_6147_ = v_reuseFailAlloc_6148_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_6147_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_withRWRulesSeq_spec__0___redArg___lam__0___boxed(
    mut v___y_6150_: *mut LeanObject,
    mut v_mkInfoTree_6151_: *mut LeanObject,
    mut v___y_6152_: *mut LeanObject,
    mut v___y_6153_: *mut LeanObject,
    mut v___y_6154_: *mut LeanObject,
    mut v___y_6155_: *mut LeanObject,
    mut v___y_6156_: *mut LeanObject,
    mut v___y_6157_: *mut LeanObject,
    mut v___y_6158_: *mut LeanObject,
    mut v_a_6159_: *mut LeanObject,
    mut v_a_x3f_6160_: *mut LeanObject,
    mut v___y_6161_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6162_: *mut LeanObject = core::ptr::null_mut();
    v_res_6162_ = l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_withRWRulesSeq_spec__0___redArg___lam__0(v___y_6150_, v_mkInfoTree_6151_, v___y_6152_, v___y_6153_, v___y_6154_, v___y_6155_, v___y_6156_, v___y_6157_, v___y_6158_, v_a_6159_, v_a_x3f_6160_);
    lean_dec(v_a_x3f_6160_);
    lean_dec_ref(v___y_6158_);
    lean_dec(v___y_6157_);
    lean_dec_ref(v___y_6156_);
    lean_dec(v___y_6155_);
    lean_dec_ref(v___y_6154_);
    lean_dec(v___y_6153_);
    lean_dec_ref(v___y_6152_);
    lean_dec(v___y_6150_);
    return v_res_6162_;
}
pub unsafe fn _init_l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_withRWRulesSeq_spec__0_spec__0___redArg___closed__0()
-> *mut LeanObject {
    let mut v___x_6163_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6164_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6165_: *mut LeanObject = core::ptr::null_mut();
    v___x_6163_ = lean_unsigned_to_nat(32);
    v___x_6164_ = lean_mk_empty_array_with_capacity(v___x_6163_);
    v___x_6165_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_6165_, 0, v___x_6164_);
    return v___x_6165_;
}
pub unsafe fn _init_l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_withRWRulesSeq_spec__0_spec__0___redArg___closed__1()
-> *mut LeanObject {
    let mut v___x_6166_: usize = 0;
    let mut v___x_6167_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6168_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6169_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6170_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6171_: *mut LeanObject = core::ptr::null_mut();
    v___x_6166_ = 5usize;
    v___x_6167_ = lean_unsigned_to_nat(0);
    v___x_6168_ = lean_unsigned_to_nat(32);
    v___x_6169_ = lean_mk_empty_array_with_capacity(v___x_6168_);
    v___x_6170_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_withRWRulesSeq_spec__0_spec__0___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_withRWRulesSeq_spec__0_spec__0___redArg___closed__0_once), _init_l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_withRWRulesSeq_spec__0_spec__0___redArg___closed__0);
    v___x_6171_ = lean_alloc_ctor(0, 4, (core::mem::size_of::<usize>() * 1) as u32);
    lean_ctor_set(v___x_6171_, 0, v___x_6170_);
    lean_ctor_set(v___x_6171_, 1, v___x_6169_);
    lean_ctor_set(v___x_6171_, 2, v___x_6167_);
    lean_ctor_set(v___x_6171_, 3, v___x_6167_);
    lean_ctor_set_usize(v___x_6171_, 4, v___x_6166_);
    return v___x_6171_;
}
pub unsafe fn l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_withRWRulesSeq_spec__0_spec__0___redArg(
    mut v___y_6172_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6174_: *mut LeanObject = core::ptr::null_mut();
    let mut v_infoState_6175_: *mut LeanObject = core::ptr::null_mut();
    let mut v_trees_6176_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6177_: *mut LeanObject = core::ptr::null_mut();
    let mut v_infoState_6178_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_6179_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_6180_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ngen_6181_: *mut LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_6182_: *mut LeanObject = core::ptr::null_mut();
    let mut v_traceState_6183_: *mut LeanObject = core::ptr::null_mut();
    let mut v_cache_6184_: *mut LeanObject = core::ptr::null_mut();
    let mut v_messages_6185_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_6186_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6188_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6189_: u8 = 0;
    let mut v_enabled_6190_: u8 = 0;
    let mut v_assignment_6191_: *mut LeanObject = core::ptr::null_mut();
    let mut v_lazyAssignment_6192_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6194_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6195_: u8 = 0;
    let mut v___x_6196_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6198_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6200_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6201_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6202_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6203_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6204_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6205_: u8 = 0;
    let mut v_unused_6206_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6207_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_6174_ = lean_st_ref_get(v___y_6172_);
                v_infoState_6175_ = lean_ctor_get(v___x_6174_, 7);
                lean_inc_ref(v_infoState_6175_);
                lean_dec(v___x_6174_);
                v_trees_6176_ = lean_ctor_get(v_infoState_6175_, 2);
                lean_inc_ref(v_trees_6176_);
                lean_dec_ref(v_infoState_6175_);
                v___x_6177_ = lean_st_ref_take(v___y_6172_);
                v_infoState_6178_ = lean_ctor_get(v___x_6177_, 7);
                v_env_6179_ = lean_ctor_get(v___x_6177_, 0);
                v_nextMacroScope_6180_ = lean_ctor_get(v___x_6177_, 1);
                v_ngen_6181_ = lean_ctor_get(v___x_6177_, 2);
                v_auxDeclNGen_6182_ = lean_ctor_get(v___x_6177_, 3);
                v_traceState_6183_ = lean_ctor_get(v___x_6177_, 4);
                v_cache_6184_ = lean_ctor_get(v___x_6177_, 5);
                v_messages_6185_ = lean_ctor_get(v___x_6177_, 6);
                v_snapshotTasks_6186_ = lean_ctor_get(v___x_6177_, 8);
                v_isSharedCheck_6207_ = (!lean_is_exclusive(v___x_6177_)) as u8;
                if v_isSharedCheck_6207_ == 0 {
                    v___x_6188_ = v___x_6177_;
                    v_isShared_6189_ = v_isSharedCheck_6207_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_snapshotTasks_6186_);
                    lean_inc(v_infoState_6178_);
                    lean_inc(v_messages_6185_);
                    lean_inc(v_cache_6184_);
                    lean_inc(v_traceState_6183_);
                    lean_inc(v_auxDeclNGen_6182_);
                    lean_inc(v_ngen_6181_);
                    lean_inc(v_nextMacroScope_6180_);
                    lean_inc(v_env_6179_);
                    lean_dec(v___x_6177_);
                    v___x_6188_ = lean_box(0);
                    v_isShared_6189_ = v_isSharedCheck_6207_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_enabled_6190_ = lean_ctor_get_uint8(
                    v_infoState_6178_,
                    (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
                );
                v_assignment_6191_ = lean_ctor_get(v_infoState_6178_, 0);
                v_lazyAssignment_6192_ = lean_ctor_get(v_infoState_6178_, 1);
                v_isSharedCheck_6205_ = (!lean_is_exclusive(v_infoState_6178_)) as u8;
                if v_isSharedCheck_6205_ == 0 {
                    v_unused_6206_ = lean_ctor_get(v_infoState_6178_, 2);
                    lean_dec(v_unused_6206_);
                    v___x_6194_ = v_infoState_6178_;
                    v_isShared_6195_ = v_isSharedCheck_6205_;
                    state = 2;
                    continue;
                } else {
                    lean_inc(v_lazyAssignment_6192_);
                    lean_inc(v_assignment_6191_);
                    lean_dec(v_infoState_6178_);
                    v___x_6194_ = lean_box(0);
                    v_isShared_6195_ = v_isSharedCheck_6205_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_6196_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_withRWRulesSeq_spec__0_spec__0___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_withRWRulesSeq_spec__0_spec__0___redArg___closed__1_once), _init_l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_withRWRulesSeq_spec__0_spec__0___redArg___closed__1);
                if v_isShared_6195_ == 0 {
                    lean_ctor_set(v___x_6194_, 2, v___x_6196_);
                    v___x_6198_ = v___x_6194_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_6204_ = lean_alloc_ctor(0, 3, (1) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6204_, 0, v_assignment_6191_);
                    lean_ctor_set(v_reuseFailAlloc_6204_, 1, v_lazyAssignment_6192_);
                    lean_ctor_set(v_reuseFailAlloc_6204_, 2, v___x_6196_);
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_6204_,
                        (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
                        v_enabled_6190_,
                    );
                    v___x_6198_ = v_reuseFailAlloc_6204_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_6189_ == 0 {
                    lean_ctor_set(v___x_6188_, 7, v___x_6198_);
                    v___x_6200_ = v___x_6188_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_6203_ = lean_alloc_ctor(0, 9, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6203_, 0, v_env_6179_);
                    lean_ctor_set(v_reuseFailAlloc_6203_, 1, v_nextMacroScope_6180_);
                    lean_ctor_set(v_reuseFailAlloc_6203_, 2, v_ngen_6181_);
                    lean_ctor_set(v_reuseFailAlloc_6203_, 3, v_auxDeclNGen_6182_);
                    lean_ctor_set(v_reuseFailAlloc_6203_, 4, v_traceState_6183_);
                    lean_ctor_set(v_reuseFailAlloc_6203_, 5, v_cache_6184_);
                    lean_ctor_set(v_reuseFailAlloc_6203_, 6, v_messages_6185_);
                    lean_ctor_set(v_reuseFailAlloc_6203_, 7, v___x_6198_);
                    lean_ctor_set(v_reuseFailAlloc_6203_, 8, v_snapshotTasks_6186_);
                    v___x_6200_ = v_reuseFailAlloc_6203_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_6201_ = lean_st_ref_set(v___y_6172_, v___x_6200_);
                v___x_6202_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_6202_, 0, v_trees_6176_);
                return v___x_6202_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_withRWRulesSeq_spec__0_spec__0___redArg___boxed(
    mut v___y_6208_: *mut LeanObject,
    mut v___y_6209_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6210_: *mut LeanObject = core::ptr::null_mut();
    v_res_6210_ = l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_withRWRulesSeq_spec__0_spec__0___redArg(v___y_6208_);
    lean_dec(v___y_6208_);
    return v_res_6210_;
}
pub unsafe fn l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_withRWRulesSeq_spec__0___redArg(
    mut v_x_6211_: *mut LeanObject,
    mut v_mkInfoTree_6212_: *mut LeanObject,
    mut v___y_6213_: *mut LeanObject,
    mut v___y_6214_: *mut LeanObject,
    mut v___y_6215_: *mut LeanObject,
    mut v___y_6216_: *mut LeanObject,
    mut v___y_6217_: *mut LeanObject,
    mut v___y_6218_: *mut LeanObject,
    mut v___y_6219_: *mut LeanObject,
    mut v___y_6220_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6222_: *mut LeanObject = core::ptr::null_mut();
    let mut v_infoState_6223_: *mut LeanObject = core::ptr::null_mut();
    let mut v_enabled_6224_: u8 = 0;
    let mut v___x_6225_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6226_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6227_: *mut LeanObject = core::ptr::null_mut();
    let mut v_r_6228_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6229_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6231_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6232_: u8 = 0;
    let mut v___x_6234_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6235_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6237_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6238_: u8 = 0;
    let mut v___x_6240_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6241_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6242_: u8 = 0;
    let mut v_unused_6243_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6244_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6246_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6247_: u8 = 0;
    let mut v___x_6249_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6250_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6251_: u8 = 0;
    let mut v_reuseFailAlloc_6252_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6253_: u8 = 0;
    let mut v_a_6254_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6255_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6256_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6258_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6259_: u8 = 0;
    let mut v___x_6261_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6262_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6263_: u8 = 0;
    let mut v_unused_6264_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6265_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6267_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6268_: u8 = 0;
    let mut v___x_6270_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6271_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6272_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_6222_ = lean_st_ref_get(v___y_6220_);
                v_infoState_6223_ = lean_ctor_get(v___x_6222_, 7);
                lean_inc_ref(v_infoState_6223_);
                lean_dec(v___x_6222_);
                v_enabled_6224_ = lean_ctor_get_uint8(
                    v_infoState_6223_,
                    (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
                );
                lean_dec_ref(v_infoState_6223_);
                if v_enabled_6224_ == 0 {
                    lean_dec_ref(v_mkInfoTree_6212_);
                    lean_inc(v___y_6220_);
                    lean_inc_ref(v___y_6219_);
                    lean_inc(v___y_6218_);
                    lean_inc_ref(v___y_6217_);
                    lean_inc(v___y_6216_);
                    lean_inc_ref(v___y_6215_);
                    lean_inc(v___y_6214_);
                    lean_inc_ref(v___y_6213_);
                    v___x_6225_ = lean_apply_9(
                        v_x_6211_,
                        v___y_6213_,
                        v___y_6214_,
                        v___y_6215_,
                        v___y_6216_,
                        v___y_6217_,
                        v___y_6218_,
                        v___y_6219_,
                        v___y_6220_,
                        lean_box(0),
                    );
                    return v___x_6225_;
                } else {
                    v___x_6226_ = l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_withRWRulesSeq_spec__0_spec__0___redArg(v___y_6220_);
                    v_a_6227_ = lean_ctor_get(v___x_6226_, 0);
                    lean_inc(v_a_6227_);
                    lean_dec_ref(v___x_6226_);
                    lean_inc(v___y_6220_);
                    lean_inc_ref(v___y_6219_);
                    lean_inc(v___y_6218_);
                    lean_inc_ref(v___y_6217_);
                    lean_inc(v___y_6216_);
                    lean_inc_ref(v___y_6215_);
                    lean_inc(v___y_6214_);
                    lean_inc_ref(v___y_6213_);
                    v_r_6228_ = lean_apply_9(
                        v_x_6211_,
                        v___y_6213_,
                        v___y_6214_,
                        v___y_6215_,
                        v___y_6216_,
                        v___y_6217_,
                        v___y_6218_,
                        v___y_6219_,
                        v___y_6220_,
                        lean_box(0),
                    );
                    if lean_obj_tag(v_r_6228_) == 0 {
                        v_a_6229_ = lean_ctor_get(v_r_6228_, 0);
                        v_isSharedCheck_6253_ = (!lean_is_exclusive(v_r_6228_)) as u8;
                        if v_isSharedCheck_6253_ == 0 {
                            v___x_6231_ = v_r_6228_;
                            v_isShared_6232_ = v_isSharedCheck_6253_;
                            state = 1;
                            continue;
                        } else {
                            lean_inc(v_a_6229_);
                            lean_dec(v_r_6228_);
                            v___x_6231_ = lean_box(0);
                            v_isShared_6232_ = v_isSharedCheck_6253_;
                            state = 1;
                            continue;
                        }
                    } else {
                        v_a_6254_ = lean_ctor_get(v_r_6228_, 0);
                        lean_inc(v_a_6254_);
                        lean_dec_ref_known(v_r_6228_, 1);
                        v___x_6255_ = lean_box(0);
                        v___x_6256_ = l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_withRWRulesSeq_spec__0___redArg___lam__0(v___y_6220_, v_mkInfoTree_6212_, v___y_6213_, v___y_6214_, v___y_6215_, v___y_6216_, v___y_6217_, v___y_6218_, v___y_6219_, v_a_6227_, v___x_6255_);
                        if lean_obj_tag(v___x_6256_) == 0 {
                            v_isSharedCheck_6263_ = (!lean_is_exclusive(v___x_6256_)) as u8;
                            if v_isSharedCheck_6263_ == 0 {
                                v_unused_6264_ = lean_ctor_get(v___x_6256_, 0);
                                lean_dec(v_unused_6264_);
                                v___x_6258_ = v___x_6256_;
                                v_isShared_6259_ = v_isSharedCheck_6263_;
                                state = 7;
                                continue;
                            } else {
                                lean_dec(v___x_6256_);
                                v___x_6258_ = lean_box(0);
                                v_isShared_6259_ = v_isSharedCheck_6263_;
                                state = 7;
                                continue;
                            }
                        } else {
                            lean_dec(v_a_6254_);
                            v_a_6265_ = lean_ctor_get(v___x_6256_, 0);
                            v_isSharedCheck_6272_ = (!lean_is_exclusive(v___x_6256_)) as u8;
                            if v_isSharedCheck_6272_ == 0 {
                                v___x_6267_ = v___x_6256_;
                                v_isShared_6268_ = v_isSharedCheck_6272_;
                                state = 9;
                                continue;
                            } else {
                                lean_inc(v_a_6265_);
                                lean_dec(v___x_6256_);
                                v___x_6267_ = lean_box(0);
                                v_isShared_6268_ = v_isSharedCheck_6272_;
                                state = 9;
                                continue;
                            }
                        }
                    }
                }
            }
            1 => {
                lean_inc(v_a_6229_);
                if v_isShared_6232_ == 0 {
                    lean_ctor_set_tag(v___x_6231_, 1);
                    v___x_6234_ = v___x_6231_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_6252_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6252_, 0, v_a_6229_);
                    v___x_6234_ = v_reuseFailAlloc_6252_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_6235_ = l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_withRWRulesSeq_spec__0___redArg___lam__0(v___y_6220_, v_mkInfoTree_6212_, v___y_6213_, v___y_6214_, v___y_6215_, v___y_6216_, v___y_6217_, v___y_6218_, v___y_6219_, v_a_6227_, v___x_6234_);
                lean_dec_ref(v___x_6234_);
                if lean_obj_tag(v___x_6235_) == 0 {
                    v_isSharedCheck_6242_ = (!lean_is_exclusive(v___x_6235_)) as u8;
                    if v_isSharedCheck_6242_ == 0 {
                        v_unused_6243_ = lean_ctor_get(v___x_6235_, 0);
                        lean_dec(v_unused_6243_);
                        v___x_6237_ = v___x_6235_;
                        v_isShared_6238_ = v_isSharedCheck_6242_;
                        state = 3;
                        continue;
                    } else {
                        lean_dec(v___x_6235_);
                        v___x_6237_ = lean_box(0);
                        v_isShared_6238_ = v_isSharedCheck_6242_;
                        state = 3;
                        continue;
                    }
                } else {
                    lean_dec(v_a_6229_);
                    v_a_6244_ = lean_ctor_get(v___x_6235_, 0);
                    v_isSharedCheck_6251_ = (!lean_is_exclusive(v___x_6235_)) as u8;
                    if v_isSharedCheck_6251_ == 0 {
                        v___x_6246_ = v___x_6235_;
                        v_isShared_6247_ = v_isSharedCheck_6251_;
                        state = 5;
                        continue;
                    } else {
                        lean_inc(v_a_6244_);
                        lean_dec(v___x_6235_);
                        v___x_6246_ = lean_box(0);
                        v_isShared_6247_ = v_isSharedCheck_6251_;
                        state = 5;
                        continue;
                    }
                }
            }
            3 => {
                if v_isShared_6238_ == 0 {
                    lean_ctor_set(v___x_6237_, 0, v_a_6229_);
                    v___x_6240_ = v___x_6237_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_6241_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6241_, 0, v_a_6229_);
                    v___x_6240_ = v_reuseFailAlloc_6241_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_6240_;
            }
            5 => {
                if v_isShared_6247_ == 0 {
                    v___x_6249_ = v___x_6246_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_6250_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6250_, 0, v_a_6244_);
                    v___x_6249_ = v_reuseFailAlloc_6250_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_6249_;
            }
            7 => {
                if v_isShared_6259_ == 0 {
                    lean_ctor_set_tag(v___x_6258_, 1);
                    lean_ctor_set(v___x_6258_, 0, v_a_6254_);
                    v___x_6261_ = v___x_6258_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_6262_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6262_, 0, v_a_6254_);
                    v___x_6261_ = v_reuseFailAlloc_6262_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_6261_;
            }
            9 => {
                if v_isShared_6268_ == 0 {
                    v___x_6270_ = v___x_6267_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_6271_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6271_, 0, v_a_6265_);
                    v___x_6270_ = v_reuseFailAlloc_6271_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_6270_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_withRWRulesSeq_spec__0___redArg___boxed(
    mut v_x_6273_: *mut LeanObject,
    mut v_mkInfoTree_6274_: *mut LeanObject,
    mut v___y_6275_: *mut LeanObject,
    mut v___y_6276_: *mut LeanObject,
    mut v___y_6277_: *mut LeanObject,
    mut v___y_6278_: *mut LeanObject,
    mut v___y_6279_: *mut LeanObject,
    mut v___y_6280_: *mut LeanObject,
    mut v___y_6281_: *mut LeanObject,
    mut v___y_6282_: *mut LeanObject,
    mut v___y_6283_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6284_: *mut LeanObject = core::ptr::null_mut();
    v_res_6284_ =
        l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_withRWRulesSeq_spec__0___redArg(
            v_x_6273_,
            v_mkInfoTree_6274_,
            v___y_6275_,
            v___y_6276_,
            v___y_6277_,
            v___y_6278_,
            v___y_6279_,
            v___y_6280_,
            v___y_6281_,
            v___y_6282_,
        );
    lean_dec(v___y_6282_);
    lean_dec_ref(v___y_6281_);
    lean_dec(v___y_6280_);
    lean_dec_ref(v___y_6279_);
    lean_dec(v___y_6278_);
    lean_dec_ref(v___y_6277_);
    lean_dec(v___y_6276_);
    lean_dec_ref(v___y_6275_);
    return v_res_6284_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_withRWRulesSeq_spec__1___redArg___lam__3(
    mut v___x_6294_: *mut LeanObject,
    mut v___x_6295_: u8,
    mut v___x_6296_: *mut LeanObject,
    mut v_x_6297_: *mut LeanObject,
    mut v___y_6298_: u8,
    mut v___x_6299_: *mut LeanObject,
    mut v___x_6300_: *mut LeanObject,
    mut v___f_6301_: *mut LeanObject,
    mut v___y_6302_: *mut LeanObject,
    mut v___y_6303_: *mut LeanObject,
    mut v___y_6304_: *mut LeanObject,
    mut v___y_6305_: *mut LeanObject,
    mut v___y_6306_: *mut LeanObject,
    mut v___y_6307_: *mut LeanObject,
    mut v___y_6308_: *mut LeanObject,
    mut v___y_6309_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_fileName_6311_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fileMap_6312_: *mut LeanObject = core::ptr::null_mut();
    let mut v_options_6313_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currRecDepth_6314_: *mut LeanObject = core::ptr::null_mut();
    let mut v_maxRecDepth_6315_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ref_6316_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currNamespace_6317_: *mut LeanObject = core::ptr::null_mut();
    let mut v_openDecls_6318_: *mut LeanObject = core::ptr::null_mut();
    let mut v_initHeartbeats_6319_: *mut LeanObject = core::ptr::null_mut();
    let mut v_maxHeartbeats_6320_: *mut LeanObject = core::ptr::null_mut();
    let mut v_quotContext_6321_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currMacroScope_6322_: *mut LeanObject = core::ptr::null_mut();
    let mut v_diag_6323_: u8 = 0;
    let mut v_cancelTk_x3f_6324_: *mut LeanObject = core::ptr::null_mut();
    let mut v_suppressElabErrors_6325_: u8 = 0;
    let mut v_inheritedTraceOptions_6326_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6328_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6329_: u8 = 0;
    let mut v_ref_6330_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6332_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6333_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6334_: u8 = 0;
    let mut v___x_6335_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6336_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6337_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6338_: u8 = 0;
    let mut v___x_6339_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6340_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6341_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6342_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6343_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6344_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_fileName_6311_ = lean_ctor_get(v___y_6308_, 0);
                v_fileMap_6312_ = lean_ctor_get(v___y_6308_, 1);
                v_options_6313_ = lean_ctor_get(v___y_6308_, 2);
                v_currRecDepth_6314_ = lean_ctor_get(v___y_6308_, 3);
                v_maxRecDepth_6315_ = lean_ctor_get(v___y_6308_, 4);
                v_ref_6316_ = lean_ctor_get(v___y_6308_, 5);
                v_currNamespace_6317_ = lean_ctor_get(v___y_6308_, 6);
                v_openDecls_6318_ = lean_ctor_get(v___y_6308_, 7);
                v_initHeartbeats_6319_ = lean_ctor_get(v___y_6308_, 8);
                v_maxHeartbeats_6320_ = lean_ctor_get(v___y_6308_, 9);
                v_quotContext_6321_ = lean_ctor_get(v___y_6308_, 10);
                v_currMacroScope_6322_ = lean_ctor_get(v___y_6308_, 11);
                v_diag_6323_ = lean_ctor_get_uint8(
                    v___y_6308_,
                    (core::mem::size_of::<*mut LeanObject>() * 14) as u32,
                );
                v_cancelTk_x3f_6324_ = lean_ctor_get(v___y_6308_, 12);
                v_suppressElabErrors_6325_ = lean_ctor_get_uint8(
                    v___y_6308_,
                    (core::mem::size_of::<*mut LeanObject>() * 14 + 1) as u32,
                );
                v_inheritedTraceOptions_6326_ = lean_ctor_get(v___y_6308_, 13);
                v_isSharedCheck_6344_ = (!lean_is_exclusive(v___y_6308_)) as u8;
                if v_isSharedCheck_6344_ == 0 {
                    v___x_6328_ = v___y_6308_;
                    v_isShared_6329_ = v_isSharedCheck_6344_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_inheritedTraceOptions_6326_);
                    lean_inc(v_cancelTk_x3f_6324_);
                    lean_inc(v_currMacroScope_6322_);
                    lean_inc(v_quotContext_6321_);
                    lean_inc(v_maxHeartbeats_6320_);
                    lean_inc(v_initHeartbeats_6319_);
                    lean_inc(v_openDecls_6318_);
                    lean_inc(v_currNamespace_6317_);
                    lean_inc(v_ref_6316_);
                    lean_inc(v_maxRecDepth_6315_);
                    lean_inc(v_currRecDepth_6314_);
                    lean_inc(v_options_6313_);
                    lean_inc(v_fileMap_6312_);
                    lean_inc(v_fileName_6311_);
                    lean_dec(v___y_6308_);
                    v___x_6328_ = lean_box(0);
                    v_isShared_6329_ = v_isSharedCheck_6344_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_ref_6330_ = l_Lean_replaceRef(v___x_6294_, v_ref_6316_);
                lean_dec(v_ref_6316_);
                if v_isShared_6329_ == 0 {
                    lean_ctor_set(v___x_6328_, 5, v_ref_6330_);
                    v___x_6332_ = v___x_6328_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_6343_ = lean_alloc_ctor(0, 14, (2) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6343_, 0, v_fileName_6311_);
                    lean_ctor_set(v_reuseFailAlloc_6343_, 1, v_fileMap_6312_);
                    lean_ctor_set(v_reuseFailAlloc_6343_, 2, v_options_6313_);
                    lean_ctor_set(v_reuseFailAlloc_6343_, 3, v_currRecDepth_6314_);
                    lean_ctor_set(v_reuseFailAlloc_6343_, 4, v_maxRecDepth_6315_);
                    lean_ctor_set(v_reuseFailAlloc_6343_, 5, v_ref_6330_);
                    lean_ctor_set(v_reuseFailAlloc_6343_, 6, v_currNamespace_6317_);
                    lean_ctor_set(v_reuseFailAlloc_6343_, 7, v_openDecls_6318_);
                    lean_ctor_set(v_reuseFailAlloc_6343_, 8, v_initHeartbeats_6319_);
                    lean_ctor_set(v_reuseFailAlloc_6343_, 9, v_maxHeartbeats_6320_);
                    lean_ctor_set(v_reuseFailAlloc_6343_, 10, v_quotContext_6321_);
                    lean_ctor_set(v_reuseFailAlloc_6343_, 11, v_currMacroScope_6322_);
                    lean_ctor_set(v_reuseFailAlloc_6343_, 12, v_cancelTk_x3f_6324_);
                    lean_ctor_set(v_reuseFailAlloc_6343_, 13, v_inheritedTraceOptions_6326_);
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_6343_,
                        (core::mem::size_of::<*mut LeanObject>() * 14) as u32,
                        v_diag_6323_,
                    );
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_6343_,
                        (core::mem::size_of::<*mut LeanObject>() * 14 + 1) as u32,
                        v_suppressElabErrors_6325_,
                    );
                    v___x_6332_ = v_reuseFailAlloc_6343_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                if v___x_6295_ == 0 {
                    v___x_6333_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_withRWRulesSeq_spec__1___redArg___lam__3___closed__4;
                    lean_inc(v___x_6296_);
                    v___x_6334_ = l_Lean_Syntax_isOfKind(v___x_6296_, v___x_6333_);
                    if v___x_6334_ == 0 {
                        lean_dec_ref(v___f_6301_);
                        v___x_6335_ = lean_box((v___y_6298_) as usize);
                        v___x_6336_ = lean_apply_11(
                            v_x_6297_,
                            v___x_6335_,
                            v___x_6296_,
                            v___y_6302_,
                            v___y_6303_,
                            v___y_6304_,
                            v___y_6305_,
                            v___y_6306_,
                            v___y_6307_,
                            v___x_6332_,
                            v___y_6309_,
                            lean_box(0),
                        );
                        return v___x_6336_;
                    } else {
                        v___x_6337_ = l_Lean_Syntax_getArg(v___x_6296_, v___x_6299_);
                        lean_inc(v___x_6337_);
                        v___x_6338_ = l_Lean_Syntax_isOfKind(v___x_6337_, v___x_6300_);
                        if v___x_6338_ == 0 {
                            lean_dec(v___x_6337_);
                            lean_dec_ref(v___f_6301_);
                            v___x_6339_ = lean_box((v___y_6298_) as usize);
                            v___x_6340_ = lean_apply_11(
                                v_x_6297_,
                                v___x_6339_,
                                v___x_6296_,
                                v___y_6302_,
                                v___y_6303_,
                                v___y_6304_,
                                v___y_6305_,
                                v___y_6306_,
                                v___y_6307_,
                                v___x_6332_,
                                v___y_6309_,
                                lean_box(0),
                            );
                            return v___x_6340_;
                        } else {
                            lean_dec_ref(v_x_6297_);
                            lean_dec(v___x_6296_);
                            v___x_6341_ = lean_apply_10(
                                v___f_6301_,
                                v___x_6337_,
                                v___y_6302_,
                                v___y_6303_,
                                v___y_6304_,
                                v___y_6305_,
                                v___y_6306_,
                                v___y_6307_,
                                v___x_6332_,
                                v___y_6309_,
                                lean_box(0),
                            );
                            return v___x_6341_;
                        }
                    }
                } else {
                    lean_dec_ref(v_x_6297_);
                    v___x_6342_ = lean_apply_10(
                        v___f_6301_,
                        v___x_6296_,
                        v___y_6302_,
                        v___y_6303_,
                        v___y_6304_,
                        v___y_6305_,
                        v___y_6306_,
                        v___y_6307_,
                        v___x_6332_,
                        v___y_6309_,
                        lean_box(0),
                    );
                    return v___x_6342_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_withRWRulesSeq_spec__1___redArg___lam__3___boxed(
    _args: *mut *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6345_: *mut LeanObject = *_args.add(0);
    let mut v___x_6346_: *mut LeanObject = *_args.add(1);
    let mut v___x_6347_: *mut LeanObject = *_args.add(2);
    let mut v_x_6348_: *mut LeanObject = *_args.add(3);
    let mut v___y_6349_: *mut LeanObject = *_args.add(4);
    let mut v___x_6350_: *mut LeanObject = *_args.add(5);
    let mut v___x_6351_: *mut LeanObject = *_args.add(6);
    let mut v___f_6352_: *mut LeanObject = *_args.add(7);
    let mut v___y_6353_: *mut LeanObject = *_args.add(8);
    let mut v___y_6354_: *mut LeanObject = *_args.add(9);
    let mut v___y_6355_: *mut LeanObject = *_args.add(10);
    let mut v___y_6356_: *mut LeanObject = *_args.add(11);
    let mut v___y_6357_: *mut LeanObject = *_args.add(12);
    let mut v___y_6358_: *mut LeanObject = *_args.add(13);
    let mut v___y_6359_: *mut LeanObject = *_args.add(14);
    let mut v___y_6360_: *mut LeanObject = *_args.add(15);
    let mut v___y_6361_: *mut LeanObject = *_args.add(16);
    let mut v___x_16685__boxed_6362_: u8 = 0;
    let mut v___y_16687__boxed_6363_: u8 = 0;
    let mut v_res_6364_: *mut LeanObject = core::ptr::null_mut();
    v___x_16685__boxed_6362_ = (lean_unbox(v___x_6346_) as u8);
    v___y_16687__boxed_6363_ = (lean_unbox(v___y_6349_) as u8);
    v_res_6364_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_withRWRulesSeq_spec__1___redArg___lam__3(v___x_6345_, v___x_16685__boxed_6362_, v___x_6347_, v_x_6348_, v___y_16687__boxed_6363_, v___x_6350_, v___x_6351_, v___f_6352_, v___y_6353_, v___y_6354_, v___y_6355_, v___y_6356_, v___y_6357_, v___y_6358_, v___y_6359_, v___y_6360_);
    lean_dec(v___x_6351_);
    lean_dec(v___x_6350_);
    lean_dec(v___x_6345_);
    return v_res_6364_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_withRWRulesSeq_spec__1___redArg___lam__0(
    mut v_a_6365_: *mut LeanObject,
    mut v_trees_6366_: *mut LeanObject,
    mut v___y_6367_: *mut LeanObject,
    mut v___y_6368_: *mut LeanObject,
    mut v___y_6369_: *mut LeanObject,
    mut v___y_6370_: *mut LeanObject,
    mut v___y_6371_: *mut LeanObject,
    mut v___y_6372_: *mut LeanObject,
    mut v___y_6373_: *mut LeanObject,
    mut v___y_6374_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6376_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6377_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6379_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6380_: u8 = 0;
    let mut v___x_6381_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6383_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6384_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6385_: u8 = 0;
    let mut v_a_6386_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6388_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6389_: u8 = 0;
    let mut v___x_6391_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6392_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6393_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                lean_inc(v___y_6374_);
                lean_inc_ref(v___y_6373_);
                lean_inc(v___y_6372_);
                lean_inc_ref(v___y_6371_);
                lean_inc(v___y_6370_);
                lean_inc_ref(v___y_6369_);
                lean_inc(v___y_6368_);
                lean_inc_ref(v___y_6367_);
                v___x_6376_ = lean_apply_9(
                    v_a_6365_,
                    v___y_6367_,
                    v___y_6368_,
                    v___y_6369_,
                    v___y_6370_,
                    v___y_6371_,
                    v___y_6372_,
                    v___y_6373_,
                    v___y_6374_,
                    lean_box(0),
                );
                if lean_obj_tag(v___x_6376_) == 0 {
                    v_a_6377_ = lean_ctor_get(v___x_6376_, 0);
                    v_isSharedCheck_6385_ = (!lean_is_exclusive(v___x_6376_)) as u8;
                    if v_isSharedCheck_6385_ == 0 {
                        v___x_6379_ = v___x_6376_;
                        v_isShared_6380_ = v_isSharedCheck_6385_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_6377_);
                        lean_dec(v___x_6376_);
                        v___x_6379_ = lean_box(0);
                        v_isShared_6380_ = v_isSharedCheck_6385_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec_ref(v_trees_6366_);
                    v_a_6386_ = lean_ctor_get(v___x_6376_, 0);
                    v_isSharedCheck_6393_ = (!lean_is_exclusive(v___x_6376_)) as u8;
                    if v_isSharedCheck_6393_ == 0 {
                        v___x_6388_ = v___x_6376_;
                        v_isShared_6389_ = v_isSharedCheck_6393_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_6386_);
                        lean_dec(v___x_6376_);
                        v___x_6388_ = lean_box(0);
                        v_isShared_6389_ = v_isSharedCheck_6393_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v___x_6381_ = lean_alloc_ctor(1, 2, (0) as u32);
                lean_ctor_set(v___x_6381_, 0, v_a_6377_);
                lean_ctor_set(v___x_6381_, 1, v_trees_6366_);
                if v_isShared_6380_ == 0 {
                    lean_ctor_set(v___x_6379_, 0, v___x_6381_);
                    v___x_6383_ = v___x_6379_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_6384_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6384_, 0, v___x_6381_);
                    v___x_6383_ = v_reuseFailAlloc_6384_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_6383_;
            }
            3 => {
                if v_isShared_6389_ == 0 {
                    v___x_6391_ = v___x_6388_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_6392_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6392_, 0, v_a_6386_);
                    v___x_6391_ = v_reuseFailAlloc_6392_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_6391_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_withRWRulesSeq_spec__1___redArg___lam__0___boxed(
    mut v_a_6394_: *mut LeanObject,
    mut v_trees_6395_: *mut LeanObject,
    mut v___y_6396_: *mut LeanObject,
    mut v___y_6397_: *mut LeanObject,
    mut v___y_6398_: *mut LeanObject,
    mut v___y_6399_: *mut LeanObject,
    mut v___y_6400_: *mut LeanObject,
    mut v___y_6401_: *mut LeanObject,
    mut v___y_6402_: *mut LeanObject,
    mut v___y_6403_: *mut LeanObject,
    mut v___y_6404_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6405_: *mut LeanObject = core::ptr::null_mut();
    v_res_6405_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_withRWRulesSeq_spec__1___redArg___lam__0(v_a_6394_, v_trees_6395_, v___y_6396_, v___y_6397_, v___y_6398_, v___y_6399_, v___y_6400_, v___y_6401_, v___y_6402_, v___y_6403_);
    lean_dec(v___y_6403_);
    lean_dec_ref(v___y_6402_);
    lean_dec(v___y_6401_);
    lean_dec_ref(v___y_6400_);
    lean_dec(v___y_6399_);
    lean_dec_ref(v___y_6398_);
    lean_dec(v___y_6397_);
    lean_dec_ref(v___y_6396_);
    return v_res_6405_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_withRWRulesSeq_spec__1___redArg___lam__1(
    mut v_id_6406_: *mut LeanObject,
    mut v___y_6407_: *mut LeanObject,
    mut v___y_6408_: *mut LeanObject,
    mut v___y_6409_: *mut LeanObject,
    mut v___y_6410_: *mut LeanObject,
    mut v___y_6411_: *mut LeanObject,
    mut v___y_6412_: *mut LeanObject,
    mut v___y_6413_: *mut LeanObject,
    mut v___y_6414_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6416_: *mut LeanObject = core::ptr::null_mut();
    v___x_6416_ = l_Lean_Elab_Term_isLocalIdent_x3f(
        v_id_6406_,
        v___y_6409_,
        v___y_6410_,
        v___y_6411_,
        v___y_6412_,
        v___y_6413_,
        v___y_6414_,
    );
    return v___x_6416_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_withRWRulesSeq_spec__1___redArg___lam__1___boxed(
    mut v_id_6417_: *mut LeanObject,
    mut v___y_6418_: *mut LeanObject,
    mut v___y_6419_: *mut LeanObject,
    mut v___y_6420_: *mut LeanObject,
    mut v___y_6421_: *mut LeanObject,
    mut v___y_6422_: *mut LeanObject,
    mut v___y_6423_: *mut LeanObject,
    mut v___y_6424_: *mut LeanObject,
    mut v___y_6425_: *mut LeanObject,
    mut v___y_6426_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6427_: *mut LeanObject = core::ptr::null_mut();
    v_res_6427_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_withRWRulesSeq_spec__1___redArg___lam__1(v_id_6417_, v___y_6418_, v___y_6419_, v___y_6420_, v___y_6421_, v___y_6422_, v___y_6423_, v___y_6424_, v___y_6425_);
    lean_dec(v___y_6425_);
    lean_dec_ref(v___y_6424_);
    lean_dec(v___y_6423_);
    lean_dec_ref(v___y_6422_);
    lean_dec(v___y_6421_);
    lean_dec_ref(v___y_6420_);
    lean_dec(v___y_6419_);
    lean_dec_ref(v___y_6418_);
    return v_res_6427_;
}
pub unsafe fn _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_withRWRulesSeq_spec__1___redArg___lam__2___closed__1()
-> *mut LeanObject {
    let mut v___x_6429_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6430_: *mut LeanObject = core::ptr::null_mut();
    v___x_6429_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_withRWRulesSeq_spec__1___redArg___lam__2___closed__0;
    v___x_6430_ = l_Lean_stringToMessageData(v___x_6429_);
    return v___x_6430_;
}
pub unsafe fn _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_withRWRulesSeq_spec__1___redArg___lam__2___closed__3()
-> *mut LeanObject {
    let mut v___x_6432_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6433_: *mut LeanObject = core::ptr::null_mut();
    v___x_6432_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_withRWRulesSeq_spec__1___redArg___lam__2___closed__2;
    v___x_6433_ = l_Lean_stringToMessageData(v___x_6432_);
    return v___x_6433_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_withRWRulesSeq_spec__1___redArg___lam__2(
    mut v_x_6434_: *mut LeanObject,
    mut v___y_6435_: u8,
    mut v___x_6436_: *mut LeanObject,
    mut v___x_6437_: *mut LeanObject,
    mut v_id_6438_: *mut LeanObject,
    mut v___y_6439_: *mut LeanObject,
    mut v___y_6440_: *mut LeanObject,
    mut v___y_6441_: *mut LeanObject,
    mut v___y_6442_: *mut LeanObject,
    mut v___y_6443_: *mut LeanObject,
    mut v___y_6444_: *mut LeanObject,
    mut v___y_6445_: *mut LeanObject,
    mut v___y_6446_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_6448_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6449_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6450_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6451_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6452_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6453_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6454_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6455_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6456_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_6457_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6459_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6460_: u8 = 0;
    let mut v___x_6461_: u8 = 0;
    let mut v___y_6463_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6464_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6465_: *mut LeanObject = core::ptr::null_mut();
    let mut v_lctx_6466_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6468_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6469_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6470_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6471_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6472_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6473_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6475_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6476_: u8 = 0;
    let mut v___x_6478_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6479_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6480_: u8 = 0;
    let mut v_reuseFailAlloc_6481_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6482_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6484_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6485_: u8 = 0;
    let mut v___x_6487_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6488_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6489_: u8 = 0;
    let mut v___x_6490_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6491_: u8 = 0;
    let mut v___x_6492_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6493_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6494_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6495_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6496_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6497_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6498_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6499_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6500_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6501_: u8 = 0;
    let mut v___x_6502_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6503_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6504_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6506_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6507_: u8 = 0;
    let mut v___x_6509_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6510_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6511_: u8 = 0;
    let mut v_a_6512_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6514_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6515_: u8 = 0;
    let mut v___y_6517_: u8 = 0;
    let mut v___x_6518_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6519_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6520_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6522_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6523_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6524_: u8 = 0;
    let mut v___x_6525_: u8 = 0;
    let mut v_isSharedCheck_6526_: u8 = 0;
    let mut v_a_6527_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6529_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6530_: u8 = 0;
    let mut v___x_6532_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6533_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6534_: u8 = 0;
    let mut v___x_6535_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6536_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6537_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6539_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6540_: u8 = 0;
    let mut v___x_6542_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6543_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6544_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                lean_inc(v_id_6438_);
                v___f_6448_ = lean_alloc_closure(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_withRWRulesSeq_spec__1___redArg___lam__1___boxed as *mut core::ffi::c_void, 10, 1);
                lean_closure_set(v___f_6448_, 0, v_id_6438_);
                v___x_6449_ = l_Lean_Elab_Tactic_withMainContext___redArg(
                    v___f_6448_,
                    v___y_6439_,
                    v___y_6440_,
                    v___y_6441_,
                    v___y_6442_,
                    v___y_6443_,
                    v___y_6444_,
                    v___y_6445_,
                    v___y_6446_,
                );
                if lean_obj_tag(v___x_6449_) == 0 {
                    v_a_6450_ = lean_ctor_get(v___x_6449_, 0);
                    lean_inc(v_a_6450_);
                    lean_dec_ref_known(v___x_6449_, 1);
                    if lean_obj_tag(v_a_6450_) == 0 {
                        v___x_6451_ = l_Lean_Elab_Tactic_saveState___redArg(
                            v___y_6440_,
                            v___y_6442_,
                            v___y_6444_,
                            v___y_6446_,
                        );
                        if lean_obj_tag(v___x_6451_) == 0 {
                            v_a_6452_ = lean_ctor_get(v___x_6451_, 0);
                            lean_inc(v_a_6452_);
                            lean_dec_ref_known(v___x_6451_, 1);
                            lean_inc(v_id_6438_);
                            v___x_6453_ = l_Lean_realizeGlobalConstNoOverload(
                                v_id_6438_,
                                v___y_6445_,
                                v___y_6446_,
                            );
                            if lean_obj_tag(v___x_6453_) == 0 {
                                lean_dec(v_a_6452_);
                                v_a_6454_ = lean_ctor_get(v___x_6453_, 0);
                                lean_inc_n(v_a_6454_, 2);
                                lean_dec_ref_known(v___x_6453_, 1);
                                v___x_6455_ = l_Lean_Meta_getEqnsFor_x3f(
                                    v_a_6454_,
                                    v___y_6443_,
                                    v___y_6444_,
                                    v___y_6445_,
                                    v___y_6446_,
                                );
                                if lean_obj_tag(v___x_6455_) == 0 {
                                    v_a_6456_ = lean_ctor_get(v___x_6455_, 0);
                                    lean_inc(v_a_6456_);
                                    lean_dec_ref_known(v___x_6455_, 1);
                                    if lean_obj_tag(v_a_6456_) == 1 {
                                        lean_dec(v___x_6437_);
                                        v_val_6457_ = lean_ctor_get(v_a_6456_, 0);
                                        v_isSharedCheck_6501_ =
                                            (!lean_is_exclusive(v_a_6456_)) as u8;
                                        if v_isSharedCheck_6501_ == 0 {
                                            v___x_6459_ = v_a_6456_;
                                            v_isShared_6460_ = v_isSharedCheck_6501_;
                                            state = 1;
                                            continue;
                                        } else {
                                            lean_inc(v_val_6457_);
                                            lean_dec(v_a_6456_);
                                            v___x_6459_ = lean_box(0);
                                            v_isShared_6460_ = v_isSharedCheck_6501_;
                                            state = 1;
                                            continue;
                                        }
                                    } else {
                                        lean_dec(v_a_6456_);
                                        lean_dec(v_a_6454_);
                                        lean_dec(v_id_6438_);
                                        v___x_6502_ = lean_box((v___y_6435_) as usize);
                                        lean_inc(v___y_6446_);
                                        lean_inc_ref(v___y_6445_);
                                        lean_inc(v___y_6444_);
                                        lean_inc_ref(v___y_6443_);
                                        lean_inc(v___y_6442_);
                                        lean_inc_ref(v___y_6441_);
                                        lean_inc(v___y_6440_);
                                        lean_inc_ref(v___y_6439_);
                                        v___x_6503_ = lean_apply_11(
                                            v_x_6434_,
                                            v___x_6502_,
                                            v___x_6437_,
                                            v___y_6439_,
                                            v___y_6440_,
                                            v___y_6441_,
                                            v___y_6442_,
                                            v___y_6443_,
                                            v___y_6444_,
                                            v___y_6445_,
                                            v___y_6446_,
                                            lean_box(0),
                                        );
                                        return v___x_6503_;
                                    }
                                } else {
                                    lean_dec(v_a_6454_);
                                    lean_dec(v_id_6438_);
                                    lean_dec(v___x_6437_);
                                    lean_dec_ref(v_x_6434_);
                                    v_a_6504_ = lean_ctor_get(v___x_6455_, 0);
                                    v_isSharedCheck_6511_ = (!lean_is_exclusive(v___x_6455_)) as u8;
                                    if v_isSharedCheck_6511_ == 0 {
                                        v___x_6506_ = v___x_6455_;
                                        v_isShared_6507_ = v_isSharedCheck_6511_;
                                        state = 8;
                                        continue;
                                    } else {
                                        lean_inc(v_a_6504_);
                                        lean_dec(v___x_6455_);
                                        v___x_6506_ = lean_box(0);
                                        v_isShared_6507_ = v_isSharedCheck_6511_;
                                        state = 8;
                                        continue;
                                    }
                                }
                            } else {
                                lean_dec(v_id_6438_);
                                v_a_6512_ = lean_ctor_get(v___x_6453_, 0);
                                v_isSharedCheck_6526_ = (!lean_is_exclusive(v___x_6453_)) as u8;
                                if v_isSharedCheck_6526_ == 0 {
                                    v___x_6514_ = v___x_6453_;
                                    v_isShared_6515_ = v_isSharedCheck_6526_;
                                    state = 10;
                                    continue;
                                } else {
                                    lean_inc(v_a_6512_);
                                    lean_dec(v___x_6453_);
                                    v___x_6514_ = lean_box(0);
                                    v_isShared_6515_ = v_isSharedCheck_6526_;
                                    state = 10;
                                    continue;
                                }
                            }
                        } else {
                            lean_dec(v_id_6438_);
                            lean_dec(v___x_6437_);
                            lean_dec_ref(v_x_6434_);
                            v_a_6527_ = lean_ctor_get(v___x_6451_, 0);
                            v_isSharedCheck_6534_ = (!lean_is_exclusive(v___x_6451_)) as u8;
                            if v_isSharedCheck_6534_ == 0 {
                                v___x_6529_ = v___x_6451_;
                                v_isShared_6530_ = v_isSharedCheck_6534_;
                                state = 13;
                                continue;
                            } else {
                                lean_inc(v_a_6527_);
                                lean_dec(v___x_6451_);
                                v___x_6529_ = lean_box(0);
                                v_isShared_6530_ = v_isSharedCheck_6534_;
                                state = 13;
                                continue;
                            }
                        }
                    } else {
                        lean_dec_ref_known(v_a_6450_, 1);
                        lean_dec(v_id_6438_);
                        v___x_6535_ = lean_box((v___y_6435_) as usize);
                        lean_inc(v___y_6446_);
                        lean_inc_ref(v___y_6445_);
                        lean_inc(v___y_6444_);
                        lean_inc_ref(v___y_6443_);
                        lean_inc(v___y_6442_);
                        lean_inc_ref(v___y_6441_);
                        lean_inc(v___y_6440_);
                        lean_inc_ref(v___y_6439_);
                        v___x_6536_ = lean_apply_11(
                            v_x_6434_,
                            v___x_6535_,
                            v___x_6437_,
                            v___y_6439_,
                            v___y_6440_,
                            v___y_6441_,
                            v___y_6442_,
                            v___y_6443_,
                            v___y_6444_,
                            v___y_6445_,
                            v___y_6446_,
                            lean_box(0),
                        );
                        return v___x_6536_;
                    }
                } else {
                    lean_dec(v_id_6438_);
                    lean_dec(v___x_6437_);
                    lean_dec_ref(v_x_6434_);
                    v_a_6537_ = lean_ctor_get(v___x_6449_, 0);
                    v_isSharedCheck_6544_ = (!lean_is_exclusive(v___x_6449_)) as u8;
                    if v_isSharedCheck_6544_ == 0 {
                        v___x_6539_ = v___x_6449_;
                        v_isShared_6540_ = v_isSharedCheck_6544_;
                        state = 15;
                        continue;
                    } else {
                        lean_inc(v_a_6537_);
                        lean_dec(v___x_6449_);
                        v___x_6539_ = lean_box(0);
                        v_isShared_6540_ = v_isSharedCheck_6544_;
                        state = 15;
                        continue;
                    }
                }
            }
            1 => {
                v___x_6461_ = 0;
                v___x_6490_ = lean_array_get_size(v_val_6457_);
                v___x_6491_ = lean_nat_dec_eq(v___x_6490_, v___x_6436_);
                if v___x_6491_ == 0 {
                    v___x_6492_ = lean_obj_once(core::ptr::addr_of_mut!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_withRWRulesSeq_spec__1___redArg___lam__2___closed__1), core::ptr::addr_of_mut!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_withRWRulesSeq_spec__1___redArg___lam__2___closed__1_once), _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_withRWRulesSeq_spec__1___redArg___lam__2___closed__1);
                    v___x_6493_ = l_Lean_Meta_unfoldThmSuffix;
                    lean_inc(v_a_6454_);
                    v___x_6494_ = l_Lean_Name_str___override(v_a_6454_, v___x_6493_);
                    v___x_6495_ = l_Lean_MessageData_ofName(v___x_6494_);
                    v___x_6496_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_6496_, 0, v___x_6492_);
                    lean_ctor_set(v___x_6496_, 1, v___x_6495_);
                    v___x_6497_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_withRWRulesSeq_go___closed__3), core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_withRWRulesSeq_go___closed__3_once), _init_l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_withRWRulesSeq_go___closed__3);
                    v___x_6498_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_6498_, 0, v___x_6496_);
                    lean_ctor_set(v___x_6498_, 1, v___x_6497_);
                    v___x_6499_ = l_Lean_MessageData_hint_x27(v___x_6498_);
                    v___y_6463_ = v___x_6499_;
                    state = 2;
                    continue;
                } else {
                    v___x_6500_ = lean_obj_once(core::ptr::addr_of_mut!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_withRWRulesSeq_spec__1___redArg___lam__2___closed__3), core::ptr::addr_of_mut!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_withRWRulesSeq_spec__1___redArg___lam__2___closed__3_once), _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_withRWRulesSeq_spec__1___redArg___lam__2___closed__3);
                    v___y_6463_ = v___x_6500_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                lean_inc(v_a_6454_);
                v___x_6464_ = l_Lean_Meta_mkConstWithFreshMVarLevels(
                    v_a_6454_,
                    v___y_6443_,
                    v___y_6444_,
                    v___y_6445_,
                    v___y_6446_,
                );
                if lean_obj_tag(v___x_6464_) == 0 {
                    v_a_6465_ = lean_ctor_get(v___x_6464_, 0);
                    lean_inc(v_a_6465_);
                    lean_dec_ref_known(v___x_6464_, 1);
                    v_lctx_6466_ = lean_ctor_get(v___y_6443_, 2);
                    lean_inc_ref(v_lctx_6466_);
                    if v_isShared_6460_ == 0 {
                        lean_ctor_set(v___x_6459_, 0, v_lctx_6466_);
                        v___x_6468_ = v___x_6459_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_6481_ = lean_alloc_ctor(1, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_6481_, 0, v_lctx_6466_);
                        v___x_6468_ = v_reuseFailAlloc_6481_;
                        state = 3;
                        continue;
                    }
                } else {
                    lean_dec_ref(v___y_6463_);
                    lean_del_object(v___x_6459_);
                    lean_dec(v_val_6457_);
                    lean_dec(v_a_6454_);
                    lean_dec(v_id_6438_);
                    lean_dec_ref(v_x_6434_);
                    v_a_6482_ = lean_ctor_get(v___x_6464_, 0);
                    v_isSharedCheck_6489_ = (!lean_is_exclusive(v___x_6464_)) as u8;
                    if v_isSharedCheck_6489_ == 0 {
                        v___x_6484_ = v___x_6464_;
                        v_isShared_6485_ = v_isSharedCheck_6489_;
                        state = 6;
                        continue;
                    } else {
                        lean_inc(v_a_6482_);
                        lean_dec(v___x_6464_);
                        v___x_6484_ = lean_box(0);
                        v_isShared_6485_ = v_isSharedCheck_6489_;
                        state = 6;
                        continue;
                    }
                }
            }
            3 => {
                v___x_6469_ = lean_box(0);
                lean_inc(v_id_6438_);
                v___x_6470_ = l_Lean_Elab_Term_addTermInfo(
                    v_id_6438_,
                    v_a_6465_,
                    v_a_6450_,
                    v___x_6468_,
                    v___x_6469_,
                    v___x_6461_,
                    v___x_6461_,
                    v___x_6461_,
                    v___y_6441_,
                    v___y_6442_,
                    v___y_6443_,
                    v___y_6444_,
                    v___y_6445_,
                    v___y_6446_,
                );
                if lean_obj_tag(v___x_6470_) == 0 {
                    lean_dec_ref_known(v___x_6470_, 1);
                    v___x_6471_ = lean_array_to_list(v_val_6457_);
                    v___x_6472_ =
                        l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_withRWRulesSeq_go(
                            v_x_6434_,
                            v___y_6435_,
                            v_id_6438_,
                            v_a_6454_,
                            v___y_6463_,
                            v___x_6471_,
                            v___y_6439_,
                            v___y_6440_,
                            v___y_6441_,
                            v___y_6442_,
                            v___y_6443_,
                            v___y_6444_,
                            v___y_6445_,
                            v___y_6446_,
                        );
                    lean_dec(v_id_6438_);
                    return v___x_6472_;
                } else {
                    lean_dec_ref(v___y_6463_);
                    lean_dec(v_val_6457_);
                    lean_dec(v_a_6454_);
                    lean_dec(v_id_6438_);
                    lean_dec_ref(v_x_6434_);
                    v_a_6473_ = lean_ctor_get(v___x_6470_, 0);
                    v_isSharedCheck_6480_ = (!lean_is_exclusive(v___x_6470_)) as u8;
                    if v_isSharedCheck_6480_ == 0 {
                        v___x_6475_ = v___x_6470_;
                        v_isShared_6476_ = v_isSharedCheck_6480_;
                        state = 4;
                        continue;
                    } else {
                        lean_inc(v_a_6473_);
                        lean_dec(v___x_6470_);
                        v___x_6475_ = lean_box(0);
                        v_isShared_6476_ = v_isSharedCheck_6480_;
                        state = 4;
                        continue;
                    }
                }
            }
            4 => {
                if v_isShared_6476_ == 0 {
                    v___x_6478_ = v___x_6475_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_6479_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6479_, 0, v_a_6473_);
                    v___x_6478_ = v_reuseFailAlloc_6479_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_6478_;
            }
            6 => {
                if v_isShared_6485_ == 0 {
                    v___x_6487_ = v___x_6484_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_6488_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6488_, 0, v_a_6482_);
                    v___x_6487_ = v_reuseFailAlloc_6488_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_6487_;
            }
            8 => {
                if v_isShared_6507_ == 0 {
                    v___x_6509_ = v___x_6506_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_6510_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6510_, 0, v_a_6504_);
                    v___x_6509_ = v_reuseFailAlloc_6510_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_6509_;
            }
            10 => {
                v___x_6524_ = l_Lean_Exception_isInterrupt(v_a_6512_);
                if v___x_6524_ == 0 {
                    lean_inc(v_a_6512_);
                    v___x_6525_ = l_Lean_Exception_isRuntime(v_a_6512_);
                    v___y_6517_ = v___x_6525_;
                    state = 11;
                    continue;
                } else {
                    v___y_6517_ = v___x_6524_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                if v___y_6517_ == 0 {
                    lean_del_object(v___x_6514_);
                    lean_dec(v_a_6512_);
                    v___x_6518_ = l_Lean_Elab_Tactic_SavedState_restore___redArg(
                        v_a_6452_,
                        v___y_6517_,
                        v___y_6440_,
                        v___y_6441_,
                        v___y_6442_,
                        v___y_6443_,
                        v___y_6444_,
                        v___y_6445_,
                        v___y_6446_,
                    );
                    if lean_obj_tag(v___x_6518_) == 0 {
                        lean_dec_ref_known(v___x_6518_, 1);
                        v___x_6519_ = lean_box((v___y_6435_) as usize);
                        lean_inc(v___y_6446_);
                        lean_inc_ref(v___y_6445_);
                        lean_inc(v___y_6444_);
                        lean_inc_ref(v___y_6443_);
                        lean_inc(v___y_6442_);
                        lean_inc_ref(v___y_6441_);
                        lean_inc(v___y_6440_);
                        lean_inc_ref(v___y_6439_);
                        v___x_6520_ = lean_apply_11(
                            v_x_6434_,
                            v___x_6519_,
                            v___x_6437_,
                            v___y_6439_,
                            v___y_6440_,
                            v___y_6441_,
                            v___y_6442_,
                            v___y_6443_,
                            v___y_6444_,
                            v___y_6445_,
                            v___y_6446_,
                            lean_box(0),
                        );
                        return v___x_6520_;
                    } else {
                        lean_dec(v___x_6437_);
                        lean_dec_ref(v_x_6434_);
                        return v___x_6518_;
                    }
                } else {
                    lean_dec(v_a_6452_);
                    lean_dec(v___x_6437_);
                    lean_dec_ref(v_x_6434_);
                    if v_isShared_6515_ == 0 {
                        v___x_6522_ = v___x_6514_;
                        state = 12;
                        continue;
                    } else {
                        v_reuseFailAlloc_6523_ = lean_alloc_ctor(1, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_6523_, 0, v_a_6512_);
                        v___x_6522_ = v_reuseFailAlloc_6523_;
                        state = 12;
                        continue;
                    }
                }
            }
            12 => {
                return v___x_6522_;
            }
            13 => {
                if v_isShared_6530_ == 0 {
                    v___x_6532_ = v___x_6529_;
                    state = 14;
                    continue;
                } else {
                    v_reuseFailAlloc_6533_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6533_, 0, v_a_6527_);
                    v___x_6532_ = v_reuseFailAlloc_6533_;
                    state = 14;
                    continue;
                }
            }
            14 => {
                return v___x_6532_;
            }
            15 => {
                if v_isShared_6540_ == 0 {
                    v___x_6542_ = v___x_6539_;
                    state = 16;
                    continue;
                } else {
                    v_reuseFailAlloc_6543_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6543_, 0, v_a_6537_);
                    v___x_6542_ = v_reuseFailAlloc_6543_;
                    state = 16;
                    continue;
                }
            }
            16 => {
                return v___x_6542_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_withRWRulesSeq_spec__1___redArg___lam__2___boxed(
    mut v_x_6545_: *mut LeanObject,
    mut v___y_6546_: *mut LeanObject,
    mut v___x_6547_: *mut LeanObject,
    mut v___x_6548_: *mut LeanObject,
    mut v_id_6549_: *mut LeanObject,
    mut v___y_6550_: *mut LeanObject,
    mut v___y_6551_: *mut LeanObject,
    mut v___y_6552_: *mut LeanObject,
    mut v___y_6553_: *mut LeanObject,
    mut v___y_6554_: *mut LeanObject,
    mut v___y_6555_: *mut LeanObject,
    mut v___y_6556_: *mut LeanObject,
    mut v___y_6557_: *mut LeanObject,
    mut v___y_6558_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___y_16885__boxed_6559_: u8 = 0;
    let mut v_res_6560_: *mut LeanObject = core::ptr::null_mut();
    v___y_16885__boxed_6559_ = (lean_unbox(v___y_6546_) as u8);
    v_res_6560_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_withRWRulesSeq_spec__1___redArg___lam__2(v_x_6545_, v___y_16885__boxed_6559_, v___x_6547_, v___x_6548_, v_id_6549_, v___y_6550_, v___y_6551_, v___y_6552_, v___y_6553_, v___y_6554_, v___y_6555_, v___y_6556_, v___y_6557_);
    lean_dec(v___y_6557_);
    lean_dec_ref(v___y_6556_);
    lean_dec(v___y_6555_);
    lean_dec_ref(v___y_6554_);
    lean_dec(v___y_6553_);
    lean_dec_ref(v___y_6552_);
    lean_dec(v___y_6551_);
    lean_dec_ref(v___y_6550_);
    lean_dec(v___x_6547_);
    return v_res_6560_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_withRWRulesSeq_spec__1___redArg(
    mut v_upperBound_6567_: *mut LeanObject,
    mut v_rules_6568_: *mut LeanObject,
    mut v_x_6569_: *mut LeanObject,
    mut v_a_6570_: *mut LeanObject,
    mut v_b_6571_: *mut LeanObject,
    mut v___y_6572_: *mut LeanObject,
    mut v___y_6573_: *mut LeanObject,
    mut v___y_6574_: *mut LeanObject,
    mut v___y_6575_: *mut LeanObject,
    mut v___y_6576_: *mut LeanObject,
    mut v___y_6577_: *mut LeanObject,
    mut v___y_6578_: *mut LeanObject,
    mut v___y_6579_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6581_: u8 = 0;
    let mut v___x_6582_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6583_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6584_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6585_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6586_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6587_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6588_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6589_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6591_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6592_: u8 = 0;
    let mut v___x_6593_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6594_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_6595_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6596_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6597_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_6598_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6599_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6600_: u8 = 0;
    let mut v___x_6601_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6602_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_6603_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6604_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6605_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6607_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6609_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6610_: u8 = 0;
    let mut v___x_6612_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6613_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6614_: u8 = 0;
    let mut v___y_6616_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6617_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6618_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6619_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6620_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6621_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6622_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6623_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6624_: u8 = 0;
    let mut v___x_6625_: u8 = 0;
    let mut v___x_6626_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6627_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6628_: u8 = 0;
    let mut v___x_6629_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_6581_ = lean_nat_dec_lt(v_a_6570_, v_upperBound_6567_);
                if v___x_6581_ == 0 {
                    lean_dec(v_a_6570_);
                    lean_dec_ref(v_x_6569_);
                    v___x_6582_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_6582_, 0, v_b_6571_);
                    return v___x_6582_;
                } else {
                    v___x_6583_ = lean_unsigned_to_nat(2);
                    v___x_6584_ = lean_box(0);
                    v___x_6585_ = lean_unsigned_to_nat(1);
                    v___x_6586_ = lean_box(0);
                    v___x_6587_ = lean_unsigned_to_nat(0);
                    v___x_6588_ = lean_nat_mul(v_a_6570_, v___x_6583_);
                    v___x_6589_ = lean_array_get_borrowed(v___x_6584_, v_rules_6568_, v___x_6588_);
                    v___x_6626_ = lean_nat_add(v___x_6588_, v___x_6585_);
                    lean_dec(v___x_6588_);
                    v___x_6627_ = lean_array_get_size(v_rules_6568_);
                    v___x_6628_ = lean_nat_dec_lt(v___x_6626_, v___x_6627_);
                    if v___x_6628_ == 0 {
                        lean_dec(v___x_6626_);
                        v___y_6616_ = v___x_6584_;
                        state = 4;
                        continue;
                    } else {
                        v___x_6629_ = lean_array_fget_borrowed(v_rules_6568_, v___x_6626_);
                        lean_dec(v___x_6626_);
                        lean_inc(v___x_6629_);
                        v___y_6616_ = v___x_6629_;
                        state = 4;
                        continue;
                    }
                }
            }
            1 => {
                v___x_6593_ = l_Lean_Elab_Tactic_mkInitialTacticInfo(
                    v___y_6591_,
                    v___y_6572_,
                    v___y_6573_,
                    v___y_6574_,
                    v___y_6575_,
                    v___y_6576_,
                    v___y_6577_,
                    v___y_6578_,
                    v___y_6579_,
                );
                if lean_obj_tag(v___x_6593_) == 0 {
                    v_a_6594_ = lean_ctor_get(v___x_6593_, 0);
                    lean_inc(v_a_6594_);
                    lean_dec_ref_known(v___x_6593_, 1);
                    v___f_6595_ = lean_alloc_closure(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_withRWRulesSeq_spec__1___redArg___lam__0___boxed as *mut core::ffi::c_void, 11, 1);
                    lean_closure_set(v___f_6595_, 0, v_a_6594_);
                    v___x_6596_ = l_Lean_Syntax_getArg(v___x_6589_, v___x_6585_);
                    v___x_6597_ = lean_box((v___y_6592_) as usize);
                    lean_inc_n(v___x_6596_, 2);
                    lean_inc_ref_n(v_x_6569_, 2);
                    v___f_6598_ = lean_alloc_closure(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_withRWRulesSeq_spec__1___redArg___lam__2___boxed as *mut core::ffi::c_void, 14, 4);
                    lean_closure_set(v___f_6598_, 0, v_x_6569_);
                    lean_closure_set(v___f_6598_, 1, v___x_6597_);
                    lean_closure_set(v___f_6598_, 2, v___x_6585_);
                    lean_closure_set(v___f_6598_, 3, v___x_6596_);
                    v___x_6599_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_withRWRulesSeq_spec__1___redArg___closed__1;
                    v___x_6600_ = l_Lean_Syntax_isOfKind(v___x_6596_, v___x_6599_);
                    v___x_6601_ = lean_box((v___x_6600_) as usize);
                    v___x_6602_ = lean_box((v___y_6592_) as usize);
                    lean_inc(v___x_6589_);
                    v___f_6603_ = lean_alloc_closure(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_withRWRulesSeq_spec__1___redArg___lam__3___boxed as *mut core::ffi::c_void, 17, 8);
                    lean_closure_set(v___f_6603_, 0, v___x_6589_);
                    lean_closure_set(v___f_6603_, 1, v___x_6601_);
                    lean_closure_set(v___f_6603_, 2, v___x_6596_);
                    lean_closure_set(v___f_6603_, 3, v_x_6569_);
                    lean_closure_set(v___f_6603_, 4, v___x_6602_);
                    lean_closure_set(v___f_6603_, 5, v___x_6585_);
                    lean_closure_set(v___f_6603_, 6, v___x_6599_);
                    lean_closure_set(v___f_6603_, 7, v___f_6598_);
                    v___x_6604_ = l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_withRWRulesSeq_spec__0___redArg(v___f_6603_, v___f_6595_, v___y_6572_, v___y_6573_, v___y_6574_, v___y_6575_, v___y_6576_, v___y_6577_, v___y_6578_, v___y_6579_);
                    if lean_obj_tag(v___x_6604_) == 0 {
                        lean_dec_ref_known(v___x_6604_, 1);
                        v___x_6605_ = lean_nat_add(v_a_6570_, v___x_6585_);
                        lean_dec(v_a_6570_);
                        v_a_6570_ = v___x_6605_;
                        v_b_6571_ = v___x_6586_;
                        state = 0;
                        continue;
                    } else {
                        lean_dec(v_a_6570_);
                        lean_dec_ref(v_x_6569_);
                        return v___x_6604_;
                    }
                } else {
                    lean_dec(v_a_6570_);
                    lean_dec_ref(v_x_6569_);
                    v_a_6607_ = lean_ctor_get(v___x_6593_, 0);
                    v_isSharedCheck_6614_ = (!lean_is_exclusive(v___x_6593_)) as u8;
                    if v_isSharedCheck_6614_ == 0 {
                        v___x_6609_ = v___x_6593_;
                        v_isShared_6610_ = v_isSharedCheck_6614_;
                        state = 2;
                        continue;
                    } else {
                        lean_inc(v_a_6607_);
                        lean_dec(v___x_6593_);
                        v___x_6609_ = lean_box(0);
                        v_isShared_6610_ = v_isSharedCheck_6614_;
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                if v_isShared_6610_ == 0 {
                    v___x_6612_ = v___x_6609_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_6613_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6613_, 0, v_a_6607_);
                    v___x_6612_ = v_reuseFailAlloc_6613_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_6612_;
            }
            4 => {
                v___x_6617_ = lean_mk_empty_array_with_capacity(v___x_6583_);
                lean_inc(v___x_6589_);
                v___x_6618_ = lean_array_push(v___x_6617_, v___x_6589_);
                v___x_6619_ = lean_array_push(v___x_6618_, v___y_6616_);
                v___x_6620_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_withRWRulesSeq_spec__1___redArg___closed__3;
                v___x_6621_ = lean_box(2);
                v___x_6622_ = lean_alloc_ctor(1, 3, (0) as u32);
                lean_ctor_set(v___x_6622_, 0, v___x_6621_);
                lean_ctor_set(v___x_6622_, 1, v___x_6620_);
                lean_ctor_set(v___x_6622_, 2, v___x_6619_);
                v___x_6623_ = l_Lean_Syntax_getArg(v___x_6589_, v___x_6587_);
                v___x_6624_ = l_Lean_Syntax_isNone(v___x_6623_);
                lean_dec(v___x_6623_);
                if v___x_6624_ == 0 {
                    v___y_6591_ = v___x_6622_;
                    v___y_6592_ = v___x_6581_;
                    state = 1;
                    continue;
                } else {
                    v___x_6625_ = 0;
                    v___y_6591_ = v___x_6622_;
                    v___y_6592_ = v___x_6625_;
                    state = 1;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_withRWRulesSeq_spec__1___redArg___boxed(
    mut v_upperBound_6630_: *mut LeanObject,
    mut v_rules_6631_: *mut LeanObject,
    mut v_x_6632_: *mut LeanObject,
    mut v_a_6633_: *mut LeanObject,
    mut v_b_6634_: *mut LeanObject,
    mut v___y_6635_: *mut LeanObject,
    mut v___y_6636_: *mut LeanObject,
    mut v___y_6637_: *mut LeanObject,
    mut v___y_6638_: *mut LeanObject,
    mut v___y_6639_: *mut LeanObject,
    mut v___y_6640_: *mut LeanObject,
    mut v___y_6641_: *mut LeanObject,
    mut v___y_6642_: *mut LeanObject,
    mut v___y_6643_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6644_: *mut LeanObject = core::ptr::null_mut();
    v_res_6644_ =
        l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_withRWRulesSeq_spec__1___redArg(
            v_upperBound_6630_,
            v_rules_6631_,
            v_x_6632_,
            v_a_6633_,
            v_b_6634_,
            v___y_6635_,
            v___y_6636_,
            v___y_6637_,
            v___y_6638_,
            v___y_6639_,
            v___y_6640_,
            v___y_6641_,
            v___y_6642_,
        );
    lean_dec(v___y_6642_);
    lean_dec_ref(v___y_6641_);
    lean_dec(v___y_6640_);
    lean_dec_ref(v___y_6639_);
    lean_dec(v___y_6638_);
    lean_dec_ref(v___y_6637_);
    lean_dec(v___y_6636_);
    lean_dec_ref(v___y_6635_);
    lean_dec_ref(v_rules_6631_);
    lean_dec(v_upperBound_6630_);
    return v_res_6644_;
}
pub unsafe fn l_Lean_Elab_Tactic_withRWRulesSeq(
    mut v_token_6647_: *mut LeanObject,
    mut v_rwRulesSeqStx_6648_: *mut LeanObject,
    mut v_x_6649_: *mut LeanObject,
    mut v_a_6650_: *mut LeanObject,
    mut v_a_6651_: *mut LeanObject,
    mut v_a_6652_: *mut LeanObject,
    mut v_a_6653_: *mut LeanObject,
    mut v_a_6654_: *mut LeanObject,
    mut v_a_6655_: *mut LeanObject,
    mut v_a_6656_: *mut LeanObject,
    mut v_a_6657_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6659_: *mut LeanObject = core::ptr::null_mut();
    let mut v_lbrak_6660_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6661_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6662_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6663_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6664_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6665_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6666_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6667_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6668_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6669_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_6670_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6671_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_6672_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6673_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6674_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6675_: *mut LeanObject = core::ptr::null_mut();
    let mut v_rules_6676_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6677_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6678_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6679_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6680_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6682_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6683_: u8 = 0;
    let mut v___x_6685_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6686_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6687_: u8 = 0;
    let mut v_unused_6688_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6689_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6691_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6692_: u8 = 0;
    let mut v___x_6694_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6695_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6696_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_6659_ = lean_unsigned_to_nat(0);
                v_lbrak_6660_ = l_Lean_Syntax_getArg(v_rwRulesSeqStx_6648_, v___x_6659_);
                v___x_6661_ = lean_unsigned_to_nat(2);
                v___x_6662_ = lean_mk_empty_array_with_capacity(v___x_6661_);
                v___x_6663_ = lean_array_push(v___x_6662_, v_token_6647_);
                v___x_6664_ = lean_array_push(v___x_6663_, v_lbrak_6660_);
                v___x_6665_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_withRWRulesSeq_spec__1___redArg___closed__3;
                v___x_6666_ = lean_box(2);
                v___x_6667_ = lean_alloc_ctor(1, 3, (0) as u32);
                lean_ctor_set(v___x_6667_, 0, v___x_6666_);
                lean_ctor_set(v___x_6667_, 1, v___x_6665_);
                lean_ctor_set(v___x_6667_, 2, v___x_6664_);
                v___x_6668_ = l_Lean_Elab_Tactic_mkInitialTacticInfo(
                    v___x_6667_,
                    v_a_6650_,
                    v_a_6651_,
                    v_a_6652_,
                    v_a_6653_,
                    v_a_6654_,
                    v_a_6655_,
                    v_a_6656_,
                    v_a_6657_,
                );
                if lean_obj_tag(v___x_6668_) == 0 {
                    v_a_6669_ = lean_ctor_get(v___x_6668_, 0);
                    lean_inc(v_a_6669_);
                    lean_dec_ref_known(v___x_6668_, 1);
                    v___f_6670_ = lean_alloc_closure(
                        l_Lean_Elab_Tactic_withRWRulesSeq___lam__0___boxed
                            as *mut core::ffi::c_void,
                        11,
                        1,
                    );
                    lean_closure_set(v___f_6670_, 0, v_a_6669_);
                    v___x_6671_ = lean_box(0);
                    v___f_6672_ = l_Lean_Elab_Tactic_withRWRulesSeq___closed__0;
                    v___x_6673_ = l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_withRWRulesSeq_spec__0___redArg(v___f_6672_, v___f_6670_, v_a_6650_, v_a_6651_, v_a_6652_, v_a_6653_, v_a_6654_, v_a_6655_, v_a_6656_, v_a_6657_);
                    if lean_obj_tag(v___x_6673_) == 0 {
                        lean_dec_ref_known(v___x_6673_, 1);
                        v___x_6674_ = lean_unsigned_to_nat(1);
                        v___x_6675_ = l_Lean_Syntax_getArg(v_rwRulesSeqStx_6648_, v___x_6674_);
                        v_rules_6676_ = l_Lean_Syntax_getArgs(v___x_6675_);
                        lean_dec(v___x_6675_);
                        v___x_6677_ = lean_array_get_size(v_rules_6676_);
                        v___x_6678_ = lean_nat_add(v___x_6677_, v___x_6674_);
                        v___x_6679_ = lean_nat_shiftr(v___x_6678_, v___x_6674_);
                        lean_dec(v___x_6678_);
                        v___x_6680_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_withRWRulesSeq_spec__1___redArg(v___x_6679_, v_rules_6676_, v_x_6649_, v___x_6659_, v___x_6671_, v_a_6650_, v_a_6651_, v_a_6652_, v_a_6653_, v_a_6654_, v_a_6655_, v_a_6656_, v_a_6657_);
                        lean_dec_ref(v_rules_6676_);
                        lean_dec(v___x_6679_);
                        if lean_obj_tag(v___x_6680_) == 0 {
                            v_isSharedCheck_6687_ = (!lean_is_exclusive(v___x_6680_)) as u8;
                            if v_isSharedCheck_6687_ == 0 {
                                v_unused_6688_ = lean_ctor_get(v___x_6680_, 0);
                                lean_dec(v_unused_6688_);
                                v___x_6682_ = v___x_6680_;
                                v_isShared_6683_ = v_isSharedCheck_6687_;
                                state = 1;
                                continue;
                            } else {
                                lean_dec(v___x_6680_);
                                v___x_6682_ = lean_box(0);
                                v_isShared_6683_ = v_isSharedCheck_6687_;
                                state = 1;
                                continue;
                            }
                        } else {
                            return v___x_6680_;
                        }
                    } else {
                        lean_dec_ref(v_x_6649_);
                        return v___x_6673_;
                    }
                } else {
                    lean_dec_ref(v_x_6649_);
                    v_a_6689_ = lean_ctor_get(v___x_6668_, 0);
                    v_isSharedCheck_6696_ = (!lean_is_exclusive(v___x_6668_)) as u8;
                    if v_isSharedCheck_6696_ == 0 {
                        v___x_6691_ = v___x_6668_;
                        v_isShared_6692_ = v_isSharedCheck_6696_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_6689_);
                        lean_dec(v___x_6668_);
                        v___x_6691_ = lean_box(0);
                        v_isShared_6692_ = v_isSharedCheck_6696_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_6683_ == 0 {
                    lean_ctor_set(v___x_6682_, 0, v___x_6671_);
                    v___x_6685_ = v___x_6682_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_6686_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6686_, 0, v___x_6671_);
                    v___x_6685_ = v_reuseFailAlloc_6686_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_6685_;
            }
            3 => {
                if v_isShared_6692_ == 0 {
                    v___x_6694_ = v___x_6691_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_6695_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6695_, 0, v_a_6689_);
                    v___x_6694_ = v_reuseFailAlloc_6695_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_6694_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_Tactic_withRWRulesSeq___boxed(
    mut v_token_6697_: *mut LeanObject,
    mut v_rwRulesSeqStx_6698_: *mut LeanObject,
    mut v_x_6699_: *mut LeanObject,
    mut v_a_6700_: *mut LeanObject,
    mut v_a_6701_: *mut LeanObject,
    mut v_a_6702_: *mut LeanObject,
    mut v_a_6703_: *mut LeanObject,
    mut v_a_6704_: *mut LeanObject,
    mut v_a_6705_: *mut LeanObject,
    mut v_a_6706_: *mut LeanObject,
    mut v_a_6707_: *mut LeanObject,
    mut v_a_6708_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6709_: *mut LeanObject = core::ptr::null_mut();
    v_res_6709_ = l_Lean_Elab_Tactic_withRWRulesSeq(
        v_token_6697_,
        v_rwRulesSeqStx_6698_,
        v_x_6699_,
        v_a_6700_,
        v_a_6701_,
        v_a_6702_,
        v_a_6703_,
        v_a_6704_,
        v_a_6705_,
        v_a_6706_,
        v_a_6707_,
    );
    lean_dec(v_a_6707_);
    lean_dec_ref(v_a_6706_);
    lean_dec(v_a_6705_);
    lean_dec_ref(v_a_6704_);
    lean_dec(v_a_6703_);
    lean_dec_ref(v_a_6702_);
    lean_dec(v_a_6701_);
    lean_dec_ref(v_a_6700_);
    lean_dec(v_rwRulesSeqStx_6698_);
    return v_res_6709_;
}
pub unsafe fn l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_withRWRulesSeq_spec__0_spec__0(
    mut v___y_6710_: *mut LeanObject,
    mut v___y_6711_: *mut LeanObject,
    mut v___y_6712_: *mut LeanObject,
    mut v___y_6713_: *mut LeanObject,
    mut v___y_6714_: *mut LeanObject,
    mut v___y_6715_: *mut LeanObject,
    mut v___y_6716_: *mut LeanObject,
    mut v___y_6717_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6719_: *mut LeanObject = core::ptr::null_mut();
    v___x_6719_ = l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_withRWRulesSeq_spec__0_spec__0___redArg(v___y_6717_);
    return v___x_6719_;
}
pub unsafe fn l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_withRWRulesSeq_spec__0_spec__0___boxed(
    mut v___y_6720_: *mut LeanObject,
    mut v___y_6721_: *mut LeanObject,
    mut v___y_6722_: *mut LeanObject,
    mut v___y_6723_: *mut LeanObject,
    mut v___y_6724_: *mut LeanObject,
    mut v___y_6725_: *mut LeanObject,
    mut v___y_6726_: *mut LeanObject,
    mut v___y_6727_: *mut LeanObject,
    mut v___y_6728_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6729_: *mut LeanObject = core::ptr::null_mut();
    v_res_6729_ = l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_withRWRulesSeq_spec__0_spec__0(v___y_6720_, v___y_6721_, v___y_6722_, v___y_6723_, v___y_6724_, v___y_6725_, v___y_6726_, v___y_6727_);
    lean_dec(v___y_6727_);
    lean_dec_ref(v___y_6726_);
    lean_dec(v___y_6725_);
    lean_dec_ref(v___y_6724_);
    lean_dec(v___y_6723_);
    lean_dec_ref(v___y_6722_);
    lean_dec(v___y_6721_);
    lean_dec_ref(v___y_6720_);
    return v_res_6729_;
}
pub unsafe fn l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_withRWRulesSeq_spec__0(
    mut v_00_u03b1_6730_: *mut LeanObject,
    mut v_x_6731_: *mut LeanObject,
    mut v_mkInfoTree_6732_: *mut LeanObject,
    mut v___y_6733_: *mut LeanObject,
    mut v___y_6734_: *mut LeanObject,
    mut v___y_6735_: *mut LeanObject,
    mut v___y_6736_: *mut LeanObject,
    mut v___y_6737_: *mut LeanObject,
    mut v___y_6738_: *mut LeanObject,
    mut v___y_6739_: *mut LeanObject,
    mut v___y_6740_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6742_: *mut LeanObject = core::ptr::null_mut();
    v___x_6742_ =
        l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_withRWRulesSeq_spec__0___redArg(
            v_x_6731_,
            v_mkInfoTree_6732_,
            v___y_6733_,
            v___y_6734_,
            v___y_6735_,
            v___y_6736_,
            v___y_6737_,
            v___y_6738_,
            v___y_6739_,
            v___y_6740_,
        );
    return v___x_6742_;
}
pub unsafe fn l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_withRWRulesSeq_spec__0___boxed(
    mut v_00_u03b1_6743_: *mut LeanObject,
    mut v_x_6744_: *mut LeanObject,
    mut v_mkInfoTree_6745_: *mut LeanObject,
    mut v___y_6746_: *mut LeanObject,
    mut v___y_6747_: *mut LeanObject,
    mut v___y_6748_: *mut LeanObject,
    mut v___y_6749_: *mut LeanObject,
    mut v___y_6750_: *mut LeanObject,
    mut v___y_6751_: *mut LeanObject,
    mut v___y_6752_: *mut LeanObject,
    mut v___y_6753_: *mut LeanObject,
    mut v___y_6754_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6755_: *mut LeanObject = core::ptr::null_mut();
    v_res_6755_ = l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_withRWRulesSeq_spec__0(
        v_00_u03b1_6743_,
        v_x_6744_,
        v_mkInfoTree_6745_,
        v___y_6746_,
        v___y_6747_,
        v___y_6748_,
        v___y_6749_,
        v___y_6750_,
        v___y_6751_,
        v___y_6752_,
        v___y_6753_,
    );
    lean_dec(v___y_6753_);
    lean_dec_ref(v___y_6752_);
    lean_dec(v___y_6751_);
    lean_dec_ref(v___y_6750_);
    lean_dec(v___y_6749_);
    lean_dec_ref(v___y_6748_);
    lean_dec(v___y_6747_);
    lean_dec_ref(v___y_6746_);
    return v_res_6755_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_withRWRulesSeq_spec__1(
    mut v_upperBound_6756_: *mut LeanObject,
    mut v_rules_6757_: *mut LeanObject,
    mut v_x_6758_: *mut LeanObject,
    mut v_inst_6759_: *mut LeanObject,
    mut v_R_6760_: *mut LeanObject,
    mut v_a_6761_: *mut LeanObject,
    mut v_b_6762_: *mut LeanObject,
    mut v_c_6763_: *mut LeanObject,
    mut v___y_6764_: *mut LeanObject,
    mut v___y_6765_: *mut LeanObject,
    mut v___y_6766_: *mut LeanObject,
    mut v___y_6767_: *mut LeanObject,
    mut v___y_6768_: *mut LeanObject,
    mut v___y_6769_: *mut LeanObject,
    mut v___y_6770_: *mut LeanObject,
    mut v___y_6771_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6773_: *mut LeanObject = core::ptr::null_mut();
    v___x_6773_ =
        l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_withRWRulesSeq_spec__1___redArg(
            v_upperBound_6756_,
            v_rules_6757_,
            v_x_6758_,
            v_a_6761_,
            v_b_6762_,
            v___y_6764_,
            v___y_6765_,
            v___y_6766_,
            v___y_6767_,
            v___y_6768_,
            v___y_6769_,
            v___y_6770_,
            v___y_6771_,
        );
    return v___x_6773_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_withRWRulesSeq_spec__1___boxed(
    _args: *mut *mut LeanObject,
) -> *mut LeanObject {
    let mut v_upperBound_6774_: *mut LeanObject = *_args.add(0);
    let mut v_rules_6775_: *mut LeanObject = *_args.add(1);
    let mut v_x_6776_: *mut LeanObject = *_args.add(2);
    let mut v_inst_6777_: *mut LeanObject = *_args.add(3);
    let mut v_R_6778_: *mut LeanObject = *_args.add(4);
    let mut v_a_6779_: *mut LeanObject = *_args.add(5);
    let mut v_b_6780_: *mut LeanObject = *_args.add(6);
    let mut v_c_6781_: *mut LeanObject = *_args.add(7);
    let mut v___y_6782_: *mut LeanObject = *_args.add(8);
    let mut v___y_6783_: *mut LeanObject = *_args.add(9);
    let mut v___y_6784_: *mut LeanObject = *_args.add(10);
    let mut v___y_6785_: *mut LeanObject = *_args.add(11);
    let mut v___y_6786_: *mut LeanObject = *_args.add(12);
    let mut v___y_6787_: *mut LeanObject = *_args.add(13);
    let mut v___y_6788_: *mut LeanObject = *_args.add(14);
    let mut v___y_6789_: *mut LeanObject = *_args.add(15);
    let mut v___y_6790_: *mut LeanObject = *_args.add(16);
    let mut v_res_6791_: *mut LeanObject = core::ptr::null_mut();
    v_res_6791_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Tactic_withRWRulesSeq_spec__1(
        v_upperBound_6774_,
        v_rules_6775_,
        v_x_6776_,
        v_inst_6777_,
        v_R_6778_,
        v_a_6779_,
        v_b_6780_,
        v_c_6781_,
        v___y_6782_,
        v___y_6783_,
        v___y_6784_,
        v___y_6785_,
        v___y_6786_,
        v___y_6787_,
        v___y_6788_,
        v___y_6789_,
    );
    lean_dec(v___y_6789_);
    lean_dec_ref(v___y_6788_);
    lean_dec(v___y_6787_);
    lean_dec_ref(v___y_6786_);
    lean_dec(v___y_6785_);
    lean_dec_ref(v___y_6784_);
    lean_dec(v___y_6783_);
    lean_dec_ref(v___y_6782_);
    lean_dec_ref(v_rules_6775_);
    lean_dec(v_upperBound_6774_);
    return v_res_6791_;
}
pub unsafe fn _init_l_Lean_Elab_ConfigEval_throwUnsupportedExpr___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_instEvalExprConfig_evalExpr_spec__0___redArg___closed__0()
-> *mut LeanObject {
    let mut v___x_6792_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6793_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6794_: *mut LeanObject = core::ptr::null_mut();
    v___x_6792_ = lean_box(0);
    v___x_6793_ = l_Lean_Elab_ConfigEval_unsupportedExprExceptionId;
    v___x_6794_ = lean_alloc_ctor(1, 2, (0) as u32);
    lean_ctor_set(v___x_6794_, 0, v___x_6793_);
    lean_ctor_set(v___x_6794_, 1, v___x_6792_);
    return v___x_6794_;
}
pub unsafe fn l_Lean_Elab_ConfigEval_throwUnsupportedExpr___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_instEvalExprConfig_evalExpr_spec__0___redArg()
-> *mut LeanObject {
    let mut v___x_6796_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6797_: *mut LeanObject = core::ptr::null_mut();
    v___x_6796_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_ConfigEval_throwUnsupportedExpr___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_instEvalExprConfig_evalExpr_spec__0___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_Elab_ConfigEval_throwUnsupportedExpr___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_instEvalExprConfig_evalExpr_spec__0___redArg___closed__0_once), _init_l_Lean_Elab_ConfigEval_throwUnsupportedExpr___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_instEvalExprConfig_evalExpr_spec__0___redArg___closed__0);
    v___x_6797_ = lean_alloc_ctor(1, 1, (0) as u32);
    lean_ctor_set(v___x_6797_, 0, v___x_6796_);
    return v___x_6797_;
}
pub unsafe fn l_Lean_Elab_ConfigEval_throwUnsupportedExpr___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_instEvalExprConfig_evalExpr_spec__0___redArg___boxed(
    mut v___y_6798_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6799_: *mut LeanObject = core::ptr::null_mut();
    v_res_6799_ = l_Lean_Elab_ConfigEval_throwUnsupportedExpr___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_instEvalExprConfig_evalExpr_spec__0___redArg();
    return v_res_6799_;
}
pub unsafe fn l_Lean_Elab_ConfigEval_throwUnsupportedExpr___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_instEvalExprConfig_evalExpr_spec__0(
    mut v_00_u03b1_6800_: *mut LeanObject,
    mut v___y_6801_: *mut LeanObject,
    mut v___y_6802_: *mut LeanObject,
    mut v___y_6803_: *mut LeanObject,
    mut v___y_6804_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6806_: *mut LeanObject = core::ptr::null_mut();
    v___x_6806_ = l_Lean_Elab_ConfigEval_throwUnsupportedExpr___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_instEvalExprConfig_evalExpr_spec__0___redArg();
    return v___x_6806_;
}
pub unsafe fn l_Lean_Elab_ConfigEval_throwUnsupportedExpr___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_instEvalExprConfig_evalExpr_spec__0___boxed(
    mut v_00_u03b1_6807_: *mut LeanObject,
    mut v___y_6808_: *mut LeanObject,
    mut v___y_6809_: *mut LeanObject,
    mut v___y_6810_: *mut LeanObject,
    mut v___y_6811_: *mut LeanObject,
    mut v___y_6812_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6813_: *mut LeanObject = core::ptr::null_mut();
    v_res_6813_ = l_Lean_Elab_ConfigEval_throwUnsupportedExpr___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_instEvalExprConfig_evalExpr_spec__0(v_00_u03b1_6807_, v___y_6808_, v___y_6809_, v___y_6810_, v___y_6811_);
    lean_dec(v___y_6811_);
    lean_dec_ref(v___y_6810_);
    lean_dec(v___y_6809_);
    lean_dec_ref(v___y_6808_);
    return v_res_6813_;
}
pub unsafe fn l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_instEvalExprConfig_evalExpr_spec__1___redArg(
    mut v_msg_6814_: *mut LeanObject,
    mut v___y_6815_: *mut LeanObject,
    mut v___y_6816_: *mut LeanObject,
    mut v___y_6817_: *mut LeanObject,
    mut v___y_6818_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_ref_6820_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6821_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6822_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6824_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6825_: u8 = 0;
    let mut v___x_6826_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6828_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6829_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6830_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ref_6820_ = lean_ctor_get(v___y_6817_, 5);
                v___x_6821_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Tactic_elabRewrite_spec__3_spec__4_spec__9(v_msg_6814_, v___y_6815_, v___y_6816_, v___y_6817_, v___y_6818_);
                v_a_6822_ = lean_ctor_get(v___x_6821_, 0);
                v_isSharedCheck_6830_ = (!lean_is_exclusive(v___x_6821_)) as u8;
                if v_isSharedCheck_6830_ == 0 {
                    v___x_6824_ = v___x_6821_;
                    v_isShared_6825_ = v_isSharedCheck_6830_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_a_6822_);
                    lean_dec(v___x_6821_);
                    v___x_6824_ = lean_box(0);
                    v_isShared_6825_ = v_isSharedCheck_6830_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                lean_inc(v_ref_6820_);
                v___x_6826_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_6826_, 0, v_ref_6820_);
                lean_ctor_set(v___x_6826_, 1, v_a_6822_);
                if v_isShared_6825_ == 0 {
                    lean_ctor_set_tag(v___x_6824_, 1);
                    lean_ctor_set(v___x_6824_, 0, v___x_6826_);
                    v___x_6828_ = v___x_6824_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_6829_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6829_, 0, v___x_6826_);
                    v___x_6828_ = v_reuseFailAlloc_6829_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_6828_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_instEvalExprConfig_evalExpr_spec__1___redArg___boxed(
    mut v_msg_6831_: *mut LeanObject,
    mut v___y_6832_: *mut LeanObject,
    mut v___y_6833_: *mut LeanObject,
    mut v___y_6834_: *mut LeanObject,
    mut v___y_6835_: *mut LeanObject,
    mut v___y_6836_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6837_: *mut LeanObject = core::ptr::null_mut();
    v_res_6837_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_instEvalExprConfig_evalExpr_spec__1___redArg(v_msg_6831_, v___y_6832_, v___y_6833_, v___y_6834_, v___y_6835_);
    lean_dec(v___y_6835_);
    lean_dec_ref(v___y_6834_);
    lean_dec(v___y_6833_);
    lean_dec_ref(v___y_6832_);
    return v_res_6837_;
}
pub unsafe fn _init_l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_instEvalExprConfig_evalExpr___lam__0___closed__2()
-> *mut LeanObject {
    let mut v___x_6840_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6841_: *mut LeanObject = core::ptr::null_mut();
    v___x_6840_ = l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_instEvalExprConfig_evalExpr___lam__0___closed__1;
    v___x_6841_ = l_Lean_stringToMessageData(v___x_6840_);
    return v___x_6841_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_instEvalExprConfig_evalExpr___lam__0(
    mut v_ctor_6842_: *mut LeanObject,
    mut v_args_6843_: *mut LeanObject,
    mut v___y_6844_: *mut LeanObject,
    mut v___y_6845_: *mut LeanObject,
    mut v___y_6846_: *mut LeanObject,
    mut v___y_6847_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6850_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6851_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6852_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6853_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6854_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6855_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6856_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6857_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6858_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6859_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6860_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6861_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6862_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6863_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6864_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6865_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6866_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6868_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6869_: u8 = 0;
    let mut v___x_6870_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6871_: u8 = 0;
    let mut v___x_6872_: u8 = 0;
    let mut v___x_6873_: u8 = 0;
    let mut v___x_6875_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6876_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6877_: u8 = 0;
    let mut v_a_6878_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6880_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6881_: u8 = 0;
    let mut v___x_6883_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6884_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6885_: u8 = 0;
    let mut v_a_6886_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6888_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6889_: u8 = 0;
    let mut v___x_6891_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6892_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6893_: u8 = 0;
    let mut v_a_6894_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6896_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6897_: u8 = 0;
    let mut v___x_6899_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6900_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6901_: u8 = 0;
    let mut v_a_6902_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6904_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6905_: u8 = 0;
    let mut v___x_6907_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6908_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6909_: u8 = 0;
    let mut v___x_6910_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6911_: u8 = 0;
    let mut v___x_6912_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6913_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6914_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6915_: u8 = 0;
    let mut v___x_6916_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6917_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6918_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6920_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6921_: u8 = 0;
    let mut v___x_6923_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6924_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6925_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_6910_ = l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_instEvalExprConfig_evalExpr___lam__0___closed__0;
                v___x_6911_ = lean_string_dec_eq(v_ctor_6842_, v___x_6910_);
                if v___x_6911_ == 0 {
                    v___x_6912_ = l_Lean_Elab_ConfigEval_throwUnsupportedExpr___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_instEvalExprConfig_evalExpr_spec__0___redArg();
                    return v___x_6912_;
                } else {
                    v___x_6913_ = lean_array_get_size(v_args_6843_);
                    v___x_6914_ = lean_unsigned_to_nat(4);
                    v___x_6915_ = lean_nat_dec_eq(v___x_6913_, v___x_6914_);
                    if v___x_6915_ == 0 {
                        v___x_6916_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_instEvalExprConfig_evalExpr___lam__0___closed__2), core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_instEvalExprConfig_evalExpr___lam__0___closed__2_once), _init_l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_instEvalExprConfig_evalExpr___lam__0___closed__2);
                        v___x_6917_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_instEvalExprConfig_evalExpr_spec__1___redArg(v___x_6916_, v___y_6844_, v___y_6845_, v___y_6846_, v___y_6847_);
                        v_a_6918_ = lean_ctor_get(v___x_6917_, 0);
                        v_isSharedCheck_6925_ = (!lean_is_exclusive(v___x_6917_)) as u8;
                        if v_isSharedCheck_6925_ == 0 {
                            v___x_6920_ = v___x_6917_;
                            v_isShared_6921_ = v_isSharedCheck_6925_;
                            state = 12;
                            continue;
                        } else {
                            lean_inc(v_a_6918_);
                            lean_dec(v___x_6917_);
                            v___x_6920_ = lean_box(0);
                            v_isShared_6921_ = v_isSharedCheck_6925_;
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
                v___x_6850_ = l_Lean_instInhabitedExpr;
                v___x_6851_ = lean_unsigned_to_nat(0);
                v___x_6852_ = lean_array_get_borrowed(v___x_6850_, v_args_6843_, v___x_6851_);
                lean_inc(v___x_6852_);
                v___x_6853_ = l_Lean_Elab_ConfigEval_instEvalExprTransparencyMode_evalExpr(
                    v___x_6852_,
                    v___y_6844_,
                    v___y_6845_,
                    v___y_6846_,
                    v___y_6847_,
                );
                if lean_obj_tag(v___x_6853_) == 0 {
                    v_a_6854_ = lean_ctor_get(v___x_6853_, 0);
                    lean_inc(v_a_6854_);
                    lean_dec_ref_known(v___x_6853_, 1);
                    v___x_6855_ = lean_unsigned_to_nat(1);
                    v___x_6856_ = lean_array_get_borrowed(v___x_6850_, v_args_6843_, v___x_6855_);
                    lean_inc(v___x_6856_);
                    v___x_6857_ = l_Lean_Elab_ConfigEval_EvalExpr_evalBoolExpr(
                        v___x_6856_,
                        v___y_6844_,
                        v___y_6845_,
                        v___y_6846_,
                        v___y_6847_,
                    );
                    if lean_obj_tag(v___x_6857_) == 0 {
                        v_a_6858_ = lean_ctor_get(v___x_6857_, 0);
                        lean_inc(v_a_6858_);
                        lean_dec_ref_known(v___x_6857_, 1);
                        v___x_6859_ = lean_unsigned_to_nat(2);
                        v___x_6860_ =
                            lean_array_get_borrowed(v___x_6850_, v_args_6843_, v___x_6859_);
                        lean_inc(v___x_6860_);
                        v___x_6861_ = l_Lean_Elab_ConfigEval_instEvalExprOccurrences_evalExpr(
                            v___x_6860_,
                            v___y_6844_,
                            v___y_6845_,
                            v___y_6846_,
                            v___y_6847_,
                        );
                        if lean_obj_tag(v___x_6861_) == 0 {
                            v_a_6862_ = lean_ctor_get(v___x_6861_, 0);
                            lean_inc(v_a_6862_);
                            lean_dec_ref_known(v___x_6861_, 1);
                            v___x_6863_ = lean_unsigned_to_nat(3);
                            v___x_6864_ =
                                lean_array_get_borrowed(v___x_6850_, v_args_6843_, v___x_6863_);
                            lean_inc(v___x_6864_);
                            v___x_6865_ = l_Lean_Elab_ConfigEval_instEvalExprApplyNewGoals_evalExpr(
                                v___x_6864_,
                                v___y_6844_,
                                v___y_6845_,
                                v___y_6846_,
                                v___y_6847_,
                            );
                            if lean_obj_tag(v___x_6865_) == 0 {
                                v_a_6866_ = lean_ctor_get(v___x_6865_, 0);
                                v_isSharedCheck_6877_ = (!lean_is_exclusive(v___x_6865_)) as u8;
                                if v_isSharedCheck_6877_ == 0 {
                                    v___x_6868_ = v___x_6865_;
                                    v_isShared_6869_ = v_isSharedCheck_6877_;
                                    state = 2;
                                    continue;
                                } else {
                                    lean_inc(v_a_6866_);
                                    lean_dec(v___x_6865_);
                                    v___x_6868_ = lean_box(0);
                                    v_isShared_6869_ = v_isSharedCheck_6877_;
                                    state = 2;
                                    continue;
                                }
                            } else {
                                lean_dec(v_a_6862_);
                                lean_dec(v_a_6858_);
                                lean_dec(v_a_6854_);
                                v_a_6878_ = lean_ctor_get(v___x_6865_, 0);
                                v_isSharedCheck_6885_ = (!lean_is_exclusive(v___x_6865_)) as u8;
                                if v_isSharedCheck_6885_ == 0 {
                                    v___x_6880_ = v___x_6865_;
                                    v_isShared_6881_ = v_isSharedCheck_6885_;
                                    state = 4;
                                    continue;
                                } else {
                                    lean_inc(v_a_6878_);
                                    lean_dec(v___x_6865_);
                                    v___x_6880_ = lean_box(0);
                                    v_isShared_6881_ = v_isSharedCheck_6885_;
                                    state = 4;
                                    continue;
                                }
                            }
                        } else {
                            lean_dec(v_a_6858_);
                            lean_dec(v_a_6854_);
                            v_a_6886_ = lean_ctor_get(v___x_6861_, 0);
                            v_isSharedCheck_6893_ = (!lean_is_exclusive(v___x_6861_)) as u8;
                            if v_isSharedCheck_6893_ == 0 {
                                v___x_6888_ = v___x_6861_;
                                v_isShared_6889_ = v_isSharedCheck_6893_;
                                state = 6;
                                continue;
                            } else {
                                lean_inc(v_a_6886_);
                                lean_dec(v___x_6861_);
                                v___x_6888_ = lean_box(0);
                                v_isShared_6889_ = v_isSharedCheck_6893_;
                                state = 6;
                                continue;
                            }
                        }
                    } else {
                        lean_dec(v_a_6854_);
                        v_a_6894_ = lean_ctor_get(v___x_6857_, 0);
                        v_isSharedCheck_6901_ = (!lean_is_exclusive(v___x_6857_)) as u8;
                        if v_isSharedCheck_6901_ == 0 {
                            v___x_6896_ = v___x_6857_;
                            v_isShared_6897_ = v_isSharedCheck_6901_;
                            state = 8;
                            continue;
                        } else {
                            lean_inc(v_a_6894_);
                            lean_dec(v___x_6857_);
                            v___x_6896_ = lean_box(0);
                            v_isShared_6897_ = v_isSharedCheck_6901_;
                            state = 8;
                            continue;
                        }
                    }
                } else {
                    v_a_6902_ = lean_ctor_get(v___x_6853_, 0);
                    v_isSharedCheck_6909_ = (!lean_is_exclusive(v___x_6853_)) as u8;
                    if v_isSharedCheck_6909_ == 0 {
                        v___x_6904_ = v___x_6853_;
                        v_isShared_6905_ = v_isSharedCheck_6909_;
                        state = 10;
                        continue;
                    } else {
                        lean_inc(v_a_6902_);
                        lean_dec(v___x_6853_);
                        v___x_6904_ = lean_box(0);
                        v_isShared_6905_ = v_isSharedCheck_6909_;
                        state = 10;
                        continue;
                    }
                }
            }
            2 => {
                v___x_6870_ = lean_alloc_ctor(0, 1, (3) as u32);
                lean_ctor_set(v___x_6870_, 0, v_a_6862_);
                v___x_6871_ = (lean_unbox(v_a_6854_) as u8);
                lean_dec(v_a_6854_);
                lean_ctor_set_uint8(
                    v___x_6870_,
                    (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                    v___x_6871_,
                );
                v___x_6872_ = (lean_unbox(v_a_6858_) as u8);
                lean_dec(v_a_6858_);
                lean_ctor_set_uint8(
                    v___x_6870_,
                    (core::mem::size_of::<*mut LeanObject>() * 1 + 1) as u32,
                    v___x_6872_,
                );
                v___x_6873_ = (lean_unbox(v_a_6866_) as u8);
                lean_dec(v_a_6866_);
                lean_ctor_set_uint8(
                    v___x_6870_,
                    (core::mem::size_of::<*mut LeanObject>() * 1 + 2) as u32,
                    v___x_6873_,
                );
                if v_isShared_6869_ == 0 {
                    lean_ctor_set(v___x_6868_, 0, v___x_6870_);
                    v___x_6875_ = v___x_6868_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_6876_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6876_, 0, v___x_6870_);
                    v___x_6875_ = v_reuseFailAlloc_6876_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_6875_;
            }
            4 => {
                if v_isShared_6881_ == 0 {
                    v___x_6883_ = v___x_6880_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_6884_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6884_, 0, v_a_6878_);
                    v___x_6883_ = v_reuseFailAlloc_6884_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_6883_;
            }
            6 => {
                if v_isShared_6889_ == 0 {
                    v___x_6891_ = v___x_6888_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_6892_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6892_, 0, v_a_6886_);
                    v___x_6891_ = v_reuseFailAlloc_6892_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_6891_;
            }
            8 => {
                if v_isShared_6897_ == 0 {
                    v___x_6899_ = v___x_6896_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_6900_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6900_, 0, v_a_6894_);
                    v___x_6899_ = v_reuseFailAlloc_6900_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_6899_;
            }
            10 => {
                if v_isShared_6905_ == 0 {
                    v___x_6907_ = v___x_6904_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_6908_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6908_, 0, v_a_6902_);
                    v___x_6907_ = v_reuseFailAlloc_6908_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                return v___x_6907_;
            }
            12 => {
                if v_isShared_6921_ == 0 {
                    v___x_6923_ = v___x_6920_;
                    state = 13;
                    continue;
                } else {
                    v_reuseFailAlloc_6924_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6924_, 0, v_a_6918_);
                    v___x_6923_ = v_reuseFailAlloc_6924_;
                    state = 13;
                    continue;
                }
            }
            13 => {
                return v___x_6923_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_instEvalExprConfig_evalExpr___lam__0___boxed(
    mut v_ctor_6926_: *mut LeanObject,
    mut v_args_6927_: *mut LeanObject,
    mut v___y_6928_: *mut LeanObject,
    mut v___y_6929_: *mut LeanObject,
    mut v___y_6930_: *mut LeanObject,
    mut v___y_6931_: *mut LeanObject,
    mut v___y_6932_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6933_: *mut LeanObject = core::ptr::null_mut();
    v_res_6933_ = l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_instEvalExprConfig_evalExpr___lam__0(v_ctor_6926_, v_args_6927_, v___y_6928_, v___y_6929_, v___y_6930_, v___y_6931_);
    lean_dec(v___y_6931_);
    lean_dec_ref(v___y_6930_);
    lean_dec(v___y_6929_);
    lean_dec_ref(v___y_6928_);
    lean_dec_ref(v_args_6927_);
    lean_dec_ref(v_ctor_6926_);
    return v_res_6933_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_instEvalExprConfig_evalExpr(
    mut v_a_6943_: *mut LeanObject,
    mut v_a_6944_: *mut LeanObject,
    mut v_a_6945_: *mut LeanObject,
    mut v_a_6946_: *mut LeanObject,
    mut v_a_6947_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_6949_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6950_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6951_: *mut LeanObject = core::ptr::null_mut();
    v___f_6949_ = l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_instEvalExprConfig_evalExpr___closed__0;
    v___x_6950_ = l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_instEvalExprConfig_evalExpr___closed__4;
    v___x_6951_ = l_Lean_Elab_ConfigEval_EvalExpr_withSimpleEvalExpr___redArg(
        v___x_6950_,
        v___f_6949_,
        v_a_6943_,
        v_a_6944_,
        v_a_6945_,
        v_a_6946_,
        v_a_6947_,
    );
    return v___x_6951_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_instEvalExprConfig_evalExpr___boxed(
    mut v_a_6952_: *mut LeanObject,
    mut v_a_6953_: *mut LeanObject,
    mut v_a_6954_: *mut LeanObject,
    mut v_a_6955_: *mut LeanObject,
    mut v_a_6956_: *mut LeanObject,
    mut v_a_6957_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6958_: *mut LeanObject = core::ptr::null_mut();
    v_res_6958_ =
        l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_instEvalExprConfig_evalExpr(
            v_a_6952_, v_a_6953_, v_a_6954_, v_a_6955_, v_a_6956_,
        );
    lean_dec(v_a_6956_);
    lean_dec_ref(v_a_6955_);
    lean_dec(v_a_6954_);
    lean_dec_ref(v_a_6953_);
    return v_res_6958_;
}
pub unsafe fn l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_instEvalExprConfig_evalExpr_spec__1(
    mut v_00_u03b1_6959_: *mut LeanObject,
    mut v_msg_6960_: *mut LeanObject,
    mut v___y_6961_: *mut LeanObject,
    mut v___y_6962_: *mut LeanObject,
    mut v___y_6963_: *mut LeanObject,
    mut v___y_6964_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6966_: *mut LeanObject = core::ptr::null_mut();
    v___x_6966_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_instEvalExprConfig_evalExpr_spec__1___redArg(v_msg_6960_, v___y_6961_, v___y_6962_, v___y_6963_, v___y_6964_);
    return v___x_6966_;
}
pub unsafe fn l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_instEvalExprConfig_evalExpr_spec__1___boxed(
    mut v_00_u03b1_6967_: *mut LeanObject,
    mut v_msg_6968_: *mut LeanObject,
    mut v___y_6969_: *mut LeanObject,
    mut v___y_6970_: *mut LeanObject,
    mut v___y_6971_: *mut LeanObject,
    mut v___y_6972_: *mut LeanObject,
    mut v___y_6973_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6974_: *mut LeanObject = core::ptr::null_mut();
    v_res_6974_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_instEvalExprConfig_evalExpr_spec__1(v_00_u03b1_6967_, v_msg_6968_, v___y_6969_, v___y_6970_, v___y_6971_, v___y_6972_);
    lean_dec(v___y_6972_);
    lean_dec_ref(v___y_6971_);
    lean_dec(v___y_6970_);
    lean_dec_ref(v___y_6969_);
    return v_res_6974_;
}
pub unsafe fn _init_l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_instEvalExprConfig___closed__1()
-> *mut LeanObject {
    let mut v___x_6976_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6977_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6978_: *mut LeanObject = core::ptr::null_mut();
    v___x_6976_ = lean_box(0);
    v___x_6977_ = l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_instEvalExprConfig_evalExpr___closed__4;
    v___x_6978_ = l_Lean_Expr_const___override(v___x_6977_, v___x_6976_);
    return v___x_6978_;
}
pub unsafe fn _init_l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_instEvalExprConfig___closed__2()
-> *mut LeanObject {
    let mut v___x_6979_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6980_: *mut LeanObject = core::ptr::null_mut();
    v___x_6979_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_instEvalExprConfig___closed__1), core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_instEvalExprConfig___closed__1_once), _init_l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_instEvalExprConfig___closed__1);
    v___x_6980_ = lean_alloc_ctor(1, 1, (0) as u32);
    lean_ctor_set(v___x_6980_, 0, v___x_6979_);
    return v___x_6980_;
}
pub unsafe fn _init_l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_instEvalExprConfig___closed__3()
-> *mut LeanObject {
    let mut v___x_6981_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6982_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6983_: *mut LeanObject = core::ptr::null_mut();
    v___x_6981_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_instEvalExprConfig___closed__2), core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_instEvalExprConfig___closed__2_once), _init_l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_instEvalExprConfig___closed__2);
    v___x_6982_ =
        l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_instEvalExprConfig___closed__0;
    v___x_6983_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_6983_, 0, v___x_6982_);
    lean_ctor_set(v___x_6983_, 1, v___x_6981_);
    return v___x_6983_;
}
pub unsafe fn _init_l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_instEvalExprConfig()
-> *mut LeanObject {
    let mut v___x_6984_: *mut LeanObject = core::ptr::null_mut();
    v___x_6984_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_instEvalExprConfig___closed__3), core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_instEvalExprConfig___closed__3_once), _init_l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_instEvalExprConfig___closed__3);
    return v___x_6984_;
}
pub unsafe fn _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3_spec__7_spec__8_spec__11___closed__0()
-> *mut LeanObject {
    let mut v___x_6985_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6986_: *mut LeanObject = core::ptr::null_mut();
    v___x_6985_ = lean_box(1);
    v___x_6986_ = l_Lean_MessageData_ofFormat(v___x_6985_);
    return v___x_6986_;
}
pub unsafe fn _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3_spec__7_spec__8_spec__11___closed__3()
-> *mut LeanObject {
    let mut v___x_6990_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6991_: *mut LeanObject = core::ptr::null_mut();
    v___x_6990_ = l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3_spec__7_spec__8_spec__11___closed__2;
    v___x_6991_ = l_Lean_MessageData_ofFormat(v___x_6990_);
    return v___x_6991_;
}
pub unsafe fn l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3_spec__7_spec__8_spec__11(
    mut v_x_6992_: *mut LeanObject,
    mut v_x_6993_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_head_6994_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_6995_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6997_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6998_: u8 = 0;
    let mut v_before_6999_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7001_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7002_: u8 = 0;
    let mut v___x_7003_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7005_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7006_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7008_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7009_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7010_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7011_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7013_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7014_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7015_: u8 = 0;
    let mut v_unused_7016_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7017_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_6993_) == 0 {
                    return v_x_6992_;
                } else {
                    v_head_6994_ = lean_ctor_get(v_x_6993_, 0);
                    v_tail_6995_ = lean_ctor_get(v_x_6993_, 1);
                    v_isSharedCheck_7017_ = (!lean_is_exclusive(v_x_6993_)) as u8;
                    if v_isSharedCheck_7017_ == 0 {
                        v___x_6997_ = v_x_6993_;
                        v_isShared_6998_ = v_isSharedCheck_7017_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_tail_6995_);
                        lean_inc(v_head_6994_);
                        lean_dec(v_x_6993_);
                        v___x_6997_ = lean_box(0);
                        v_isShared_6998_ = v_isSharedCheck_7017_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_before_6999_ = lean_ctor_get(v_head_6994_, 0);
                v_isSharedCheck_7015_ = (!lean_is_exclusive(v_head_6994_)) as u8;
                if v_isSharedCheck_7015_ == 0 {
                    v_unused_7016_ = lean_ctor_get(v_head_6994_, 1);
                    lean_dec(v_unused_7016_);
                    v___x_7001_ = v_head_6994_;
                    v_isShared_7002_ = v_isSharedCheck_7015_;
                    state = 2;
                    continue;
                } else {
                    lean_inc(v_before_6999_);
                    lean_dec(v_head_6994_);
                    v___x_7001_ = lean_box(0);
                    v_isShared_7002_ = v_isSharedCheck_7015_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_7003_ = lean_obj_once(core::ptr::addr_of_mut!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3_spec__7_spec__8_spec__11___closed__0), core::ptr::addr_of_mut!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3_spec__7_spec__8_spec__11___closed__0_once), _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3_spec__7_spec__8_spec__11___closed__0);
                if v_isShared_7002_ == 0 {
                    lean_ctor_set_tag(v___x_7001_, 7);
                    lean_ctor_set(v___x_7001_, 1, v___x_7003_);
                    lean_ctor_set(v___x_7001_, 0, v_x_6992_);
                    v___x_7005_ = v___x_7001_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_7014_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_7014_, 0, v_x_6992_);
                    lean_ctor_set(v_reuseFailAlloc_7014_, 1, v___x_7003_);
                    v___x_7005_ = v_reuseFailAlloc_7014_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_7006_ = lean_obj_once(core::ptr::addr_of_mut!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3_spec__7_spec__8_spec__11___closed__3), core::ptr::addr_of_mut!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3_spec__7_spec__8_spec__11___closed__3_once), _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3_spec__7_spec__8_spec__11___closed__3);
                if v_isShared_6998_ == 0 {
                    lean_ctor_set_tag(v___x_6997_, 7);
                    lean_ctor_set(v___x_6997_, 1, v___x_7006_);
                    lean_ctor_set(v___x_6997_, 0, v___x_7005_);
                    v___x_7008_ = v___x_6997_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_7013_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_7013_, 0, v___x_7005_);
                    lean_ctor_set(v_reuseFailAlloc_7013_, 1, v___x_7006_);
                    v___x_7008_ = v_reuseFailAlloc_7013_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_7009_ = l_Lean_MessageData_ofSyntax(v_before_6999_);
                v___x_7010_ = l_Lean_indentD(v___x_7009_);
                v___x_7011_ = lean_alloc_ctor(7, 2, (0) as u32);
                lean_ctor_set(v___x_7011_, 0, v___x_7008_);
                lean_ctor_set(v___x_7011_, 1, v___x_7010_);
                v_x_6992_ = v___x_7011_;
                v_x_6993_ = v_tail_6995_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3_spec__7_spec__8_spec__10(
    mut v_opts_7018_: *mut LeanObject,
    mut v_opt_7019_: *mut LeanObject,
) -> u8 {
    let mut v_name_7020_: *mut LeanObject = core::ptr::null_mut();
    let mut v_defValue_7021_: *mut LeanObject = core::ptr::null_mut();
    let mut v_map_7022_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7023_: *mut LeanObject = core::ptr::null_mut();
    v_name_7020_ = lean_ctor_get(v_opt_7019_, 0);
    v_defValue_7021_ = lean_ctor_get(v_opt_7019_, 1);
    v_map_7022_ = lean_ctor_get(v_opts_7018_, 0);
    v___x_7023_ =
        l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(
            v_map_7022_,
            v_name_7020_,
        );
    if lean_obj_tag(v___x_7023_) == 0 {
        let mut v___x_7024_: u8 = 0;
        v___x_7024_ = (lean_unbox(v_defValue_7021_) as u8);
        return v___x_7024_;
    } else {
        let mut v_val_7025_: *mut LeanObject = core::ptr::null_mut();
        v_val_7025_ = lean_ctor_get(v___x_7023_, 0);
        lean_inc(v_val_7025_);
        lean_dec_ref_known(v___x_7023_, 1);
        if lean_obj_tag(v_val_7025_) == 1 {
            let mut v_v_7026_: u8 = 0;
            v_v_7026_ = lean_ctor_get_uint8(v_val_7025_, 0 as u32);
            lean_dec_ref_known(v_val_7025_, 0);
            return v_v_7026_;
        } else {
            let mut v___x_7027_: u8 = 0;
            lean_dec(v_val_7025_);
            v___x_7027_ = (lean_unbox(v_defValue_7021_) as u8);
            return v___x_7027_;
        }
    }
}
pub unsafe fn l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3_spec__7_spec__8_spec__10___boxed(
    mut v_opts_7028_: *mut LeanObject,
    mut v_opt_7029_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_7030_: u8 = 0;
    let mut v_r_7031_: *mut LeanObject = core::ptr::null_mut();
    v_res_7030_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3_spec__7_spec__8_spec__10(v_opts_7028_, v_opt_7029_);
    lean_dec_ref(v_opt_7029_);
    lean_dec_ref(v_opts_7028_);
    v_r_7031_ = lean_box((v_res_7030_) as usize);
    return v_r_7031_;
}
pub unsafe fn _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3_spec__7_spec__8___redArg___closed__2()
-> *mut LeanObject {
    let mut v___x_7035_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7036_: *mut LeanObject = core::ptr::null_mut();
    v___x_7035_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3_spec__7_spec__8___redArg___closed__1;
    v___x_7036_ = l_Lean_MessageData_ofFormat(v___x_7035_);
    return v___x_7036_;
}
pub unsafe fn l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3_spec__7_spec__8___redArg(
    mut v_msgData_7037_: *mut LeanObject,
    mut v_macroStack_7038_: *mut LeanObject,
    mut v___y_7039_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_options_7041_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7042_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7043_: u8 = 0;
    let mut v___x_7044_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7045_: *mut LeanObject = core::ptr::null_mut();
    let mut v_head_7046_: *mut LeanObject = core::ptr::null_mut();
    let mut v_after_7047_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7049_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7050_: u8 = 0;
    let mut v___x_7051_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7053_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7054_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7055_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7056_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7057_: *mut LeanObject = core::ptr::null_mut();
    let mut v_msgData_7058_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7059_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7060_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7061_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7062_: u8 = 0;
    let mut v_unused_7063_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_options_7041_ = lean_ctor_get(v___y_7039_, 2);
                v___x_7042_ = l_Lean_Elab_pp_macroStack;
                v___x_7043_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3_spec__7_spec__8_spec__10(v_options_7041_, v___x_7042_);
                if v___x_7043_ == 0 {
                    lean_dec(v_macroStack_7038_);
                    v___x_7044_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_7044_, 0, v_msgData_7037_);
                    return v___x_7044_;
                } else {
                    if lean_obj_tag(v_macroStack_7038_) == 0 {
                        v___x_7045_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v___x_7045_, 0, v_msgData_7037_);
                        return v___x_7045_;
                    } else {
                        v_head_7046_ = lean_ctor_get(v_macroStack_7038_, 0);
                        lean_inc(v_head_7046_);
                        v_after_7047_ = lean_ctor_get(v_head_7046_, 1);
                        v_isSharedCheck_7062_ = (!lean_is_exclusive(v_head_7046_)) as u8;
                        if v_isSharedCheck_7062_ == 0 {
                            v_unused_7063_ = lean_ctor_get(v_head_7046_, 0);
                            lean_dec(v_unused_7063_);
                            v___x_7049_ = v_head_7046_;
                            v_isShared_7050_ = v_isSharedCheck_7062_;
                            state = 1;
                            continue;
                        } else {
                            lean_inc(v_after_7047_);
                            lean_dec(v_head_7046_);
                            v___x_7049_ = lean_box(0);
                            v_isShared_7050_ = v_isSharedCheck_7062_;
                            state = 1;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v___x_7051_ = lean_obj_once(core::ptr::addr_of_mut!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3_spec__7_spec__8_spec__11___closed__0), core::ptr::addr_of_mut!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3_spec__7_spec__8_spec__11___closed__0_once), _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3_spec__7_spec__8_spec__11___closed__0);
                if v_isShared_7050_ == 0 {
                    lean_ctor_set_tag(v___x_7049_, 7);
                    lean_ctor_set(v___x_7049_, 1, v___x_7051_);
                    lean_ctor_set(v___x_7049_, 0, v_msgData_7037_);
                    v___x_7053_ = v___x_7049_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_7061_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_7061_, 0, v_msgData_7037_);
                    lean_ctor_set(v_reuseFailAlloc_7061_, 1, v___x_7051_);
                    v___x_7053_ = v_reuseFailAlloc_7061_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_7054_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3_spec__7_spec__8___redArg___closed__2), core::ptr::addr_of_mut!(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3_spec__7_spec__8___redArg___closed__2_once), _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3_spec__7_spec__8___redArg___closed__2);
                v___x_7055_ = lean_alloc_ctor(7, 2, (0) as u32);
                lean_ctor_set(v___x_7055_, 0, v___x_7053_);
                lean_ctor_set(v___x_7055_, 1, v___x_7054_);
                v___x_7056_ = l_Lean_MessageData_ofSyntax(v_after_7047_);
                v___x_7057_ = l_Lean_indentD(v___x_7056_);
                v_msgData_7058_ = lean_alloc_ctor(7, 2, (0) as u32);
                lean_ctor_set(v_msgData_7058_, 0, v___x_7055_);
                lean_ctor_set(v_msgData_7058_, 1, v___x_7057_);
                v___x_7059_ = l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3_spec__7_spec__8_spec__11(v_msgData_7058_, v_macroStack_7038_);
                v___x_7060_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_7060_, 0, v___x_7059_);
                return v___x_7060_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3_spec__7_spec__8___redArg___boxed(
    mut v_msgData_7064_: *mut LeanObject,
    mut v_macroStack_7065_: *mut LeanObject,
    mut v___y_7066_: *mut LeanObject,
    mut v___y_7067_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_7068_: *mut LeanObject = core::ptr::null_mut();
    v_res_7068_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3_spec__7_spec__8___redArg(v_msgData_7064_, v_macroStack_7065_, v___y_7066_);
    lean_dec_ref(v___y_7066_);
    return v_res_7068_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3_spec__7___redArg(
    mut v_msg_7069_: *mut LeanObject,
    mut v___y_7070_: *mut LeanObject,
    mut v___y_7071_: *mut LeanObject,
    mut v___y_7072_: *mut LeanObject,
    mut v___y_7073_: *mut LeanObject,
    mut v___y_7074_: *mut LeanObject,
    mut v___y_7075_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_ref_7077_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7078_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_7079_: *mut LeanObject = core::ptr::null_mut();
    let mut v_macroStack_7080_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7081_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7082_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_7083_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7085_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7086_: u8 = 0;
    let mut v___x_7087_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7089_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7090_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7091_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ref_7077_ = lean_ctor_get(v___y_7074_, 5);
                v___x_7078_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Tactic_elabRewrite_spec__3_spec__4_spec__9(v_msg_7069_, v___y_7072_, v___y_7073_, v___y_7074_, v___y_7075_);
                v_a_7079_ = lean_ctor_get(v___x_7078_, 0);
                lean_inc(v_a_7079_);
                lean_dec_ref(v___x_7078_);
                v_macroStack_7080_ = lean_ctor_get(v___y_7070_, 1);
                v___x_7081_ = l_Lean_Elab_getBetterRef(v_ref_7077_, v_macroStack_7080_);
                lean_inc(v_macroStack_7080_);
                v___x_7082_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3_spec__7_spec__8___redArg(v_a_7079_, v_macroStack_7080_, v___y_7074_);
                v_a_7083_ = lean_ctor_get(v___x_7082_, 0);
                v_isSharedCheck_7091_ = (!lean_is_exclusive(v___x_7082_)) as u8;
                if v_isSharedCheck_7091_ == 0 {
                    v___x_7085_ = v___x_7082_;
                    v_isShared_7086_ = v_isSharedCheck_7091_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_a_7083_);
                    lean_dec(v___x_7082_);
                    v___x_7085_ = lean_box(0);
                    v_isShared_7086_ = v_isSharedCheck_7091_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_7087_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_7087_, 0, v___x_7081_);
                lean_ctor_set(v___x_7087_, 1, v_a_7083_);
                if v_isShared_7086_ == 0 {
                    lean_ctor_set_tag(v___x_7085_, 1);
                    lean_ctor_set(v___x_7085_, 0, v___x_7087_);
                    v___x_7089_ = v___x_7085_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_7090_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_7090_, 0, v___x_7087_);
                    v___x_7089_ = v_reuseFailAlloc_7090_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_7089_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3_spec__7___redArg___boxed(
    mut v_msg_7092_: *mut LeanObject,
    mut v___y_7093_: *mut LeanObject,
    mut v___y_7094_: *mut LeanObject,
    mut v___y_7095_: *mut LeanObject,
    mut v___y_7096_: *mut LeanObject,
    mut v___y_7097_: *mut LeanObject,
    mut v___y_7098_: *mut LeanObject,
    mut v___y_7099_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_7100_: *mut LeanObject = core::ptr::null_mut();
    v_res_7100_ = l_Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3_spec__7___redArg(v_msg_7092_, v___y_7093_, v___y_7094_, v___y_7095_, v___y_7096_, v___y_7097_, v___y_7098_);
    lean_dec(v___y_7098_);
    lean_dec_ref(v___y_7097_);
    lean_dec(v___y_7096_);
    lean_dec_ref(v___y_7095_);
    lean_dec(v___y_7094_);
    lean_dec_ref(v___y_7093_);
    return v_res_7100_;
}
pub unsafe fn l_Lean_instantiateMVars___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3_spec__6___redArg(
    mut v_e_7101_: *mut LeanObject,
    mut v___y_7102_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_7104_: u8 = 0;
    let mut v___x_7105_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7106_: *mut LeanObject = core::ptr::null_mut();
    let mut v_mctx_7107_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7108_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_7109_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_7110_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7111_: *mut LeanObject = core::ptr::null_mut();
    let mut v_cache_7112_: *mut LeanObject = core::ptr::null_mut();
    let mut v_zetaDeltaFVarIds_7113_: *mut LeanObject = core::ptr::null_mut();
    let mut v_postponed_7114_: *mut LeanObject = core::ptr::null_mut();
    let mut v_diag_7115_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7117_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7118_: u8 = 0;
    let mut v___x_7120_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7121_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7122_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7123_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7124_: u8 = 0;
    let mut v_unused_7125_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_7104_ = l_Lean_Expr_hasMVar(v_e_7101_);
                if v___x_7104_ == 0 {
                    v___x_7105_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_7105_, 0, v_e_7101_);
                    return v___x_7105_;
                } else {
                    v___x_7106_ = lean_st_ref_get(v___y_7102_);
                    v_mctx_7107_ = lean_ctor_get(v___x_7106_, 0);
                    lean_inc_ref(v_mctx_7107_);
                    lean_dec(v___x_7106_);
                    v___x_7108_ = l_Lean_instantiateMVarsCore(v_mctx_7107_, v_e_7101_);
                    v_fst_7109_ = lean_ctor_get(v___x_7108_, 0);
                    lean_inc(v_fst_7109_);
                    v_snd_7110_ = lean_ctor_get(v___x_7108_, 1);
                    lean_inc(v_snd_7110_);
                    lean_dec_ref(v___x_7108_);
                    v___x_7111_ = lean_st_ref_take(v___y_7102_);
                    v_cache_7112_ = lean_ctor_get(v___x_7111_, 1);
                    v_zetaDeltaFVarIds_7113_ = lean_ctor_get(v___x_7111_, 2);
                    v_postponed_7114_ = lean_ctor_get(v___x_7111_, 3);
                    v_diag_7115_ = lean_ctor_get(v___x_7111_, 4);
                    v_isSharedCheck_7124_ = (!lean_is_exclusive(v___x_7111_)) as u8;
                    if v_isSharedCheck_7124_ == 0 {
                        v_unused_7125_ = lean_ctor_get(v___x_7111_, 0);
                        lean_dec(v_unused_7125_);
                        v___x_7117_ = v___x_7111_;
                        v_isShared_7118_ = v_isSharedCheck_7124_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_diag_7115_);
                        lean_inc(v_postponed_7114_);
                        lean_inc(v_zetaDeltaFVarIds_7113_);
                        lean_inc(v_cache_7112_);
                        lean_dec(v___x_7111_);
                        v___x_7117_ = lean_box(0);
                        v_isShared_7118_ = v_isSharedCheck_7124_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_7118_ == 0 {
                    lean_ctor_set(v___x_7117_, 0, v_snd_7110_);
                    v___x_7120_ = v___x_7117_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_7123_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_7123_, 0, v_snd_7110_);
                    lean_ctor_set(v_reuseFailAlloc_7123_, 1, v_cache_7112_);
                    lean_ctor_set(v_reuseFailAlloc_7123_, 2, v_zetaDeltaFVarIds_7113_);
                    lean_ctor_set(v_reuseFailAlloc_7123_, 3, v_postponed_7114_);
                    lean_ctor_set(v_reuseFailAlloc_7123_, 4, v_diag_7115_);
                    v___x_7120_ = v_reuseFailAlloc_7123_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_7121_ = lean_st_ref_set(v___y_7102_, v___x_7120_);
                v___x_7122_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_7122_, 0, v_fst_7109_);
                return v___x_7122_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_instantiateMVars___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3_spec__6___redArg___boxed(
    mut v_e_7126_: *mut LeanObject,
    mut v___y_7127_: *mut LeanObject,
    mut v___y_7128_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_7129_: *mut LeanObject = core::ptr::null_mut();
    v_res_7129_ = l_Lean_instantiateMVars___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3_spec__6___redArg(v_e_7126_, v___y_7127_);
    lean_dec(v___y_7127_);
    return v_res_7129_;
}
pub unsafe fn _init_l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3_spec__8___redArg___closed__0()
-> *mut LeanObject {
    let mut v___x_7130_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7131_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7132_: *mut LeanObject = core::ptr::null_mut();
    v___x_7130_ = lean_box(0);
    v___x_7131_ = l_Lean_Elab_abortTermExceptionId;
    v___x_7132_ = lean_alloc_ctor(1, 2, (0) as u32);
    lean_ctor_set(v___x_7132_, 0, v___x_7131_);
    lean_ctor_set(v___x_7132_, 1, v___x_7130_);
    return v___x_7132_;
}
pub unsafe fn l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3_spec__8___redArg()
-> *mut LeanObject {
    let mut v___x_7134_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7135_: *mut LeanObject = core::ptr::null_mut();
    v___x_7134_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3_spec__8___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3_spec__8___redArg___closed__0_once), _init_l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3_spec__8___redArg___closed__0);
    v___x_7135_ = lean_alloc_ctor(1, 1, (0) as u32);
    lean_ctor_set(v___x_7135_, 0, v___x_7134_);
    return v___x_7135_;
}
pub unsafe fn l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3_spec__8___redArg___boxed(
    mut v___y_7136_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_7137_: *mut LeanObject = core::ptr::null_mut();
    v_res_7137_ = l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3_spec__8___redArg();
    return v_res_7137_;
}
pub unsafe fn _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__2_spec__4___closed__2()
-> *mut LeanObject {
    let mut v___x_7143_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7144_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7145_: *mut LeanObject = core::ptr::null_mut();
    v___x_7143_ = lean_box(0);
    v___x_7144_ = l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__2_spec__4___closed__1;
    v___x_7145_ = l_Lean_Expr_const___override(v___x_7144_, v___x_7143_);
    return v___x_7145_;
}
pub unsafe fn _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__2_spec__4___closed__3()
-> *mut LeanObject {
    let mut v___x_7146_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ty_x3f_7147_: *mut LeanObject = core::ptr::null_mut();
    v___x_7146_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__2_spec__4___closed__2), core::ptr::addr_of_mut!(l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__2_spec__4___closed__2_once), _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__2_spec__4___closed__2);
    v_ty_x3f_7147_ = lean_alloc_ctor(1, 1, (0) as u32);
    lean_ctor_set(v_ty_x3f_7147_, 0, v___x_7146_);
    return v_ty_x3f_7147_;
}
pub unsafe fn _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__2_spec__4___closed__5()
-> *mut LeanObject {
    let mut v___x_7149_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7150_: *mut LeanObject = core::ptr::null_mut();
    v___x_7149_ = l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__2_spec__4___closed__4;
    v___x_7150_ = l_Lean_stringToMessageData(v___x_7149_);
    return v___x_7150_;
}
pub unsafe fn _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__2_spec__4___closed__6()
-> *mut LeanObject {
    let mut v___x_7151_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7152_: *mut LeanObject = core::ptr::null_mut();
    v___x_7151_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__2_spec__4___closed__2), core::ptr::addr_of_mut!(l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__2_spec__4___closed__2_once), _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__2_spec__4___closed__2);
    v___x_7152_ = l_Lean_MessageData_ofExpr(v___x_7151_);
    return v___x_7152_;
}
pub unsafe fn _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__2_spec__4___closed__7()
-> *mut LeanObject {
    let mut v___x_7153_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7154_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7155_: *mut LeanObject = core::ptr::null_mut();
    v___x_7153_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__2_spec__4___closed__6), core::ptr::addr_of_mut!(l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__2_spec__4___closed__6_once), _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__2_spec__4___closed__6);
    v___x_7154_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__2_spec__4___closed__5), core::ptr::addr_of_mut!(l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__2_spec__4___closed__5_once), _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__2_spec__4___closed__5);
    v___x_7155_ = lean_alloc_ctor(7, 2, (0) as u32);
    lean_ctor_set(v___x_7155_, 0, v___x_7154_);
    lean_ctor_set(v___x_7155_, 1, v___x_7153_);
    return v___x_7155_;
}
pub unsafe fn _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__2_spec__4___closed__8()
-> *mut LeanObject {
    let mut v___x_7156_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7157_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7158_: *mut LeanObject = core::ptr::null_mut();
    v___x_7156_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_withRWRulesSeq_go___closed__3), core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_withRWRulesSeq_go___closed__3_once), _init_l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_withRWRulesSeq_go___closed__3);
    v___x_7157_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__2_spec__4___closed__7), core::ptr::addr_of_mut!(l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__2_spec__4___closed__7_once), _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__2_spec__4___closed__7);
    v___x_7158_ = lean_alloc_ctor(7, 2, (0) as u32);
    lean_ctor_set(v___x_7158_, 0, v___x_7157_);
    lean_ctor_set(v___x_7158_, 1, v___x_7156_);
    return v___x_7158_;
}
pub unsafe fn _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__2_spec__4___closed__10()
-> *mut LeanObject {
    let mut v___x_7160_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7161_: *mut LeanObject = core::ptr::null_mut();
    v___x_7160_ = l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__2_spec__4___closed__9;
    v___x_7161_ = l_Lean_stringToMessageData(v___x_7160_);
    return v___x_7161_;
}
pub unsafe fn _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__2_spec__4___closed__12()
-> *mut LeanObject {
    let mut v___x_7163_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7164_: *mut LeanObject = core::ptr::null_mut();
    v___x_7163_ = l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__2_spec__4___closed__11;
    v___x_7164_ = l_Lean_stringToMessageData(v___x_7163_);
    return v___x_7164_;
}
pub unsafe fn l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__2_spec__4(
    mut v_stx_7165_: *mut LeanObject,
    mut v_a_7166_: *mut LeanObject,
    mut v_a_7167_: *mut LeanObject,
    mut v_a_7168_: *mut LeanObject,
    mut v_a_7169_: *mut LeanObject,
    mut v_a_7170_: *mut LeanObject,
    mut v_a_7171_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_ty_x3f_7173_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7174_: u8 = 0;
    let mut v___x_7175_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7176_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7177_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7178_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fileName_7179_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fileMap_7180_: *mut LeanObject = core::ptr::null_mut();
    let mut v_options_7181_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currRecDepth_7182_: *mut LeanObject = core::ptr::null_mut();
    let mut v_maxRecDepth_7183_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ref_7184_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currNamespace_7185_: *mut LeanObject = core::ptr::null_mut();
    let mut v_openDecls_7186_: *mut LeanObject = core::ptr::null_mut();
    let mut v_initHeartbeats_7187_: *mut LeanObject = core::ptr::null_mut();
    let mut v_maxHeartbeats_7188_: *mut LeanObject = core::ptr::null_mut();
    let mut v_quotContext_7189_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currMacroScope_7190_: *mut LeanObject = core::ptr::null_mut();
    let mut v_diag_7191_: u8 = 0;
    let mut v_cancelTk_x3f_7192_: *mut LeanObject = core::ptr::null_mut();
    let mut v_suppressElabErrors_7193_: u8 = 0;
    let mut v_inheritedTraceOptions_7194_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7195_: u8 = 0;
    let mut v_ref_7196_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7197_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7198_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_7199_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7200_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_7201_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7203_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7204_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7205_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7206_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7207_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7208_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7209_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7210_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7211_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7212_: u8 = 0;
    let mut v_id_7213_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7215_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7216_: u8 = 0;
    let mut v___x_7217_: u8 = 0;
    let mut v___x_7218_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7219_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7220_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7222_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7223_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7224_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7225_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7226_: u8 = 0;
    let mut v_unused_7227_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7229_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7230_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7231_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7232_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7233_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7234_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7235_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_7236_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7237_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7238_: u8 = 0;
    let mut v___x_7239_: u8 = 0;
    let mut v___y_7241_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7242_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7243_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7244_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7245_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7246_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7247_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_7248_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7249_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_7250_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7251_: u8 = 0;
    let mut v___x_7252_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_7253_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7255_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7256_: u8 = 0;
    let mut v___x_7258_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7259_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7260_: u8 = 0;
    let mut v_a_7261_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7263_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7264_: u8 = 0;
    let mut v___x_7266_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7267_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7268_: u8 = 0;
    let mut v_a_7269_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7271_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7272_: u8 = 0;
    let mut v___x_7274_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7275_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7276_: u8 = 0;
    let mut v___y_7278_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7279_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7280_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7281_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7282_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7283_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7284_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7285_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7286_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7287_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_7288_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7290_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7291_: u8 = 0;
    let mut v___x_7293_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7294_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7295_: u8 = 0;
    let mut v___x_7296_: u8 = 0;
    let mut v___x_7297_: u8 = 0;
    let mut v___x_7298_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_7299_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7301_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7302_: u8 = 0;
    let mut v___x_7304_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7305_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7306_: u8 = 0;
    let mut v_a_7307_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7309_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7310_: u8 = 0;
    let mut v___x_7312_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7313_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7314_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ty_x3f_7173_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__2_spec__4___closed__3), core::ptr::addr_of_mut!(l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__2_spec__4___closed__3_once), _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__2_spec__4___closed__3);
                v___x_7174_ = 1;
                v___x_7175_ = lean_box(0);
                v___x_7176_ = lean_box((v___x_7174_) as usize);
                v___x_7177_ = lean_box((v___x_7174_) as usize);
                lean_inc(v_stx_7165_);
                v___x_7178_ = lean_alloc_closure(
                    l_Lean_Elab_Term_elabTermEnsuringType___boxed as *mut core::ffi::c_void,
                    12,
                    5,
                );
                lean_closure_set(v___x_7178_, 0, v_stx_7165_);
                lean_closure_set(v___x_7178_, 1, v_ty_x3f_7173_);
                lean_closure_set(v___x_7178_, 2, v___x_7176_);
                lean_closure_set(v___x_7178_, 3, v___x_7177_);
                lean_closure_set(v___x_7178_, 4, v___x_7175_);
                v_fileName_7179_ = lean_ctor_get(v_a_7170_, 0);
                v_fileMap_7180_ = lean_ctor_get(v_a_7170_, 1);
                v_options_7181_ = lean_ctor_get(v_a_7170_, 2);
                v_currRecDepth_7182_ = lean_ctor_get(v_a_7170_, 3);
                v_maxRecDepth_7183_ = lean_ctor_get(v_a_7170_, 4);
                v_ref_7184_ = lean_ctor_get(v_a_7170_, 5);
                v_currNamespace_7185_ = lean_ctor_get(v_a_7170_, 6);
                v_openDecls_7186_ = lean_ctor_get(v_a_7170_, 7);
                v_initHeartbeats_7187_ = lean_ctor_get(v_a_7170_, 8);
                v_maxHeartbeats_7188_ = lean_ctor_get(v_a_7170_, 9);
                v_quotContext_7189_ = lean_ctor_get(v_a_7170_, 10);
                v_currMacroScope_7190_ = lean_ctor_get(v_a_7170_, 11);
                v_diag_7191_ = lean_ctor_get_uint8(
                    v_a_7170_,
                    (core::mem::size_of::<*mut LeanObject>() * 14) as u32,
                );
                v_cancelTk_x3f_7192_ = lean_ctor_get(v_a_7170_, 12);
                v_suppressElabErrors_7193_ = lean_ctor_get_uint8(
                    v_a_7170_,
                    (core::mem::size_of::<*mut LeanObject>() * 14 + 1) as u32,
                );
                v_inheritedTraceOptions_7194_ = lean_ctor_get(v_a_7170_, 13);
                v___x_7195_ = 1;
                v_ref_7196_ = l_Lean_replaceRef(v_stx_7165_, v_ref_7184_);
                lean_dec(v_stx_7165_);
                lean_inc_ref(v_inheritedTraceOptions_7194_);
                lean_inc(v_cancelTk_x3f_7192_);
                lean_inc(v_currMacroScope_7190_);
                lean_inc(v_quotContext_7189_);
                lean_inc(v_maxHeartbeats_7188_);
                lean_inc(v_initHeartbeats_7187_);
                lean_inc(v_openDecls_7186_);
                lean_inc(v_currNamespace_7185_);
                lean_inc(v_maxRecDepth_7183_);
                lean_inc(v_currRecDepth_7182_);
                lean_inc_ref(v_options_7181_);
                lean_inc_ref(v_fileMap_7180_);
                lean_inc_ref(v_fileName_7179_);
                v___x_7197_ = lean_alloc_ctor(0, 14, (2) as u32);
                lean_ctor_set(v___x_7197_, 0, v_fileName_7179_);
                lean_ctor_set(v___x_7197_, 1, v_fileMap_7180_);
                lean_ctor_set(v___x_7197_, 2, v_options_7181_);
                lean_ctor_set(v___x_7197_, 3, v_currRecDepth_7182_);
                lean_ctor_set(v___x_7197_, 4, v_maxRecDepth_7183_);
                lean_ctor_set(v___x_7197_, 5, v_ref_7196_);
                lean_ctor_set(v___x_7197_, 6, v_currNamespace_7185_);
                lean_ctor_set(v___x_7197_, 7, v_openDecls_7186_);
                lean_ctor_set(v___x_7197_, 8, v_initHeartbeats_7187_);
                lean_ctor_set(v___x_7197_, 9, v_maxHeartbeats_7188_);
                lean_ctor_set(v___x_7197_, 10, v_quotContext_7189_);
                lean_ctor_set(v___x_7197_, 11, v_currMacroScope_7190_);
                lean_ctor_set(v___x_7197_, 12, v_cancelTk_x3f_7192_);
                lean_ctor_set(v___x_7197_, 13, v_inheritedTraceOptions_7194_);
                lean_ctor_set_uint8(
                    v___x_7197_,
                    (core::mem::size_of::<*mut LeanObject>() * 14) as u32,
                    v_diag_7191_,
                );
                lean_ctor_set_uint8(
                    v___x_7197_,
                    (core::mem::size_of::<*mut LeanObject>() * 14 + 1) as u32,
                    v_suppressElabErrors_7193_,
                );
                v___x_7198_ =
                    l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_withSynthesizeImp(
                        lean_box(0),
                        v___x_7178_,
                        v___x_7195_,
                        v_a_7166_,
                        v_a_7167_,
                        v_a_7168_,
                        v_a_7169_,
                        v___x_7197_,
                        v_a_7171_,
                    );
                if lean_obj_tag(v___x_7198_) == 0 {
                    v_a_7199_ = lean_ctor_get(v___x_7198_, 0);
                    lean_inc(v_a_7199_);
                    lean_dec_ref_known(v___x_7198_, 1);
                    v___x_7200_ = l_Lean_instantiateMVars___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3_spec__6___redArg(v_a_7199_, v_a_7169_);
                    v_a_7201_ = lean_ctor_get(v___x_7200_, 0);
                    lean_inc(v_a_7201_);
                    lean_dec_ref(v___x_7200_);
                    v___x_7296_ = l_Lean_Expr_hasSorry(v_a_7201_);
                    if v___x_7296_ == 0 {
                        v___y_7241_ = v_a_7166_;
                        v___y_7242_ = v_a_7167_;
                        v___y_7243_ = v_a_7168_;
                        v___y_7244_ = v_a_7169_;
                        v___y_7245_ = v___x_7197_;
                        v___y_7246_ = v_a_7171_;
                        state = 5;
                        continue;
                    } else {
                        v___x_7297_ = l_Lean_Expr_hasSyntheticSorry(v_a_7201_);
                        if v___x_7297_ == 0 {
                            v___y_7278_ = v_a_7166_;
                            v___y_7279_ = v_a_7167_;
                            v___y_7280_ = v_a_7168_;
                            v___y_7281_ = v_a_7169_;
                            v___y_7282_ = v___x_7197_;
                            v___y_7283_ = v_a_7171_;
                            state = 12;
                            continue;
                        } else {
                            lean_dec(v_a_7201_);
                            lean_dec_ref_known(v___x_7197_, 14);
                            v___x_7298_ = l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3_spec__8___redArg();
                            v_a_7299_ = lean_ctor_get(v___x_7298_, 0);
                            v_isSharedCheck_7306_ = (!lean_is_exclusive(v___x_7298_)) as u8;
                            if v_isSharedCheck_7306_ == 0 {
                                v___x_7301_ = v___x_7298_;
                                v_isShared_7302_ = v_isSharedCheck_7306_;
                                state = 15;
                                continue;
                            } else {
                                lean_inc(v_a_7299_);
                                lean_dec(v___x_7298_);
                                v___x_7301_ = lean_box(0);
                                v_isShared_7302_ = v_isSharedCheck_7306_;
                                state = 15;
                                continue;
                            }
                        }
                    }
                } else {
                    lean_dec_ref_known(v___x_7197_, 14);
                    v_a_7307_ = lean_ctor_get(v___x_7198_, 0);
                    v_isSharedCheck_7314_ = (!lean_is_exclusive(v___x_7198_)) as u8;
                    if v_isSharedCheck_7314_ == 0 {
                        v___x_7309_ = v___x_7198_;
                        v_isShared_7310_ = v_isSharedCheck_7314_;
                        state = 17;
                        continue;
                    } else {
                        lean_inc(v_a_7307_);
                        lean_dec(v___x_7198_);
                        v___x_7309_ = lean_box(0);
                        v_isShared_7310_ = v_isSharedCheck_7314_;
                        state = 17;
                        continue;
                    }
                }
            }
            1 => {
                if v___y_7212_ == 0 {
                    if lean_obj_tag(v___y_7208_) == 0 {
                        lean_dec_ref_known(v___y_7208_, 2);
                        lean_dec_ref(v___y_7210_);
                        lean_dec(v_a_7201_);
                        return v___y_7205_;
                    } else {
                        v_id_7213_ = lean_ctor_get(v___y_7208_, 0);
                        v_isSharedCheck_7226_ = (!lean_is_exclusive(v___y_7208_)) as u8;
                        if v_isSharedCheck_7226_ == 0 {
                            v_unused_7227_ = lean_ctor_get(v___y_7208_, 1);
                            lean_dec(v_unused_7227_);
                            v___x_7215_ = v___y_7208_;
                            v_isShared_7216_ = v_isSharedCheck_7226_;
                            state = 2;
                            continue;
                        } else {
                            lean_inc(v_id_7213_);
                            lean_dec(v___y_7208_);
                            v___x_7215_ = lean_box(0);
                            v_isShared_7216_ = v_isSharedCheck_7226_;
                            state = 2;
                            continue;
                        }
                    }
                } else {
                    lean_dec_ref(v___y_7210_);
                    lean_dec_ref(v___y_7208_);
                    lean_dec(v_a_7201_);
                    return v___y_7205_;
                }
            }
            2 => {
                v___x_7217_ = l_Lean_instBEqInternalExceptionId_beq(v___y_7207_, v_id_7213_);
                lean_dec(v_id_7213_);
                if v___x_7217_ == 0 {
                    lean_del_object(v___x_7215_);
                    lean_dec_ref(v___y_7210_);
                    lean_dec(v_a_7201_);
                    return v___y_7205_;
                } else {
                    lean_dec_ref(v___y_7205_);
                    v___x_7218_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__2_spec__4___closed__8), core::ptr::addr_of_mut!(l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__2_spec__4___closed__8_once), _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__2_spec__4___closed__8);
                    v___x_7219_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__2_spec__4___closed__10), core::ptr::addr_of_mut!(l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__2_spec__4___closed__10_once), _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__2_spec__4___closed__10);
                    v___x_7220_ = l_Lean_indentExpr(v_a_7201_);
                    if v_isShared_7216_ == 0 {
                        lean_ctor_set_tag(v___x_7215_, 7);
                        lean_ctor_set(v___x_7215_, 1, v___x_7220_);
                        lean_ctor_set(v___x_7215_, 0, v___x_7219_);
                        v___x_7222_ = v___x_7215_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_7225_ = lean_alloc_ctor(7, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_7225_, 0, v___x_7219_);
                        lean_ctor_set(v_reuseFailAlloc_7225_, 1, v___x_7220_);
                        v___x_7222_ = v_reuseFailAlloc_7225_;
                        state = 3;
                        continue;
                    }
                }
            }
            3 => {
                v___x_7223_ = lean_alloc_ctor(7, 2, (0) as u32);
                lean_ctor_set(v___x_7223_, 0, v___x_7222_);
                lean_ctor_set(v___x_7223_, 1, v___x_7218_);
                v___x_7224_ = l_Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3_spec__7___redArg(v___x_7223_, v___y_7211_, v___y_7203_, v___y_7206_, v___y_7204_, v___y_7210_, v___y_7209_);
                lean_dec_ref(v___y_7210_);
                return v___x_7224_;
            }
            4 => {
                lean_inc(v_a_7201_);
                v___x_7235_ = l_Lean_Elab_ConfigEval_instEvalExprApplyNewGoals_evalExpr(
                    v_a_7201_,
                    v___y_7231_,
                    v___y_7232_,
                    v___y_7233_,
                    v___y_7234_,
                );
                if lean_obj_tag(v___x_7235_) == 0 {
                    lean_dec_ref(v___y_7233_);
                    lean_dec(v_a_7201_);
                    return v___x_7235_;
                } else {
                    v_a_7236_ = lean_ctor_get(v___x_7235_, 0);
                    lean_inc(v_a_7236_);
                    v___x_7237_ = l_Lean_Elab_unsupportedSyntaxExceptionId;
                    v___x_7238_ = l_Lean_Exception_isInterrupt(v_a_7236_);
                    if v___x_7238_ == 0 {
                        lean_inc(v_a_7236_);
                        v___x_7239_ = l_Lean_Exception_isRuntime(v_a_7236_);
                        v___y_7203_ = v___y_7230_;
                        v___y_7204_ = v___y_7232_;
                        v___y_7205_ = v___x_7235_;
                        v___y_7206_ = v___y_7231_;
                        v___y_7207_ = v___x_7237_;
                        v___y_7208_ = v_a_7236_;
                        v___y_7209_ = v___y_7234_;
                        v___y_7210_ = v___y_7233_;
                        v___y_7211_ = v___y_7229_;
                        v___y_7212_ = v___x_7239_;
                        state = 1;
                        continue;
                    } else {
                        v___y_7203_ = v___y_7230_;
                        v___y_7204_ = v___y_7232_;
                        v___y_7205_ = v___x_7235_;
                        v___y_7206_ = v___y_7231_;
                        v___y_7207_ = v___x_7237_;
                        v___y_7208_ = v_a_7236_;
                        v___y_7209_ = v___y_7234_;
                        v___y_7210_ = v___y_7233_;
                        v___y_7211_ = v___y_7229_;
                        v___y_7212_ = v___x_7238_;
                        state = 1;
                        continue;
                    }
                }
            }
            5 => {
                lean_inc(v_a_7201_);
                v___x_7247_ = l_Lean_Meta_getMVars(
                    v_a_7201_,
                    v___y_7243_,
                    v___y_7244_,
                    v___y_7245_,
                    v___y_7246_,
                );
                if lean_obj_tag(v___x_7247_) == 0 {
                    v_a_7248_ = lean_ctor_get(v___x_7247_, 0);
                    lean_inc(v_a_7248_);
                    lean_dec_ref_known(v___x_7247_, 1);
                    v___x_7249_ = l_Lean_Elab_Term_logUnassignedUsingErrorInfos(
                        v_a_7248_,
                        v___x_7175_,
                        v___y_7241_,
                        v___y_7242_,
                        v___y_7243_,
                        v___y_7244_,
                        v___y_7245_,
                        v___y_7246_,
                    );
                    lean_dec(v_a_7248_);
                    if lean_obj_tag(v___x_7249_) == 0 {
                        v_a_7250_ = lean_ctor_get(v___x_7249_, 0);
                        lean_inc(v_a_7250_);
                        lean_dec_ref_known(v___x_7249_, 1);
                        v___x_7251_ = (lean_unbox(v_a_7250_) as u8);
                        lean_dec(v_a_7250_);
                        if v___x_7251_ == 0 {
                            v___y_7229_ = v___y_7241_;
                            v___y_7230_ = v___y_7242_;
                            v___y_7231_ = v___y_7243_;
                            v___y_7232_ = v___y_7244_;
                            v___y_7233_ = v___y_7245_;
                            v___y_7234_ = v___y_7246_;
                            state = 4;
                            continue;
                        } else {
                            lean_dec_ref(v___y_7245_);
                            lean_dec(v_a_7201_);
                            v___x_7252_ = l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3_spec__8___redArg();
                            v_a_7253_ = lean_ctor_get(v___x_7252_, 0);
                            v_isSharedCheck_7260_ = (!lean_is_exclusive(v___x_7252_)) as u8;
                            if v_isSharedCheck_7260_ == 0 {
                                v___x_7255_ = v___x_7252_;
                                v_isShared_7256_ = v_isSharedCheck_7260_;
                                state = 6;
                                continue;
                            } else {
                                lean_inc(v_a_7253_);
                                lean_dec(v___x_7252_);
                                v___x_7255_ = lean_box(0);
                                v_isShared_7256_ = v_isSharedCheck_7260_;
                                state = 6;
                                continue;
                            }
                        }
                    } else {
                        lean_dec_ref(v___y_7245_);
                        lean_dec(v_a_7201_);
                        v_a_7261_ = lean_ctor_get(v___x_7249_, 0);
                        v_isSharedCheck_7268_ = (!lean_is_exclusive(v___x_7249_)) as u8;
                        if v_isSharedCheck_7268_ == 0 {
                            v___x_7263_ = v___x_7249_;
                            v_isShared_7264_ = v_isSharedCheck_7268_;
                            state = 8;
                            continue;
                        } else {
                            lean_inc(v_a_7261_);
                            lean_dec(v___x_7249_);
                            v___x_7263_ = lean_box(0);
                            v_isShared_7264_ = v_isSharedCheck_7268_;
                            state = 8;
                            continue;
                        }
                    }
                } else {
                    lean_dec_ref(v___y_7245_);
                    lean_dec(v_a_7201_);
                    v_a_7269_ = lean_ctor_get(v___x_7247_, 0);
                    v_isSharedCheck_7276_ = (!lean_is_exclusive(v___x_7247_)) as u8;
                    if v_isSharedCheck_7276_ == 0 {
                        v___x_7271_ = v___x_7247_;
                        v_isShared_7272_ = v_isSharedCheck_7276_;
                        state = 10;
                        continue;
                    } else {
                        lean_inc(v_a_7269_);
                        lean_dec(v___x_7247_);
                        v___x_7271_ = lean_box(0);
                        v_isShared_7272_ = v_isSharedCheck_7276_;
                        state = 10;
                        continue;
                    }
                }
            }
            6 => {
                if v_isShared_7256_ == 0 {
                    v___x_7258_ = v___x_7255_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_7259_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_7259_, 0, v_a_7253_);
                    v___x_7258_ = v_reuseFailAlloc_7259_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_7258_;
            }
            8 => {
                if v_isShared_7264_ == 0 {
                    v___x_7266_ = v___x_7263_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_7267_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_7267_, 0, v_a_7261_);
                    v___x_7266_ = v_reuseFailAlloc_7267_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_7266_;
            }
            10 => {
                if v_isShared_7272_ == 0 {
                    v___x_7274_ = v___x_7271_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_7275_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_7275_, 0, v_a_7269_);
                    v___x_7274_ = v_reuseFailAlloc_7275_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                return v___x_7274_;
            }
            12 => {
                v___x_7284_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__2_spec__4___closed__12), core::ptr::addr_of_mut!(l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__2_spec__4___closed__12_once), _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__2_spec__4___closed__12);
                v___x_7285_ = l_Lean_indentExpr(v_a_7201_);
                v___x_7286_ = lean_alloc_ctor(7, 2, (0) as u32);
                lean_ctor_set(v___x_7286_, 0, v___x_7284_);
                lean_ctor_set(v___x_7286_, 1, v___x_7285_);
                v___x_7287_ = l_Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3_spec__7___redArg(v___x_7286_, v___y_7278_, v___y_7279_, v___y_7280_, v___y_7281_, v___y_7282_, v___y_7283_);
                lean_dec_ref(v___y_7282_);
                v_a_7288_ = lean_ctor_get(v___x_7287_, 0);
                v_isSharedCheck_7295_ = (!lean_is_exclusive(v___x_7287_)) as u8;
                if v_isSharedCheck_7295_ == 0 {
                    v___x_7290_ = v___x_7287_;
                    v_isShared_7291_ = v_isSharedCheck_7295_;
                    state = 13;
                    continue;
                } else {
                    lean_inc(v_a_7288_);
                    lean_dec(v___x_7287_);
                    v___x_7290_ = lean_box(0);
                    v_isShared_7291_ = v_isSharedCheck_7295_;
                    state = 13;
                    continue;
                }
            }
            13 => {
                if v_isShared_7291_ == 0 {
                    v___x_7293_ = v___x_7290_;
                    state = 14;
                    continue;
                } else {
                    v_reuseFailAlloc_7294_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_7294_, 0, v_a_7288_);
                    v___x_7293_ = v_reuseFailAlloc_7294_;
                    state = 14;
                    continue;
                }
            }
            14 => {
                return v___x_7293_;
            }
            15 => {
                if v_isShared_7302_ == 0 {
                    v___x_7304_ = v___x_7301_;
                    state = 16;
                    continue;
                } else {
                    v_reuseFailAlloc_7305_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_7305_, 0, v_a_7299_);
                    v___x_7304_ = v_reuseFailAlloc_7305_;
                    state = 16;
                    continue;
                }
            }
            16 => {
                return v___x_7304_;
            }
            17 => {
                if v_isShared_7310_ == 0 {
                    v___x_7312_ = v___x_7309_;
                    state = 18;
                    continue;
                } else {
                    v_reuseFailAlloc_7313_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_7313_, 0, v_a_7307_);
                    v___x_7312_ = v_reuseFailAlloc_7313_;
                    state = 18;
                    continue;
                }
            }
            18 => {
                return v___x_7312_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__2_spec__4___boxed(
    mut v_stx_7315_: *mut LeanObject,
    mut v_a_7316_: *mut LeanObject,
    mut v_a_7317_: *mut LeanObject,
    mut v_a_7318_: *mut LeanObject,
    mut v_a_7319_: *mut LeanObject,
    mut v_a_7320_: *mut LeanObject,
    mut v_a_7321_: *mut LeanObject,
    mut v_a_7322_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_7323_: *mut LeanObject = core::ptr::null_mut();
    v_res_7323_ = l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__2_spec__4(v_stx_7315_, v_a_7316_, v_a_7317_, v_a_7318_, v_a_7319_, v_a_7320_, v_a_7321_);
    lean_dec(v_a_7321_);
    lean_dec_ref(v_a_7320_);
    lean_dec(v_a_7319_);
    lean_dec_ref(v_a_7318_);
    lean_dec(v_a_7317_);
    lean_dec_ref(v_a_7316_);
    return v_res_7323_;
}
pub unsafe fn l_Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__2(
    mut v_stx_7324_: *mut LeanObject,
    mut v_a_7325_: *mut LeanObject,
    mut v_a_7326_: *mut LeanObject,
    mut v_a_7327_: *mut LeanObject,
    mut v_a_7328_: *mut LeanObject,
    mut v_a_7329_: *mut LeanObject,
    mut v_a_7330_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_fileName_7332_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fileMap_7333_: *mut LeanObject = core::ptr::null_mut();
    let mut v_options_7334_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currRecDepth_7335_: *mut LeanObject = core::ptr::null_mut();
    let mut v_maxRecDepth_7336_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ref_7337_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currNamespace_7338_: *mut LeanObject = core::ptr::null_mut();
    let mut v_openDecls_7339_: *mut LeanObject = core::ptr::null_mut();
    let mut v_initHeartbeats_7340_: *mut LeanObject = core::ptr::null_mut();
    let mut v_maxHeartbeats_7341_: *mut LeanObject = core::ptr::null_mut();
    let mut v_quotContext_7342_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currMacroScope_7343_: *mut LeanObject = core::ptr::null_mut();
    let mut v_diag_7344_: u8 = 0;
    let mut v_cancelTk_x3f_7345_: *mut LeanObject = core::ptr::null_mut();
    let mut v_suppressElabErrors_7346_: u8 = 0;
    let mut v_inheritedTraceOptions_7347_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ref_7348_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7349_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7350_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_7351_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7353_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7354_: u8 = 0;
    let mut v_fst_7355_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7357_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7358_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7359_: u8 = 0;
    let mut v_a_7360_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7362_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7363_: u8 = 0;
    let mut v___x_7364_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7366_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7368_: u8 = 0;
    let mut v_id_7369_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7370_: u8 = 0;
    let mut v___x_7371_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7372_: u8 = 0;
    let mut v___x_7373_: u8 = 0;
    let mut v_reuseFailAlloc_7374_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7375_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_fileName_7332_ = lean_ctor_get(v_a_7329_, 0);
                v_fileMap_7333_ = lean_ctor_get(v_a_7329_, 1);
                v_options_7334_ = lean_ctor_get(v_a_7329_, 2);
                v_currRecDepth_7335_ = lean_ctor_get(v_a_7329_, 3);
                v_maxRecDepth_7336_ = lean_ctor_get(v_a_7329_, 4);
                v_ref_7337_ = lean_ctor_get(v_a_7329_, 5);
                v_currNamespace_7338_ = lean_ctor_get(v_a_7329_, 6);
                v_openDecls_7339_ = lean_ctor_get(v_a_7329_, 7);
                v_initHeartbeats_7340_ = lean_ctor_get(v_a_7329_, 8);
                v_maxHeartbeats_7341_ = lean_ctor_get(v_a_7329_, 9);
                v_quotContext_7342_ = lean_ctor_get(v_a_7329_, 10);
                v_currMacroScope_7343_ = lean_ctor_get(v_a_7329_, 11);
                v_diag_7344_ = lean_ctor_get_uint8(
                    v_a_7329_,
                    (core::mem::size_of::<*mut LeanObject>() * 14) as u32,
                );
                v_cancelTk_x3f_7345_ = lean_ctor_get(v_a_7329_, 12);
                v_suppressElabErrors_7346_ = lean_ctor_get_uint8(
                    v_a_7329_,
                    (core::mem::size_of::<*mut LeanObject>() * 14 + 1) as u32,
                );
                v_inheritedTraceOptions_7347_ = lean_ctor_get(v_a_7329_, 13);
                v_ref_7348_ = l_Lean_replaceRef(v_stx_7324_, v_ref_7337_);
                lean_inc_ref(v_inheritedTraceOptions_7347_);
                lean_inc(v_cancelTk_x3f_7345_);
                lean_inc(v_currMacroScope_7343_);
                lean_inc(v_quotContext_7342_);
                lean_inc(v_maxHeartbeats_7341_);
                lean_inc(v_initHeartbeats_7340_);
                lean_inc(v_openDecls_7339_);
                lean_inc(v_currNamespace_7338_);
                lean_inc(v_maxRecDepth_7336_);
                lean_inc(v_currRecDepth_7335_);
                lean_inc_ref(v_options_7334_);
                lean_inc_ref(v_fileMap_7333_);
                lean_inc_ref(v_fileName_7332_);
                v___x_7349_ = lean_alloc_ctor(0, 14, (2) as u32);
                lean_ctor_set(v___x_7349_, 0, v_fileName_7332_);
                lean_ctor_set(v___x_7349_, 1, v_fileMap_7333_);
                lean_ctor_set(v___x_7349_, 2, v_options_7334_);
                lean_ctor_set(v___x_7349_, 3, v_currRecDepth_7335_);
                lean_ctor_set(v___x_7349_, 4, v_maxRecDepth_7336_);
                lean_ctor_set(v___x_7349_, 5, v_ref_7348_);
                lean_ctor_set(v___x_7349_, 6, v_currNamespace_7338_);
                lean_ctor_set(v___x_7349_, 7, v_openDecls_7339_);
                lean_ctor_set(v___x_7349_, 8, v_initHeartbeats_7340_);
                lean_ctor_set(v___x_7349_, 9, v_maxHeartbeats_7341_);
                lean_ctor_set(v___x_7349_, 10, v_quotContext_7342_);
                lean_ctor_set(v___x_7349_, 11, v_currMacroScope_7343_);
                lean_ctor_set(v___x_7349_, 12, v_cancelTk_x3f_7345_);
                lean_ctor_set(v___x_7349_, 13, v_inheritedTraceOptions_7347_);
                lean_ctor_set_uint8(
                    v___x_7349_,
                    (core::mem::size_of::<*mut LeanObject>() * 14) as u32,
                    v_diag_7344_,
                );
                lean_ctor_set_uint8(
                    v___x_7349_,
                    (core::mem::size_of::<*mut LeanObject>() * 14 + 1) as u32,
                    v_suppressElabErrors_7346_,
                );
                lean_inc(v_stx_7324_);
                v___x_7350_ = l_Lean_Elab_ConfigEval_instEvalTermApplyNewGoals_evalTerm(
                    v_stx_7324_,
                    v_a_7325_,
                    v_a_7326_,
                    v_a_7327_,
                    v_a_7328_,
                    v___x_7349_,
                    v_a_7330_,
                );
                if lean_obj_tag(v___x_7350_) == 0 {
                    lean_dec_ref_known(v___x_7349_, 14);
                    lean_dec(v_stx_7324_);
                    v_a_7351_ = lean_ctor_get(v___x_7350_, 0);
                    v_isSharedCheck_7359_ = (!lean_is_exclusive(v___x_7350_)) as u8;
                    if v_isSharedCheck_7359_ == 0 {
                        v___x_7353_ = v___x_7350_;
                        v_isShared_7354_ = v_isSharedCheck_7359_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_7351_);
                        lean_dec(v___x_7350_);
                        v___x_7353_ = lean_box(0);
                        v_isShared_7354_ = v_isSharedCheck_7359_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_7360_ = lean_ctor_get(v___x_7350_, 0);
                    v_isSharedCheck_7375_ = (!lean_is_exclusive(v___x_7350_)) as u8;
                    if v_isSharedCheck_7375_ == 0 {
                        v___x_7362_ = v___x_7350_;
                        v_isShared_7363_ = v_isSharedCheck_7375_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_7360_);
                        lean_dec(v___x_7350_);
                        v___x_7362_ = lean_box(0);
                        v_isShared_7363_ = v_isSharedCheck_7375_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v_fst_7355_ = lean_ctor_get(v_a_7351_, 0);
                lean_inc(v_fst_7355_);
                lean_dec(v_a_7351_);
                if v_isShared_7354_ == 0 {
                    lean_ctor_set(v___x_7353_, 0, v_fst_7355_);
                    v___x_7357_ = v___x_7353_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_7358_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_7358_, 0, v_fst_7355_);
                    v___x_7357_ = v_reuseFailAlloc_7358_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_7357_;
            }
            3 => {
                v___x_7364_ = l_Lean_Elab_unsupportedSyntaxExceptionId;
                lean_inc(v_a_7360_);
                if v_isShared_7363_ == 0 {
                    v___x_7366_ = v___x_7362_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_7374_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_7374_, 0, v_a_7360_);
                    v___x_7366_ = v_reuseFailAlloc_7374_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_7372_ = l_Lean_Exception_isInterrupt(v_a_7360_);
                if v___x_7372_ == 0 {
                    lean_inc(v_a_7360_);
                    v___x_7373_ = l_Lean_Exception_isRuntime(v_a_7360_);
                    v___y_7368_ = v___x_7373_;
                    state = 5;
                    continue;
                } else {
                    v___y_7368_ = v___x_7372_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                if v___y_7368_ == 0 {
                    if lean_obj_tag(v_a_7360_) == 0 {
                        lean_dec_ref_known(v_a_7360_, 2);
                        lean_dec_ref_known(v___x_7349_, 14);
                        lean_dec(v_stx_7324_);
                        return v___x_7366_;
                    } else {
                        v_id_7369_ = lean_ctor_get(v_a_7360_, 0);
                        lean_inc(v_id_7369_);
                        lean_dec_ref_known(v_a_7360_, 2);
                        v___x_7370_ =
                            l_Lean_instBEqInternalExceptionId_beq(v___x_7364_, v_id_7369_);
                        lean_dec(v_id_7369_);
                        if v___x_7370_ == 0 {
                            lean_dec_ref_known(v___x_7349_, 14);
                            lean_dec(v_stx_7324_);
                            return v___x_7366_;
                        } else {
                            lean_dec_ref(v___x_7366_);
                            v___x_7371_ = l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__2_spec__4(v_stx_7324_, v_a_7325_, v_a_7326_, v_a_7327_, v_a_7328_, v___x_7349_, v_a_7330_);
                            lean_dec_ref_known(v___x_7349_, 14);
                            return v___x_7371_;
                        }
                    }
                } else {
                    lean_dec(v_a_7360_);
                    lean_dec_ref_known(v___x_7349_, 14);
                    lean_dec(v_stx_7324_);
                    return v___x_7366_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__2___boxed(
    mut v_stx_7376_: *mut LeanObject,
    mut v_a_7377_: *mut LeanObject,
    mut v_a_7378_: *mut LeanObject,
    mut v_a_7379_: *mut LeanObject,
    mut v_a_7380_: *mut LeanObject,
    mut v_a_7381_: *mut LeanObject,
    mut v_a_7382_: *mut LeanObject,
    mut v_a_7383_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_7384_: *mut LeanObject = core::ptr::null_mut();
    v_res_7384_ = l_Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__2(v_stx_7376_, v_a_7377_, v_a_7378_, v_a_7379_, v_a_7380_, v_a_7381_, v_a_7382_);
    lean_dec(v_a_7382_);
    lean_dec_ref(v_a_7381_);
    lean_dec(v_a_7380_);
    lean_dec_ref(v_a_7379_);
    lean_dec(v_a_7378_);
    lean_dec_ref(v_a_7377_);
    return v_res_7384_;
}
pub unsafe fn _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__1_spec__2___closed__2()
-> *mut LeanObject {
    let mut v___x_7390_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7391_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7392_: *mut LeanObject = core::ptr::null_mut();
    v___x_7390_ = lean_box(0);
    v___x_7391_ = l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__1_spec__2___closed__1;
    v___x_7392_ = l_Lean_Expr_const___override(v___x_7391_, v___x_7390_);
    return v___x_7392_;
}
pub unsafe fn _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__1_spec__2___closed__3()
-> *mut LeanObject {
    let mut v___x_7393_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ty_x3f_7394_: *mut LeanObject = core::ptr::null_mut();
    v___x_7393_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__1_spec__2___closed__2), core::ptr::addr_of_mut!(l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__1_spec__2___closed__2_once), _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__1_spec__2___closed__2);
    v_ty_x3f_7394_ = lean_alloc_ctor(1, 1, (0) as u32);
    lean_ctor_set(v_ty_x3f_7394_, 0, v___x_7393_);
    return v_ty_x3f_7394_;
}
pub unsafe fn _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__1_spec__2___closed__4()
-> *mut LeanObject {
    let mut v___x_7395_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7396_: *mut LeanObject = core::ptr::null_mut();
    v___x_7395_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__1_spec__2___closed__2), core::ptr::addr_of_mut!(l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__1_spec__2___closed__2_once), _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__1_spec__2___closed__2);
    v___x_7396_ = l_Lean_MessageData_ofExpr(v___x_7395_);
    return v___x_7396_;
}
pub unsafe fn _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__1_spec__2___closed__5()
-> *mut LeanObject {
    let mut v___x_7397_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7398_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7399_: *mut LeanObject = core::ptr::null_mut();
    v___x_7397_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__1_spec__2___closed__4), core::ptr::addr_of_mut!(l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__1_spec__2___closed__4_once), _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__1_spec__2___closed__4);
    v___x_7398_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__2_spec__4___closed__5), core::ptr::addr_of_mut!(l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__2_spec__4___closed__5_once), _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__2_spec__4___closed__5);
    v___x_7399_ = lean_alloc_ctor(7, 2, (0) as u32);
    lean_ctor_set(v___x_7399_, 0, v___x_7398_);
    lean_ctor_set(v___x_7399_, 1, v___x_7397_);
    return v___x_7399_;
}
pub unsafe fn _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__1_spec__2___closed__6()
-> *mut LeanObject {
    let mut v___x_7400_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7401_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7402_: *mut LeanObject = core::ptr::null_mut();
    v___x_7400_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_withRWRulesSeq_go___closed__3), core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_withRWRulesSeq_go___closed__3_once), _init_l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_withRWRulesSeq_go___closed__3);
    v___x_7401_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__1_spec__2___closed__5), core::ptr::addr_of_mut!(l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__1_spec__2___closed__5_once), _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__1_spec__2___closed__5);
    v___x_7402_ = lean_alloc_ctor(7, 2, (0) as u32);
    lean_ctor_set(v___x_7402_, 0, v___x_7401_);
    lean_ctor_set(v___x_7402_, 1, v___x_7400_);
    return v___x_7402_;
}
pub unsafe fn l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__1_spec__2(
    mut v_stx_7403_: *mut LeanObject,
    mut v_a_7404_: *mut LeanObject,
    mut v_a_7405_: *mut LeanObject,
    mut v_a_7406_: *mut LeanObject,
    mut v_a_7407_: *mut LeanObject,
    mut v_a_7408_: *mut LeanObject,
    mut v_a_7409_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_ty_x3f_7411_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7412_: u8 = 0;
    let mut v___x_7413_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7414_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7415_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7416_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fileName_7417_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fileMap_7418_: *mut LeanObject = core::ptr::null_mut();
    let mut v_options_7419_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currRecDepth_7420_: *mut LeanObject = core::ptr::null_mut();
    let mut v_maxRecDepth_7421_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ref_7422_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currNamespace_7423_: *mut LeanObject = core::ptr::null_mut();
    let mut v_openDecls_7424_: *mut LeanObject = core::ptr::null_mut();
    let mut v_initHeartbeats_7425_: *mut LeanObject = core::ptr::null_mut();
    let mut v_maxHeartbeats_7426_: *mut LeanObject = core::ptr::null_mut();
    let mut v_quotContext_7427_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currMacroScope_7428_: *mut LeanObject = core::ptr::null_mut();
    let mut v_diag_7429_: u8 = 0;
    let mut v_cancelTk_x3f_7430_: *mut LeanObject = core::ptr::null_mut();
    let mut v_suppressElabErrors_7431_: u8 = 0;
    let mut v_inheritedTraceOptions_7432_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7433_: u8 = 0;
    let mut v_ref_7434_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7435_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7436_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_7437_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7438_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_7439_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7441_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7442_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7443_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7444_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7445_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7446_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7447_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7448_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7449_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7450_: u8 = 0;
    let mut v_id_7451_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7453_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7454_: u8 = 0;
    let mut v___x_7455_: u8 = 0;
    let mut v___x_7456_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7457_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7458_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7460_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7461_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7462_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7463_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7464_: u8 = 0;
    let mut v_unused_7465_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7467_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7468_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7469_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7470_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7471_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7472_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7473_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_7474_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7475_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7476_: u8 = 0;
    let mut v___x_7477_: u8 = 0;
    let mut v___y_7479_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7480_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7481_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7482_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7483_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7484_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7485_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_7486_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7487_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_7488_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7489_: u8 = 0;
    let mut v___x_7490_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_7491_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7493_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7494_: u8 = 0;
    let mut v___x_7496_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7497_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7498_: u8 = 0;
    let mut v_a_7499_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7501_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7502_: u8 = 0;
    let mut v___x_7504_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7505_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7506_: u8 = 0;
    let mut v_a_7507_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7509_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7510_: u8 = 0;
    let mut v___x_7512_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7513_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7514_: u8 = 0;
    let mut v___y_7516_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7517_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7518_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7519_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7520_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7521_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7522_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7523_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7524_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7525_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_7526_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7528_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7529_: u8 = 0;
    let mut v___x_7531_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7532_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7533_: u8 = 0;
    let mut v___x_7534_: u8 = 0;
    let mut v___x_7535_: u8 = 0;
    let mut v___x_7536_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_7537_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7539_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7540_: u8 = 0;
    let mut v___x_7542_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7543_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7544_: u8 = 0;
    let mut v_a_7545_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7547_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7548_: u8 = 0;
    let mut v___x_7550_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7551_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7552_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ty_x3f_7411_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__1_spec__2___closed__3), core::ptr::addr_of_mut!(l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__1_spec__2___closed__3_once), _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__1_spec__2___closed__3);
                v___x_7412_ = 1;
                v___x_7413_ = lean_box(0);
                v___x_7414_ = lean_box((v___x_7412_) as usize);
                v___x_7415_ = lean_box((v___x_7412_) as usize);
                lean_inc(v_stx_7403_);
                v___x_7416_ = lean_alloc_closure(
                    l_Lean_Elab_Term_elabTermEnsuringType___boxed as *mut core::ffi::c_void,
                    12,
                    5,
                );
                lean_closure_set(v___x_7416_, 0, v_stx_7403_);
                lean_closure_set(v___x_7416_, 1, v_ty_x3f_7411_);
                lean_closure_set(v___x_7416_, 2, v___x_7414_);
                lean_closure_set(v___x_7416_, 3, v___x_7415_);
                lean_closure_set(v___x_7416_, 4, v___x_7413_);
                v_fileName_7417_ = lean_ctor_get(v_a_7408_, 0);
                v_fileMap_7418_ = lean_ctor_get(v_a_7408_, 1);
                v_options_7419_ = lean_ctor_get(v_a_7408_, 2);
                v_currRecDepth_7420_ = lean_ctor_get(v_a_7408_, 3);
                v_maxRecDepth_7421_ = lean_ctor_get(v_a_7408_, 4);
                v_ref_7422_ = lean_ctor_get(v_a_7408_, 5);
                v_currNamespace_7423_ = lean_ctor_get(v_a_7408_, 6);
                v_openDecls_7424_ = lean_ctor_get(v_a_7408_, 7);
                v_initHeartbeats_7425_ = lean_ctor_get(v_a_7408_, 8);
                v_maxHeartbeats_7426_ = lean_ctor_get(v_a_7408_, 9);
                v_quotContext_7427_ = lean_ctor_get(v_a_7408_, 10);
                v_currMacroScope_7428_ = lean_ctor_get(v_a_7408_, 11);
                v_diag_7429_ = lean_ctor_get_uint8(
                    v_a_7408_,
                    (core::mem::size_of::<*mut LeanObject>() * 14) as u32,
                );
                v_cancelTk_x3f_7430_ = lean_ctor_get(v_a_7408_, 12);
                v_suppressElabErrors_7431_ = lean_ctor_get_uint8(
                    v_a_7408_,
                    (core::mem::size_of::<*mut LeanObject>() * 14 + 1) as u32,
                );
                v_inheritedTraceOptions_7432_ = lean_ctor_get(v_a_7408_, 13);
                v___x_7433_ = 1;
                v_ref_7434_ = l_Lean_replaceRef(v_stx_7403_, v_ref_7422_);
                lean_dec(v_stx_7403_);
                lean_inc_ref(v_inheritedTraceOptions_7432_);
                lean_inc(v_cancelTk_x3f_7430_);
                lean_inc(v_currMacroScope_7428_);
                lean_inc(v_quotContext_7427_);
                lean_inc(v_maxHeartbeats_7426_);
                lean_inc(v_initHeartbeats_7425_);
                lean_inc(v_openDecls_7424_);
                lean_inc(v_currNamespace_7423_);
                lean_inc(v_maxRecDepth_7421_);
                lean_inc(v_currRecDepth_7420_);
                lean_inc_ref(v_options_7419_);
                lean_inc_ref(v_fileMap_7418_);
                lean_inc_ref(v_fileName_7417_);
                v___x_7435_ = lean_alloc_ctor(0, 14, (2) as u32);
                lean_ctor_set(v___x_7435_, 0, v_fileName_7417_);
                lean_ctor_set(v___x_7435_, 1, v_fileMap_7418_);
                lean_ctor_set(v___x_7435_, 2, v_options_7419_);
                lean_ctor_set(v___x_7435_, 3, v_currRecDepth_7420_);
                lean_ctor_set(v___x_7435_, 4, v_maxRecDepth_7421_);
                lean_ctor_set(v___x_7435_, 5, v_ref_7434_);
                lean_ctor_set(v___x_7435_, 6, v_currNamespace_7423_);
                lean_ctor_set(v___x_7435_, 7, v_openDecls_7424_);
                lean_ctor_set(v___x_7435_, 8, v_initHeartbeats_7425_);
                lean_ctor_set(v___x_7435_, 9, v_maxHeartbeats_7426_);
                lean_ctor_set(v___x_7435_, 10, v_quotContext_7427_);
                lean_ctor_set(v___x_7435_, 11, v_currMacroScope_7428_);
                lean_ctor_set(v___x_7435_, 12, v_cancelTk_x3f_7430_);
                lean_ctor_set(v___x_7435_, 13, v_inheritedTraceOptions_7432_);
                lean_ctor_set_uint8(
                    v___x_7435_,
                    (core::mem::size_of::<*mut LeanObject>() * 14) as u32,
                    v_diag_7429_,
                );
                lean_ctor_set_uint8(
                    v___x_7435_,
                    (core::mem::size_of::<*mut LeanObject>() * 14 + 1) as u32,
                    v_suppressElabErrors_7431_,
                );
                v___x_7436_ =
                    l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_withSynthesizeImp(
                        lean_box(0),
                        v___x_7416_,
                        v___x_7433_,
                        v_a_7404_,
                        v_a_7405_,
                        v_a_7406_,
                        v_a_7407_,
                        v___x_7435_,
                        v_a_7409_,
                    );
                if lean_obj_tag(v___x_7436_) == 0 {
                    v_a_7437_ = lean_ctor_get(v___x_7436_, 0);
                    lean_inc(v_a_7437_);
                    lean_dec_ref_known(v___x_7436_, 1);
                    v___x_7438_ = l_Lean_instantiateMVars___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3_spec__6___redArg(v_a_7437_, v_a_7407_);
                    v_a_7439_ = lean_ctor_get(v___x_7438_, 0);
                    lean_inc(v_a_7439_);
                    lean_dec_ref(v___x_7438_);
                    v___x_7534_ = l_Lean_Expr_hasSorry(v_a_7439_);
                    if v___x_7534_ == 0 {
                        v___y_7479_ = v_a_7404_;
                        v___y_7480_ = v_a_7405_;
                        v___y_7481_ = v_a_7406_;
                        v___y_7482_ = v_a_7407_;
                        v___y_7483_ = v___x_7435_;
                        v___y_7484_ = v_a_7409_;
                        state = 5;
                        continue;
                    } else {
                        v___x_7535_ = l_Lean_Expr_hasSyntheticSorry(v_a_7439_);
                        if v___x_7535_ == 0 {
                            v___y_7516_ = v_a_7404_;
                            v___y_7517_ = v_a_7405_;
                            v___y_7518_ = v_a_7406_;
                            v___y_7519_ = v_a_7407_;
                            v___y_7520_ = v___x_7435_;
                            v___y_7521_ = v_a_7409_;
                            state = 12;
                            continue;
                        } else {
                            lean_dec(v_a_7439_);
                            lean_dec_ref_known(v___x_7435_, 14);
                            v___x_7536_ = l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3_spec__8___redArg();
                            v_a_7537_ = lean_ctor_get(v___x_7536_, 0);
                            v_isSharedCheck_7544_ = (!lean_is_exclusive(v___x_7536_)) as u8;
                            if v_isSharedCheck_7544_ == 0 {
                                v___x_7539_ = v___x_7536_;
                                v_isShared_7540_ = v_isSharedCheck_7544_;
                                state = 15;
                                continue;
                            } else {
                                lean_inc(v_a_7537_);
                                lean_dec(v___x_7536_);
                                v___x_7539_ = lean_box(0);
                                v_isShared_7540_ = v_isSharedCheck_7544_;
                                state = 15;
                                continue;
                            }
                        }
                    }
                } else {
                    lean_dec_ref_known(v___x_7435_, 14);
                    v_a_7545_ = lean_ctor_get(v___x_7436_, 0);
                    v_isSharedCheck_7552_ = (!lean_is_exclusive(v___x_7436_)) as u8;
                    if v_isSharedCheck_7552_ == 0 {
                        v___x_7547_ = v___x_7436_;
                        v_isShared_7548_ = v_isSharedCheck_7552_;
                        state = 17;
                        continue;
                    } else {
                        lean_inc(v_a_7545_);
                        lean_dec(v___x_7436_);
                        v___x_7547_ = lean_box(0);
                        v_isShared_7548_ = v_isSharedCheck_7552_;
                        state = 17;
                        continue;
                    }
                }
            }
            1 => {
                if v___y_7450_ == 0 {
                    if lean_obj_tag(v___y_7448_) == 0 {
                        lean_dec_ref_known(v___y_7448_, 2);
                        lean_dec_ref(v___y_7447_);
                        lean_dec(v_a_7439_);
                        return v___y_7441_;
                    } else {
                        v_id_7451_ = lean_ctor_get(v___y_7448_, 0);
                        v_isSharedCheck_7464_ = (!lean_is_exclusive(v___y_7448_)) as u8;
                        if v_isSharedCheck_7464_ == 0 {
                            v_unused_7465_ = lean_ctor_get(v___y_7448_, 1);
                            lean_dec(v_unused_7465_);
                            v___x_7453_ = v___y_7448_;
                            v_isShared_7454_ = v_isSharedCheck_7464_;
                            state = 2;
                            continue;
                        } else {
                            lean_inc(v_id_7451_);
                            lean_dec(v___y_7448_);
                            v___x_7453_ = lean_box(0);
                            v_isShared_7454_ = v_isSharedCheck_7464_;
                            state = 2;
                            continue;
                        }
                    }
                } else {
                    lean_dec_ref(v___y_7448_);
                    lean_dec_ref(v___y_7447_);
                    lean_dec(v_a_7439_);
                    return v___y_7441_;
                }
            }
            2 => {
                v___x_7455_ = l_Lean_instBEqInternalExceptionId_beq(v___y_7444_, v_id_7451_);
                lean_dec(v_id_7451_);
                if v___x_7455_ == 0 {
                    lean_del_object(v___x_7453_);
                    lean_dec_ref(v___y_7447_);
                    lean_dec(v_a_7439_);
                    return v___y_7441_;
                } else {
                    lean_dec_ref(v___y_7441_);
                    v___x_7456_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__1_spec__2___closed__6), core::ptr::addr_of_mut!(l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__1_spec__2___closed__6_once), _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__1_spec__2___closed__6);
                    v___x_7457_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__2_spec__4___closed__10), core::ptr::addr_of_mut!(l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__2_spec__4___closed__10_once), _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__2_spec__4___closed__10);
                    v___x_7458_ = l_Lean_indentExpr(v_a_7439_);
                    if v_isShared_7454_ == 0 {
                        lean_ctor_set_tag(v___x_7453_, 7);
                        lean_ctor_set(v___x_7453_, 1, v___x_7458_);
                        lean_ctor_set(v___x_7453_, 0, v___x_7457_);
                        v___x_7460_ = v___x_7453_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_7463_ = lean_alloc_ctor(7, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_7463_, 0, v___x_7457_);
                        lean_ctor_set(v_reuseFailAlloc_7463_, 1, v___x_7458_);
                        v___x_7460_ = v_reuseFailAlloc_7463_;
                        state = 3;
                        continue;
                    }
                }
            }
            3 => {
                v___x_7461_ = lean_alloc_ctor(7, 2, (0) as u32);
                lean_ctor_set(v___x_7461_, 0, v___x_7460_);
                lean_ctor_set(v___x_7461_, 1, v___x_7456_);
                v___x_7462_ = l_Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3_spec__7___redArg(v___x_7461_, v___y_7443_, v___y_7442_, v___y_7446_, v___y_7445_, v___y_7447_, v___y_7449_);
                lean_dec_ref(v___y_7447_);
                return v___x_7462_;
            }
            4 => {
                lean_inc(v_a_7439_);
                v___x_7473_ = l_Lean_Elab_ConfigEval_instEvalExprOccurrences_evalExpr(
                    v_a_7439_,
                    v___y_7469_,
                    v___y_7470_,
                    v___y_7471_,
                    v___y_7472_,
                );
                if lean_obj_tag(v___x_7473_) == 0 {
                    lean_dec_ref(v___y_7471_);
                    lean_dec(v_a_7439_);
                    return v___x_7473_;
                } else {
                    v_a_7474_ = lean_ctor_get(v___x_7473_, 0);
                    lean_inc(v_a_7474_);
                    v___x_7475_ = l_Lean_Elab_unsupportedSyntaxExceptionId;
                    v___x_7476_ = l_Lean_Exception_isInterrupt(v_a_7474_);
                    if v___x_7476_ == 0 {
                        lean_inc(v_a_7474_);
                        v___x_7477_ = l_Lean_Exception_isRuntime(v_a_7474_);
                        v___y_7441_ = v___x_7473_;
                        v___y_7442_ = v___y_7468_;
                        v___y_7443_ = v___y_7467_;
                        v___y_7444_ = v___x_7475_;
                        v___y_7445_ = v___y_7470_;
                        v___y_7446_ = v___y_7469_;
                        v___y_7447_ = v___y_7471_;
                        v___y_7448_ = v_a_7474_;
                        v___y_7449_ = v___y_7472_;
                        v___y_7450_ = v___x_7477_;
                        state = 1;
                        continue;
                    } else {
                        v___y_7441_ = v___x_7473_;
                        v___y_7442_ = v___y_7468_;
                        v___y_7443_ = v___y_7467_;
                        v___y_7444_ = v___x_7475_;
                        v___y_7445_ = v___y_7470_;
                        v___y_7446_ = v___y_7469_;
                        v___y_7447_ = v___y_7471_;
                        v___y_7448_ = v_a_7474_;
                        v___y_7449_ = v___y_7472_;
                        v___y_7450_ = v___x_7476_;
                        state = 1;
                        continue;
                    }
                }
            }
            5 => {
                lean_inc(v_a_7439_);
                v___x_7485_ = l_Lean_Meta_getMVars(
                    v_a_7439_,
                    v___y_7481_,
                    v___y_7482_,
                    v___y_7483_,
                    v___y_7484_,
                );
                if lean_obj_tag(v___x_7485_) == 0 {
                    v_a_7486_ = lean_ctor_get(v___x_7485_, 0);
                    lean_inc(v_a_7486_);
                    lean_dec_ref_known(v___x_7485_, 1);
                    v___x_7487_ = l_Lean_Elab_Term_logUnassignedUsingErrorInfos(
                        v_a_7486_,
                        v___x_7413_,
                        v___y_7479_,
                        v___y_7480_,
                        v___y_7481_,
                        v___y_7482_,
                        v___y_7483_,
                        v___y_7484_,
                    );
                    lean_dec(v_a_7486_);
                    if lean_obj_tag(v___x_7487_) == 0 {
                        v_a_7488_ = lean_ctor_get(v___x_7487_, 0);
                        lean_inc(v_a_7488_);
                        lean_dec_ref_known(v___x_7487_, 1);
                        v___x_7489_ = (lean_unbox(v_a_7488_) as u8);
                        lean_dec(v_a_7488_);
                        if v___x_7489_ == 0 {
                            v___y_7467_ = v___y_7479_;
                            v___y_7468_ = v___y_7480_;
                            v___y_7469_ = v___y_7481_;
                            v___y_7470_ = v___y_7482_;
                            v___y_7471_ = v___y_7483_;
                            v___y_7472_ = v___y_7484_;
                            state = 4;
                            continue;
                        } else {
                            lean_dec_ref(v___y_7483_);
                            lean_dec(v_a_7439_);
                            v___x_7490_ = l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3_spec__8___redArg();
                            v_a_7491_ = lean_ctor_get(v___x_7490_, 0);
                            v_isSharedCheck_7498_ = (!lean_is_exclusive(v___x_7490_)) as u8;
                            if v_isSharedCheck_7498_ == 0 {
                                v___x_7493_ = v___x_7490_;
                                v_isShared_7494_ = v_isSharedCheck_7498_;
                                state = 6;
                                continue;
                            } else {
                                lean_inc(v_a_7491_);
                                lean_dec(v___x_7490_);
                                v___x_7493_ = lean_box(0);
                                v_isShared_7494_ = v_isSharedCheck_7498_;
                                state = 6;
                                continue;
                            }
                        }
                    } else {
                        lean_dec_ref(v___y_7483_);
                        lean_dec(v_a_7439_);
                        v_a_7499_ = lean_ctor_get(v___x_7487_, 0);
                        v_isSharedCheck_7506_ = (!lean_is_exclusive(v___x_7487_)) as u8;
                        if v_isSharedCheck_7506_ == 0 {
                            v___x_7501_ = v___x_7487_;
                            v_isShared_7502_ = v_isSharedCheck_7506_;
                            state = 8;
                            continue;
                        } else {
                            lean_inc(v_a_7499_);
                            lean_dec(v___x_7487_);
                            v___x_7501_ = lean_box(0);
                            v_isShared_7502_ = v_isSharedCheck_7506_;
                            state = 8;
                            continue;
                        }
                    }
                } else {
                    lean_dec_ref(v___y_7483_);
                    lean_dec(v_a_7439_);
                    v_a_7507_ = lean_ctor_get(v___x_7485_, 0);
                    v_isSharedCheck_7514_ = (!lean_is_exclusive(v___x_7485_)) as u8;
                    if v_isSharedCheck_7514_ == 0 {
                        v___x_7509_ = v___x_7485_;
                        v_isShared_7510_ = v_isSharedCheck_7514_;
                        state = 10;
                        continue;
                    } else {
                        lean_inc(v_a_7507_);
                        lean_dec(v___x_7485_);
                        v___x_7509_ = lean_box(0);
                        v_isShared_7510_ = v_isSharedCheck_7514_;
                        state = 10;
                        continue;
                    }
                }
            }
            6 => {
                if v_isShared_7494_ == 0 {
                    v___x_7496_ = v___x_7493_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_7497_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_7497_, 0, v_a_7491_);
                    v___x_7496_ = v_reuseFailAlloc_7497_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_7496_;
            }
            8 => {
                if v_isShared_7502_ == 0 {
                    v___x_7504_ = v___x_7501_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_7505_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_7505_, 0, v_a_7499_);
                    v___x_7504_ = v_reuseFailAlloc_7505_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_7504_;
            }
            10 => {
                if v_isShared_7510_ == 0 {
                    v___x_7512_ = v___x_7509_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_7513_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_7513_, 0, v_a_7507_);
                    v___x_7512_ = v_reuseFailAlloc_7513_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                return v___x_7512_;
            }
            12 => {
                v___x_7522_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__2_spec__4___closed__12), core::ptr::addr_of_mut!(l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__2_spec__4___closed__12_once), _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__2_spec__4___closed__12);
                v___x_7523_ = l_Lean_indentExpr(v_a_7439_);
                v___x_7524_ = lean_alloc_ctor(7, 2, (0) as u32);
                lean_ctor_set(v___x_7524_, 0, v___x_7522_);
                lean_ctor_set(v___x_7524_, 1, v___x_7523_);
                v___x_7525_ = l_Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3_spec__7___redArg(v___x_7524_, v___y_7516_, v___y_7517_, v___y_7518_, v___y_7519_, v___y_7520_, v___y_7521_);
                lean_dec_ref(v___y_7520_);
                v_a_7526_ = lean_ctor_get(v___x_7525_, 0);
                v_isSharedCheck_7533_ = (!lean_is_exclusive(v___x_7525_)) as u8;
                if v_isSharedCheck_7533_ == 0 {
                    v___x_7528_ = v___x_7525_;
                    v_isShared_7529_ = v_isSharedCheck_7533_;
                    state = 13;
                    continue;
                } else {
                    lean_inc(v_a_7526_);
                    lean_dec(v___x_7525_);
                    v___x_7528_ = lean_box(0);
                    v_isShared_7529_ = v_isSharedCheck_7533_;
                    state = 13;
                    continue;
                }
            }
            13 => {
                if v_isShared_7529_ == 0 {
                    v___x_7531_ = v___x_7528_;
                    state = 14;
                    continue;
                } else {
                    v_reuseFailAlloc_7532_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_7532_, 0, v_a_7526_);
                    v___x_7531_ = v_reuseFailAlloc_7532_;
                    state = 14;
                    continue;
                }
            }
            14 => {
                return v___x_7531_;
            }
            15 => {
                if v_isShared_7540_ == 0 {
                    v___x_7542_ = v___x_7539_;
                    state = 16;
                    continue;
                } else {
                    v_reuseFailAlloc_7543_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_7543_, 0, v_a_7537_);
                    v___x_7542_ = v_reuseFailAlloc_7543_;
                    state = 16;
                    continue;
                }
            }
            16 => {
                return v___x_7542_;
            }
            17 => {
                if v_isShared_7548_ == 0 {
                    v___x_7550_ = v___x_7547_;
                    state = 18;
                    continue;
                } else {
                    v_reuseFailAlloc_7551_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_7551_, 0, v_a_7545_);
                    v___x_7550_ = v_reuseFailAlloc_7551_;
                    state = 18;
                    continue;
                }
            }
            18 => {
                return v___x_7550_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__1_spec__2___boxed(
    mut v_stx_7553_: *mut LeanObject,
    mut v_a_7554_: *mut LeanObject,
    mut v_a_7555_: *mut LeanObject,
    mut v_a_7556_: *mut LeanObject,
    mut v_a_7557_: *mut LeanObject,
    mut v_a_7558_: *mut LeanObject,
    mut v_a_7559_: *mut LeanObject,
    mut v_a_7560_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_7561_: *mut LeanObject = core::ptr::null_mut();
    v_res_7561_ = l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__1_spec__2(v_stx_7553_, v_a_7554_, v_a_7555_, v_a_7556_, v_a_7557_, v_a_7558_, v_a_7559_);
    lean_dec(v_a_7559_);
    lean_dec_ref(v_a_7558_);
    lean_dec(v_a_7557_);
    lean_dec_ref(v_a_7556_);
    lean_dec(v_a_7555_);
    lean_dec_ref(v_a_7554_);
    return v_res_7561_;
}
pub unsafe fn l_Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__1(
    mut v_stx_7562_: *mut LeanObject,
    mut v_a_7563_: *mut LeanObject,
    mut v_a_7564_: *mut LeanObject,
    mut v_a_7565_: *mut LeanObject,
    mut v_a_7566_: *mut LeanObject,
    mut v_a_7567_: *mut LeanObject,
    mut v_a_7568_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_fileName_7570_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fileMap_7571_: *mut LeanObject = core::ptr::null_mut();
    let mut v_options_7572_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currRecDepth_7573_: *mut LeanObject = core::ptr::null_mut();
    let mut v_maxRecDepth_7574_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ref_7575_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currNamespace_7576_: *mut LeanObject = core::ptr::null_mut();
    let mut v_openDecls_7577_: *mut LeanObject = core::ptr::null_mut();
    let mut v_initHeartbeats_7578_: *mut LeanObject = core::ptr::null_mut();
    let mut v_maxHeartbeats_7579_: *mut LeanObject = core::ptr::null_mut();
    let mut v_quotContext_7580_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currMacroScope_7581_: *mut LeanObject = core::ptr::null_mut();
    let mut v_diag_7582_: u8 = 0;
    let mut v_cancelTk_x3f_7583_: *mut LeanObject = core::ptr::null_mut();
    let mut v_suppressElabErrors_7584_: u8 = 0;
    let mut v_inheritedTraceOptions_7585_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ref_7586_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7587_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7588_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_7589_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7591_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7592_: u8 = 0;
    let mut v_fst_7593_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7595_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7596_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7597_: u8 = 0;
    let mut v_a_7598_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7600_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7601_: u8 = 0;
    let mut v___x_7602_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7604_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7606_: u8 = 0;
    let mut v_id_7607_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7608_: u8 = 0;
    let mut v___x_7609_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7610_: u8 = 0;
    let mut v___x_7611_: u8 = 0;
    let mut v_reuseFailAlloc_7612_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7613_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_fileName_7570_ = lean_ctor_get(v_a_7567_, 0);
                v_fileMap_7571_ = lean_ctor_get(v_a_7567_, 1);
                v_options_7572_ = lean_ctor_get(v_a_7567_, 2);
                v_currRecDepth_7573_ = lean_ctor_get(v_a_7567_, 3);
                v_maxRecDepth_7574_ = lean_ctor_get(v_a_7567_, 4);
                v_ref_7575_ = lean_ctor_get(v_a_7567_, 5);
                v_currNamespace_7576_ = lean_ctor_get(v_a_7567_, 6);
                v_openDecls_7577_ = lean_ctor_get(v_a_7567_, 7);
                v_initHeartbeats_7578_ = lean_ctor_get(v_a_7567_, 8);
                v_maxHeartbeats_7579_ = lean_ctor_get(v_a_7567_, 9);
                v_quotContext_7580_ = lean_ctor_get(v_a_7567_, 10);
                v_currMacroScope_7581_ = lean_ctor_get(v_a_7567_, 11);
                v_diag_7582_ = lean_ctor_get_uint8(
                    v_a_7567_,
                    (core::mem::size_of::<*mut LeanObject>() * 14) as u32,
                );
                v_cancelTk_x3f_7583_ = lean_ctor_get(v_a_7567_, 12);
                v_suppressElabErrors_7584_ = lean_ctor_get_uint8(
                    v_a_7567_,
                    (core::mem::size_of::<*mut LeanObject>() * 14 + 1) as u32,
                );
                v_inheritedTraceOptions_7585_ = lean_ctor_get(v_a_7567_, 13);
                v_ref_7586_ = l_Lean_replaceRef(v_stx_7562_, v_ref_7575_);
                lean_inc_ref(v_inheritedTraceOptions_7585_);
                lean_inc(v_cancelTk_x3f_7583_);
                lean_inc(v_currMacroScope_7581_);
                lean_inc(v_quotContext_7580_);
                lean_inc(v_maxHeartbeats_7579_);
                lean_inc(v_initHeartbeats_7578_);
                lean_inc(v_openDecls_7577_);
                lean_inc(v_currNamespace_7576_);
                lean_inc(v_maxRecDepth_7574_);
                lean_inc(v_currRecDepth_7573_);
                lean_inc_ref(v_options_7572_);
                lean_inc_ref(v_fileMap_7571_);
                lean_inc_ref(v_fileName_7570_);
                v___x_7587_ = lean_alloc_ctor(0, 14, (2) as u32);
                lean_ctor_set(v___x_7587_, 0, v_fileName_7570_);
                lean_ctor_set(v___x_7587_, 1, v_fileMap_7571_);
                lean_ctor_set(v___x_7587_, 2, v_options_7572_);
                lean_ctor_set(v___x_7587_, 3, v_currRecDepth_7573_);
                lean_ctor_set(v___x_7587_, 4, v_maxRecDepth_7574_);
                lean_ctor_set(v___x_7587_, 5, v_ref_7586_);
                lean_ctor_set(v___x_7587_, 6, v_currNamespace_7576_);
                lean_ctor_set(v___x_7587_, 7, v_openDecls_7577_);
                lean_ctor_set(v___x_7587_, 8, v_initHeartbeats_7578_);
                lean_ctor_set(v___x_7587_, 9, v_maxHeartbeats_7579_);
                lean_ctor_set(v___x_7587_, 10, v_quotContext_7580_);
                lean_ctor_set(v___x_7587_, 11, v_currMacroScope_7581_);
                lean_ctor_set(v___x_7587_, 12, v_cancelTk_x3f_7583_);
                lean_ctor_set(v___x_7587_, 13, v_inheritedTraceOptions_7585_);
                lean_ctor_set_uint8(
                    v___x_7587_,
                    (core::mem::size_of::<*mut LeanObject>() * 14) as u32,
                    v_diag_7582_,
                );
                lean_ctor_set_uint8(
                    v___x_7587_,
                    (core::mem::size_of::<*mut LeanObject>() * 14 + 1) as u32,
                    v_suppressElabErrors_7584_,
                );
                lean_inc(v_stx_7562_);
                v___x_7588_ = l_Lean_Elab_ConfigEval_instEvalTermOccurrences_evalTerm(
                    v_stx_7562_,
                    v_a_7563_,
                    v_a_7564_,
                    v_a_7565_,
                    v_a_7566_,
                    v___x_7587_,
                    v_a_7568_,
                );
                if lean_obj_tag(v___x_7588_) == 0 {
                    lean_dec_ref_known(v___x_7587_, 14);
                    lean_dec(v_stx_7562_);
                    v_a_7589_ = lean_ctor_get(v___x_7588_, 0);
                    v_isSharedCheck_7597_ = (!lean_is_exclusive(v___x_7588_)) as u8;
                    if v_isSharedCheck_7597_ == 0 {
                        v___x_7591_ = v___x_7588_;
                        v_isShared_7592_ = v_isSharedCheck_7597_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_7589_);
                        lean_dec(v___x_7588_);
                        v___x_7591_ = lean_box(0);
                        v_isShared_7592_ = v_isSharedCheck_7597_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_7598_ = lean_ctor_get(v___x_7588_, 0);
                    v_isSharedCheck_7613_ = (!lean_is_exclusive(v___x_7588_)) as u8;
                    if v_isSharedCheck_7613_ == 0 {
                        v___x_7600_ = v___x_7588_;
                        v_isShared_7601_ = v_isSharedCheck_7613_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_7598_);
                        lean_dec(v___x_7588_);
                        v___x_7600_ = lean_box(0);
                        v_isShared_7601_ = v_isSharedCheck_7613_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v_fst_7593_ = lean_ctor_get(v_a_7589_, 0);
                lean_inc(v_fst_7593_);
                lean_dec(v_a_7589_);
                if v_isShared_7592_ == 0 {
                    lean_ctor_set(v___x_7591_, 0, v_fst_7593_);
                    v___x_7595_ = v___x_7591_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_7596_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_7596_, 0, v_fst_7593_);
                    v___x_7595_ = v_reuseFailAlloc_7596_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_7595_;
            }
            3 => {
                v___x_7602_ = l_Lean_Elab_unsupportedSyntaxExceptionId;
                lean_inc(v_a_7598_);
                if v_isShared_7601_ == 0 {
                    v___x_7604_ = v___x_7600_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_7612_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_7612_, 0, v_a_7598_);
                    v___x_7604_ = v_reuseFailAlloc_7612_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_7610_ = l_Lean_Exception_isInterrupt(v_a_7598_);
                if v___x_7610_ == 0 {
                    lean_inc(v_a_7598_);
                    v___x_7611_ = l_Lean_Exception_isRuntime(v_a_7598_);
                    v___y_7606_ = v___x_7611_;
                    state = 5;
                    continue;
                } else {
                    v___y_7606_ = v___x_7610_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                if v___y_7606_ == 0 {
                    if lean_obj_tag(v_a_7598_) == 0 {
                        lean_dec_ref_known(v_a_7598_, 2);
                        lean_dec_ref_known(v___x_7587_, 14);
                        lean_dec(v_stx_7562_);
                        return v___x_7604_;
                    } else {
                        v_id_7607_ = lean_ctor_get(v_a_7598_, 0);
                        lean_inc(v_id_7607_);
                        lean_dec_ref_known(v_a_7598_, 2);
                        v___x_7608_ =
                            l_Lean_instBEqInternalExceptionId_beq(v___x_7602_, v_id_7607_);
                        lean_dec(v_id_7607_);
                        if v___x_7608_ == 0 {
                            lean_dec_ref_known(v___x_7587_, 14);
                            lean_dec(v_stx_7562_);
                            return v___x_7604_;
                        } else {
                            lean_dec_ref(v___x_7604_);
                            v___x_7609_ = l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__1_spec__2(v_stx_7562_, v_a_7563_, v_a_7564_, v_a_7565_, v_a_7566_, v___x_7587_, v_a_7568_);
                            lean_dec_ref_known(v___x_7587_, 14);
                            return v___x_7609_;
                        }
                    }
                } else {
                    lean_dec(v_a_7598_);
                    lean_dec_ref_known(v___x_7587_, 14);
                    lean_dec(v_stx_7562_);
                    return v___x_7604_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__1___boxed(
    mut v_stx_7614_: *mut LeanObject,
    mut v_a_7615_: *mut LeanObject,
    mut v_a_7616_: *mut LeanObject,
    mut v_a_7617_: *mut LeanObject,
    mut v_a_7618_: *mut LeanObject,
    mut v_a_7619_: *mut LeanObject,
    mut v_a_7620_: *mut LeanObject,
    mut v_a_7621_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_7622_: *mut LeanObject = core::ptr::null_mut();
    v_res_7622_ = l_Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__1(v_stx_7614_, v_a_7615_, v_a_7616_, v_a_7617_, v_a_7618_, v_a_7619_, v_a_7620_);
    lean_dec(v_a_7620_);
    lean_dec_ref(v_a_7619_);
    lean_dec(v_a_7618_);
    lean_dec_ref(v_a_7617_);
    lean_dec(v_a_7616_);
    lean_dec_ref(v_a_7615_);
    return v_res_7622_;
}
pub unsafe fn _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3___closed__0()
-> *mut LeanObject {
    let mut v___x_7623_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7624_: *mut LeanObject = core::ptr::null_mut();
    v___x_7623_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_instEvalExprConfig___closed__1), core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_instEvalExprConfig___closed__1_once), _init_l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_instEvalExprConfig___closed__1);
    v___x_7624_ = l_Lean_MessageData_ofExpr(v___x_7623_);
    return v___x_7624_;
}
pub unsafe fn _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3___closed__1()
-> *mut LeanObject {
    let mut v___x_7625_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7626_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7627_: *mut LeanObject = core::ptr::null_mut();
    v___x_7625_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3___closed__0), core::ptr::addr_of_mut!(l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3___closed__0_once), _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3___closed__0);
    v___x_7626_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__2_spec__4___closed__5), core::ptr::addr_of_mut!(l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__2_spec__4___closed__5_once), _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__2_spec__4___closed__5);
    v___x_7627_ = lean_alloc_ctor(7, 2, (0) as u32);
    lean_ctor_set(v___x_7627_, 0, v___x_7626_);
    lean_ctor_set(v___x_7627_, 1, v___x_7625_);
    return v___x_7627_;
}
pub unsafe fn _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3___closed__2()
-> *mut LeanObject {
    let mut v___x_7628_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7629_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7630_: *mut LeanObject = core::ptr::null_mut();
    v___x_7628_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_withRWRulesSeq_go___closed__3), core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_withRWRulesSeq_go___closed__3_once), _init_l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_withRWRulesSeq_go___closed__3);
    v___x_7629_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3___closed__1), core::ptr::addr_of_mut!(l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3___closed__1_once), _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3___closed__1);
    v___x_7630_ = lean_alloc_ctor(7, 2, (0) as u32);
    lean_ctor_set(v___x_7630_, 0, v___x_7629_);
    lean_ctor_set(v___x_7630_, 1, v___x_7628_);
    return v___x_7630_;
}
pub unsafe fn l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3(
    mut v_stx_7631_: *mut LeanObject,
    mut v_a_7632_: *mut LeanObject,
    mut v_a_7633_: *mut LeanObject,
    mut v_a_7634_: *mut LeanObject,
    mut v_a_7635_: *mut LeanObject,
    mut v_a_7636_: *mut LeanObject,
    mut v_a_7637_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_ty_x3f_7639_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7640_: u8 = 0;
    let mut v___x_7641_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7642_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7643_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7644_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fileName_7645_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fileMap_7646_: *mut LeanObject = core::ptr::null_mut();
    let mut v_options_7647_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currRecDepth_7648_: *mut LeanObject = core::ptr::null_mut();
    let mut v_maxRecDepth_7649_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ref_7650_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currNamespace_7651_: *mut LeanObject = core::ptr::null_mut();
    let mut v_openDecls_7652_: *mut LeanObject = core::ptr::null_mut();
    let mut v_initHeartbeats_7653_: *mut LeanObject = core::ptr::null_mut();
    let mut v_maxHeartbeats_7654_: *mut LeanObject = core::ptr::null_mut();
    let mut v_quotContext_7655_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currMacroScope_7656_: *mut LeanObject = core::ptr::null_mut();
    let mut v_diag_7657_: u8 = 0;
    let mut v_cancelTk_x3f_7658_: *mut LeanObject = core::ptr::null_mut();
    let mut v_suppressElabErrors_7659_: u8 = 0;
    let mut v_inheritedTraceOptions_7660_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7661_: u8 = 0;
    let mut v_ref_7662_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7663_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7664_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_7665_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7666_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_7667_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7669_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7670_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7671_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7672_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7673_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7674_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7675_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7676_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7677_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7678_: u8 = 0;
    let mut v_id_7679_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7681_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7682_: u8 = 0;
    let mut v___x_7683_: u8 = 0;
    let mut v___x_7684_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7685_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7686_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7688_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7689_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7690_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7691_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7692_: u8 = 0;
    let mut v_unused_7693_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7695_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7696_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7697_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7698_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7699_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7700_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7701_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_7702_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7703_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7704_: u8 = 0;
    let mut v___x_7705_: u8 = 0;
    let mut v___y_7707_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7708_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7709_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7710_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7711_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7712_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7713_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_7714_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7715_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_7716_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7717_: u8 = 0;
    let mut v___x_7718_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_7719_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7721_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7722_: u8 = 0;
    let mut v___x_7724_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7725_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7726_: u8 = 0;
    let mut v_a_7727_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7729_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7730_: u8 = 0;
    let mut v___x_7732_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7733_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7734_: u8 = 0;
    let mut v_a_7735_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7737_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7738_: u8 = 0;
    let mut v___x_7740_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7741_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7742_: u8 = 0;
    let mut v___y_7744_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7745_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7746_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7747_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7748_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7749_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7750_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7751_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7752_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7753_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_7754_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7756_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7757_: u8 = 0;
    let mut v___x_7759_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7760_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7761_: u8 = 0;
    let mut v___x_7762_: u8 = 0;
    let mut v___x_7763_: u8 = 0;
    let mut v___x_7764_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_7765_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7767_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7768_: u8 = 0;
    let mut v___x_7770_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7771_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7772_: u8 = 0;
    let mut v_a_7773_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7775_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7776_: u8 = 0;
    let mut v___x_7778_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7779_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7780_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ty_x3f_7639_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_instEvalExprConfig___closed__2), core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_instEvalExprConfig___closed__2_once), _init_l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_instEvalExprConfig___closed__2);
                v___x_7640_ = 1;
                v___x_7641_ = lean_box(0);
                v___x_7642_ = lean_box((v___x_7640_) as usize);
                v___x_7643_ = lean_box((v___x_7640_) as usize);
                lean_inc(v_stx_7631_);
                v___x_7644_ = lean_alloc_closure(
                    l_Lean_Elab_Term_elabTermEnsuringType___boxed as *mut core::ffi::c_void,
                    12,
                    5,
                );
                lean_closure_set(v___x_7644_, 0, v_stx_7631_);
                lean_closure_set(v___x_7644_, 1, v_ty_x3f_7639_);
                lean_closure_set(v___x_7644_, 2, v___x_7642_);
                lean_closure_set(v___x_7644_, 3, v___x_7643_);
                lean_closure_set(v___x_7644_, 4, v___x_7641_);
                v_fileName_7645_ = lean_ctor_get(v_a_7636_, 0);
                v_fileMap_7646_ = lean_ctor_get(v_a_7636_, 1);
                v_options_7647_ = lean_ctor_get(v_a_7636_, 2);
                v_currRecDepth_7648_ = lean_ctor_get(v_a_7636_, 3);
                v_maxRecDepth_7649_ = lean_ctor_get(v_a_7636_, 4);
                v_ref_7650_ = lean_ctor_get(v_a_7636_, 5);
                v_currNamespace_7651_ = lean_ctor_get(v_a_7636_, 6);
                v_openDecls_7652_ = lean_ctor_get(v_a_7636_, 7);
                v_initHeartbeats_7653_ = lean_ctor_get(v_a_7636_, 8);
                v_maxHeartbeats_7654_ = lean_ctor_get(v_a_7636_, 9);
                v_quotContext_7655_ = lean_ctor_get(v_a_7636_, 10);
                v_currMacroScope_7656_ = lean_ctor_get(v_a_7636_, 11);
                v_diag_7657_ = lean_ctor_get_uint8(
                    v_a_7636_,
                    (core::mem::size_of::<*mut LeanObject>() * 14) as u32,
                );
                v_cancelTk_x3f_7658_ = lean_ctor_get(v_a_7636_, 12);
                v_suppressElabErrors_7659_ = lean_ctor_get_uint8(
                    v_a_7636_,
                    (core::mem::size_of::<*mut LeanObject>() * 14 + 1) as u32,
                );
                v_inheritedTraceOptions_7660_ = lean_ctor_get(v_a_7636_, 13);
                v___x_7661_ = 1;
                v_ref_7662_ = l_Lean_replaceRef(v_stx_7631_, v_ref_7650_);
                lean_dec(v_stx_7631_);
                lean_inc_ref(v_inheritedTraceOptions_7660_);
                lean_inc(v_cancelTk_x3f_7658_);
                lean_inc(v_currMacroScope_7656_);
                lean_inc(v_quotContext_7655_);
                lean_inc(v_maxHeartbeats_7654_);
                lean_inc(v_initHeartbeats_7653_);
                lean_inc(v_openDecls_7652_);
                lean_inc(v_currNamespace_7651_);
                lean_inc(v_maxRecDepth_7649_);
                lean_inc(v_currRecDepth_7648_);
                lean_inc_ref(v_options_7647_);
                lean_inc_ref(v_fileMap_7646_);
                lean_inc_ref(v_fileName_7645_);
                v___x_7663_ = lean_alloc_ctor(0, 14, (2) as u32);
                lean_ctor_set(v___x_7663_, 0, v_fileName_7645_);
                lean_ctor_set(v___x_7663_, 1, v_fileMap_7646_);
                lean_ctor_set(v___x_7663_, 2, v_options_7647_);
                lean_ctor_set(v___x_7663_, 3, v_currRecDepth_7648_);
                lean_ctor_set(v___x_7663_, 4, v_maxRecDepth_7649_);
                lean_ctor_set(v___x_7663_, 5, v_ref_7662_);
                lean_ctor_set(v___x_7663_, 6, v_currNamespace_7651_);
                lean_ctor_set(v___x_7663_, 7, v_openDecls_7652_);
                lean_ctor_set(v___x_7663_, 8, v_initHeartbeats_7653_);
                lean_ctor_set(v___x_7663_, 9, v_maxHeartbeats_7654_);
                lean_ctor_set(v___x_7663_, 10, v_quotContext_7655_);
                lean_ctor_set(v___x_7663_, 11, v_currMacroScope_7656_);
                lean_ctor_set(v___x_7663_, 12, v_cancelTk_x3f_7658_);
                lean_ctor_set(v___x_7663_, 13, v_inheritedTraceOptions_7660_);
                lean_ctor_set_uint8(
                    v___x_7663_,
                    (core::mem::size_of::<*mut LeanObject>() * 14) as u32,
                    v_diag_7657_,
                );
                lean_ctor_set_uint8(
                    v___x_7663_,
                    (core::mem::size_of::<*mut LeanObject>() * 14 + 1) as u32,
                    v_suppressElabErrors_7659_,
                );
                v___x_7664_ =
                    l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_withSynthesizeImp(
                        lean_box(0),
                        v___x_7644_,
                        v___x_7661_,
                        v_a_7632_,
                        v_a_7633_,
                        v_a_7634_,
                        v_a_7635_,
                        v___x_7663_,
                        v_a_7637_,
                    );
                if lean_obj_tag(v___x_7664_) == 0 {
                    v_a_7665_ = lean_ctor_get(v___x_7664_, 0);
                    lean_inc(v_a_7665_);
                    lean_dec_ref_known(v___x_7664_, 1);
                    v___x_7666_ = l_Lean_instantiateMVars___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3_spec__6___redArg(v_a_7665_, v_a_7635_);
                    v_a_7667_ = lean_ctor_get(v___x_7666_, 0);
                    lean_inc(v_a_7667_);
                    lean_dec_ref(v___x_7666_);
                    v___x_7762_ = l_Lean_Expr_hasSorry(v_a_7667_);
                    if v___x_7762_ == 0 {
                        v___y_7707_ = v_a_7632_;
                        v___y_7708_ = v_a_7633_;
                        v___y_7709_ = v_a_7634_;
                        v___y_7710_ = v_a_7635_;
                        v___y_7711_ = v___x_7663_;
                        v___y_7712_ = v_a_7637_;
                        state = 5;
                        continue;
                    } else {
                        v___x_7763_ = l_Lean_Expr_hasSyntheticSorry(v_a_7667_);
                        if v___x_7763_ == 0 {
                            v___y_7744_ = v_a_7632_;
                            v___y_7745_ = v_a_7633_;
                            v___y_7746_ = v_a_7634_;
                            v___y_7747_ = v_a_7635_;
                            v___y_7748_ = v___x_7663_;
                            v___y_7749_ = v_a_7637_;
                            state = 12;
                            continue;
                        } else {
                            lean_dec(v_a_7667_);
                            lean_dec_ref_known(v___x_7663_, 14);
                            v___x_7764_ = l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3_spec__8___redArg();
                            v_a_7765_ = lean_ctor_get(v___x_7764_, 0);
                            v_isSharedCheck_7772_ = (!lean_is_exclusive(v___x_7764_)) as u8;
                            if v_isSharedCheck_7772_ == 0 {
                                v___x_7767_ = v___x_7764_;
                                v_isShared_7768_ = v_isSharedCheck_7772_;
                                state = 15;
                                continue;
                            } else {
                                lean_inc(v_a_7765_);
                                lean_dec(v___x_7764_);
                                v___x_7767_ = lean_box(0);
                                v_isShared_7768_ = v_isSharedCheck_7772_;
                                state = 15;
                                continue;
                            }
                        }
                    }
                } else {
                    lean_dec_ref_known(v___x_7663_, 14);
                    v_a_7773_ = lean_ctor_get(v___x_7664_, 0);
                    v_isSharedCheck_7780_ = (!lean_is_exclusive(v___x_7664_)) as u8;
                    if v_isSharedCheck_7780_ == 0 {
                        v___x_7775_ = v___x_7664_;
                        v_isShared_7776_ = v_isSharedCheck_7780_;
                        state = 17;
                        continue;
                    } else {
                        lean_inc(v_a_7773_);
                        lean_dec(v___x_7664_);
                        v___x_7775_ = lean_box(0);
                        v_isShared_7776_ = v_isSharedCheck_7780_;
                        state = 17;
                        continue;
                    }
                }
            }
            1 => {
                if v___y_7678_ == 0 {
                    if lean_obj_tag(v___y_7672_) == 0 {
                        lean_dec_ref_known(v___y_7672_, 2);
                        lean_dec_ref(v___y_7677_);
                        lean_dec(v_a_7667_);
                        return v___y_7671_;
                    } else {
                        v_id_7679_ = lean_ctor_get(v___y_7672_, 0);
                        v_isSharedCheck_7692_ = (!lean_is_exclusive(v___y_7672_)) as u8;
                        if v_isSharedCheck_7692_ == 0 {
                            v_unused_7693_ = lean_ctor_get(v___y_7672_, 1);
                            lean_dec(v_unused_7693_);
                            v___x_7681_ = v___y_7672_;
                            v_isShared_7682_ = v_isSharedCheck_7692_;
                            state = 2;
                            continue;
                        } else {
                            lean_inc(v_id_7679_);
                            lean_dec(v___y_7672_);
                            v___x_7681_ = lean_box(0);
                            v_isShared_7682_ = v_isSharedCheck_7692_;
                            state = 2;
                            continue;
                        }
                    }
                } else {
                    lean_dec_ref(v___y_7677_);
                    lean_dec_ref(v___y_7672_);
                    lean_dec(v_a_7667_);
                    return v___y_7671_;
                }
            }
            2 => {
                v___x_7683_ = l_Lean_instBEqInternalExceptionId_beq(v___y_7670_, v_id_7679_);
                lean_dec(v_id_7679_);
                if v___x_7683_ == 0 {
                    lean_del_object(v___x_7681_);
                    lean_dec_ref(v___y_7677_);
                    lean_dec(v_a_7667_);
                    return v___y_7671_;
                } else {
                    lean_dec_ref(v___y_7671_);
                    v___x_7684_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3___closed__2), core::ptr::addr_of_mut!(l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3___closed__2_once), _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3___closed__2);
                    v___x_7685_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__2_spec__4___closed__10), core::ptr::addr_of_mut!(l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__2_spec__4___closed__10_once), _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__2_spec__4___closed__10);
                    v___x_7686_ = l_Lean_indentExpr(v_a_7667_);
                    if v_isShared_7682_ == 0 {
                        lean_ctor_set_tag(v___x_7681_, 7);
                        lean_ctor_set(v___x_7681_, 1, v___x_7686_);
                        lean_ctor_set(v___x_7681_, 0, v___x_7685_);
                        v___x_7688_ = v___x_7681_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_7691_ = lean_alloc_ctor(7, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_7691_, 0, v___x_7685_);
                        lean_ctor_set(v_reuseFailAlloc_7691_, 1, v___x_7686_);
                        v___x_7688_ = v_reuseFailAlloc_7691_;
                        state = 3;
                        continue;
                    }
                }
            }
            3 => {
                v___x_7689_ = lean_alloc_ctor(7, 2, (0) as u32);
                lean_ctor_set(v___x_7689_, 0, v___x_7688_);
                lean_ctor_set(v___x_7689_, 1, v___x_7684_);
                v___x_7690_ = l_Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3_spec__7___redArg(v___x_7689_, v___y_7675_, v___y_7676_, v___y_7673_, v___y_7674_, v___y_7677_, v___y_7669_);
                lean_dec_ref(v___y_7677_);
                return v___x_7690_;
            }
            4 => {
                lean_inc(v_a_7667_);
                v___x_7701_ = l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_instEvalExprConfig_evalExpr(v_a_7667_, v___y_7697_, v___y_7698_, v___y_7699_, v___y_7700_);
                if lean_obj_tag(v___x_7701_) == 0 {
                    lean_dec_ref(v___y_7699_);
                    lean_dec(v_a_7667_);
                    return v___x_7701_;
                } else {
                    v_a_7702_ = lean_ctor_get(v___x_7701_, 0);
                    lean_inc(v_a_7702_);
                    v___x_7703_ = l_Lean_Elab_unsupportedSyntaxExceptionId;
                    v___x_7704_ = l_Lean_Exception_isInterrupt(v_a_7702_);
                    if v___x_7704_ == 0 {
                        lean_inc(v_a_7702_);
                        v___x_7705_ = l_Lean_Exception_isRuntime(v_a_7702_);
                        v___y_7669_ = v___y_7700_;
                        v___y_7670_ = v___x_7703_;
                        v___y_7671_ = v___x_7701_;
                        v___y_7672_ = v_a_7702_;
                        v___y_7673_ = v___y_7697_;
                        v___y_7674_ = v___y_7698_;
                        v___y_7675_ = v___y_7695_;
                        v___y_7676_ = v___y_7696_;
                        v___y_7677_ = v___y_7699_;
                        v___y_7678_ = v___x_7705_;
                        state = 1;
                        continue;
                    } else {
                        v___y_7669_ = v___y_7700_;
                        v___y_7670_ = v___x_7703_;
                        v___y_7671_ = v___x_7701_;
                        v___y_7672_ = v_a_7702_;
                        v___y_7673_ = v___y_7697_;
                        v___y_7674_ = v___y_7698_;
                        v___y_7675_ = v___y_7695_;
                        v___y_7676_ = v___y_7696_;
                        v___y_7677_ = v___y_7699_;
                        v___y_7678_ = v___x_7704_;
                        state = 1;
                        continue;
                    }
                }
            }
            5 => {
                lean_inc(v_a_7667_);
                v___x_7713_ = l_Lean_Meta_getMVars(
                    v_a_7667_,
                    v___y_7709_,
                    v___y_7710_,
                    v___y_7711_,
                    v___y_7712_,
                );
                if lean_obj_tag(v___x_7713_) == 0 {
                    v_a_7714_ = lean_ctor_get(v___x_7713_, 0);
                    lean_inc(v_a_7714_);
                    lean_dec_ref_known(v___x_7713_, 1);
                    v___x_7715_ = l_Lean_Elab_Term_logUnassignedUsingErrorInfos(
                        v_a_7714_,
                        v___x_7641_,
                        v___y_7707_,
                        v___y_7708_,
                        v___y_7709_,
                        v___y_7710_,
                        v___y_7711_,
                        v___y_7712_,
                    );
                    lean_dec(v_a_7714_);
                    if lean_obj_tag(v___x_7715_) == 0 {
                        v_a_7716_ = lean_ctor_get(v___x_7715_, 0);
                        lean_inc(v_a_7716_);
                        lean_dec_ref_known(v___x_7715_, 1);
                        v___x_7717_ = (lean_unbox(v_a_7716_) as u8);
                        lean_dec(v_a_7716_);
                        if v___x_7717_ == 0 {
                            v___y_7695_ = v___y_7707_;
                            v___y_7696_ = v___y_7708_;
                            v___y_7697_ = v___y_7709_;
                            v___y_7698_ = v___y_7710_;
                            v___y_7699_ = v___y_7711_;
                            v___y_7700_ = v___y_7712_;
                            state = 4;
                            continue;
                        } else {
                            lean_dec_ref(v___y_7711_);
                            lean_dec(v_a_7667_);
                            v___x_7718_ = l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3_spec__8___redArg();
                            v_a_7719_ = lean_ctor_get(v___x_7718_, 0);
                            v_isSharedCheck_7726_ = (!lean_is_exclusive(v___x_7718_)) as u8;
                            if v_isSharedCheck_7726_ == 0 {
                                v___x_7721_ = v___x_7718_;
                                v_isShared_7722_ = v_isSharedCheck_7726_;
                                state = 6;
                                continue;
                            } else {
                                lean_inc(v_a_7719_);
                                lean_dec(v___x_7718_);
                                v___x_7721_ = lean_box(0);
                                v_isShared_7722_ = v_isSharedCheck_7726_;
                                state = 6;
                                continue;
                            }
                        }
                    } else {
                        lean_dec_ref(v___y_7711_);
                        lean_dec(v_a_7667_);
                        v_a_7727_ = lean_ctor_get(v___x_7715_, 0);
                        v_isSharedCheck_7734_ = (!lean_is_exclusive(v___x_7715_)) as u8;
                        if v_isSharedCheck_7734_ == 0 {
                            v___x_7729_ = v___x_7715_;
                            v_isShared_7730_ = v_isSharedCheck_7734_;
                            state = 8;
                            continue;
                        } else {
                            lean_inc(v_a_7727_);
                            lean_dec(v___x_7715_);
                            v___x_7729_ = lean_box(0);
                            v_isShared_7730_ = v_isSharedCheck_7734_;
                            state = 8;
                            continue;
                        }
                    }
                } else {
                    lean_dec_ref(v___y_7711_);
                    lean_dec(v_a_7667_);
                    v_a_7735_ = lean_ctor_get(v___x_7713_, 0);
                    v_isSharedCheck_7742_ = (!lean_is_exclusive(v___x_7713_)) as u8;
                    if v_isSharedCheck_7742_ == 0 {
                        v___x_7737_ = v___x_7713_;
                        v_isShared_7738_ = v_isSharedCheck_7742_;
                        state = 10;
                        continue;
                    } else {
                        lean_inc(v_a_7735_);
                        lean_dec(v___x_7713_);
                        v___x_7737_ = lean_box(0);
                        v_isShared_7738_ = v_isSharedCheck_7742_;
                        state = 10;
                        continue;
                    }
                }
            }
            6 => {
                if v_isShared_7722_ == 0 {
                    v___x_7724_ = v___x_7721_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_7725_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_7725_, 0, v_a_7719_);
                    v___x_7724_ = v_reuseFailAlloc_7725_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_7724_;
            }
            8 => {
                if v_isShared_7730_ == 0 {
                    v___x_7732_ = v___x_7729_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_7733_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_7733_, 0, v_a_7727_);
                    v___x_7732_ = v_reuseFailAlloc_7733_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_7732_;
            }
            10 => {
                if v_isShared_7738_ == 0 {
                    v___x_7740_ = v___x_7737_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_7741_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_7741_, 0, v_a_7735_);
                    v___x_7740_ = v_reuseFailAlloc_7741_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                return v___x_7740_;
            }
            12 => {
                v___x_7750_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__2_spec__4___closed__12), core::ptr::addr_of_mut!(l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__2_spec__4___closed__12_once), _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__2_spec__4___closed__12);
                v___x_7751_ = l_Lean_indentExpr(v_a_7667_);
                v___x_7752_ = lean_alloc_ctor(7, 2, (0) as u32);
                lean_ctor_set(v___x_7752_, 0, v___x_7750_);
                lean_ctor_set(v___x_7752_, 1, v___x_7751_);
                v___x_7753_ = l_Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3_spec__7___redArg(v___x_7752_, v___y_7744_, v___y_7745_, v___y_7746_, v___y_7747_, v___y_7748_, v___y_7749_);
                lean_dec_ref(v___y_7748_);
                v_a_7754_ = lean_ctor_get(v___x_7753_, 0);
                v_isSharedCheck_7761_ = (!lean_is_exclusive(v___x_7753_)) as u8;
                if v_isSharedCheck_7761_ == 0 {
                    v___x_7756_ = v___x_7753_;
                    v_isShared_7757_ = v_isSharedCheck_7761_;
                    state = 13;
                    continue;
                } else {
                    lean_inc(v_a_7754_);
                    lean_dec(v___x_7753_);
                    v___x_7756_ = lean_box(0);
                    v_isShared_7757_ = v_isSharedCheck_7761_;
                    state = 13;
                    continue;
                }
            }
            13 => {
                if v_isShared_7757_ == 0 {
                    v___x_7759_ = v___x_7756_;
                    state = 14;
                    continue;
                } else {
                    v_reuseFailAlloc_7760_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_7760_, 0, v_a_7754_);
                    v___x_7759_ = v_reuseFailAlloc_7760_;
                    state = 14;
                    continue;
                }
            }
            14 => {
                return v___x_7759_;
            }
            15 => {
                if v_isShared_7768_ == 0 {
                    v___x_7770_ = v___x_7767_;
                    state = 16;
                    continue;
                } else {
                    v_reuseFailAlloc_7771_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_7771_, 0, v_a_7765_);
                    v___x_7770_ = v_reuseFailAlloc_7771_;
                    state = 16;
                    continue;
                }
            }
            16 => {
                return v___x_7770_;
            }
            17 => {
                if v_isShared_7776_ == 0 {
                    v___x_7778_ = v___x_7775_;
                    state = 18;
                    continue;
                } else {
                    v_reuseFailAlloc_7779_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_7779_, 0, v_a_7773_);
                    v___x_7778_ = v_reuseFailAlloc_7779_;
                    state = 18;
                    continue;
                }
            }
            18 => {
                return v___x_7778_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3___boxed(
    mut v_stx_7781_: *mut LeanObject,
    mut v_a_7782_: *mut LeanObject,
    mut v_a_7783_: *mut LeanObject,
    mut v_a_7784_: *mut LeanObject,
    mut v_a_7785_: *mut LeanObject,
    mut v_a_7786_: *mut LeanObject,
    mut v_a_7787_: *mut LeanObject,
    mut v_a_7788_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_7789_: *mut LeanObject = core::ptr::null_mut();
    v_res_7789_ = l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3(v_stx_7781_, v_a_7782_, v_a_7783_, v_a_7784_, v_a_7785_, v_a_7786_, v_a_7787_);
    lean_dec(v_a_7787_);
    lean_dec_ref(v_a_7786_);
    lean_dec(v_a_7785_);
    lean_dec_ref(v_a_7784_);
    lean_dec(v_a_7783_);
    lean_dec_ref(v_a_7782_);
    return v_res_7789_;
}
pub unsafe fn _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__0_spec__0___closed__2()
-> *mut LeanObject {
    let mut v___x_7795_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7796_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7797_: *mut LeanObject = core::ptr::null_mut();
    v___x_7795_ = lean_box(0);
    v___x_7796_ = l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__0_spec__0___closed__1;
    v___x_7797_ = l_Lean_Expr_const___override(v___x_7796_, v___x_7795_);
    return v___x_7797_;
}
pub unsafe fn _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__0_spec__0___closed__3()
-> *mut LeanObject {
    let mut v___x_7798_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ty_x3f_7799_: *mut LeanObject = core::ptr::null_mut();
    v___x_7798_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__0_spec__0___closed__2), core::ptr::addr_of_mut!(l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__0_spec__0___closed__2_once), _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__0_spec__0___closed__2);
    v_ty_x3f_7799_ = lean_alloc_ctor(1, 1, (0) as u32);
    lean_ctor_set(v_ty_x3f_7799_, 0, v___x_7798_);
    return v_ty_x3f_7799_;
}
pub unsafe fn _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__0_spec__0___closed__4()
-> *mut LeanObject {
    let mut v___x_7800_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7801_: *mut LeanObject = core::ptr::null_mut();
    v___x_7800_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__0_spec__0___closed__2), core::ptr::addr_of_mut!(l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__0_spec__0___closed__2_once), _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__0_spec__0___closed__2);
    v___x_7801_ = l_Lean_MessageData_ofExpr(v___x_7800_);
    return v___x_7801_;
}
pub unsafe fn _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__0_spec__0___closed__5()
-> *mut LeanObject {
    let mut v___x_7802_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7803_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7804_: *mut LeanObject = core::ptr::null_mut();
    v___x_7802_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__0_spec__0___closed__4), core::ptr::addr_of_mut!(l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__0_spec__0___closed__4_once), _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__0_spec__0___closed__4);
    v___x_7803_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__2_spec__4___closed__5), core::ptr::addr_of_mut!(l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__2_spec__4___closed__5_once), _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__2_spec__4___closed__5);
    v___x_7804_ = lean_alloc_ctor(7, 2, (0) as u32);
    lean_ctor_set(v___x_7804_, 0, v___x_7803_);
    lean_ctor_set(v___x_7804_, 1, v___x_7802_);
    return v___x_7804_;
}
pub unsafe fn _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__0_spec__0___closed__6()
-> *mut LeanObject {
    let mut v___x_7805_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7806_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7807_: *mut LeanObject = core::ptr::null_mut();
    v___x_7805_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_withRWRulesSeq_go___closed__3), core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_withRWRulesSeq_go___closed__3_once), _init_l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_withRWRulesSeq_go___closed__3);
    v___x_7806_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__0_spec__0___closed__5), core::ptr::addr_of_mut!(l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__0_spec__0___closed__5_once), _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__0_spec__0___closed__5);
    v___x_7807_ = lean_alloc_ctor(7, 2, (0) as u32);
    lean_ctor_set(v___x_7807_, 0, v___x_7806_);
    lean_ctor_set(v___x_7807_, 1, v___x_7805_);
    return v___x_7807_;
}
pub unsafe fn l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__0_spec__0(
    mut v_stx_7808_: *mut LeanObject,
    mut v_a_7809_: *mut LeanObject,
    mut v_a_7810_: *mut LeanObject,
    mut v_a_7811_: *mut LeanObject,
    mut v_a_7812_: *mut LeanObject,
    mut v_a_7813_: *mut LeanObject,
    mut v_a_7814_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_ty_x3f_7816_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7817_: u8 = 0;
    let mut v___x_7818_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7819_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7820_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7821_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fileName_7822_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fileMap_7823_: *mut LeanObject = core::ptr::null_mut();
    let mut v_options_7824_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currRecDepth_7825_: *mut LeanObject = core::ptr::null_mut();
    let mut v_maxRecDepth_7826_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ref_7827_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currNamespace_7828_: *mut LeanObject = core::ptr::null_mut();
    let mut v_openDecls_7829_: *mut LeanObject = core::ptr::null_mut();
    let mut v_initHeartbeats_7830_: *mut LeanObject = core::ptr::null_mut();
    let mut v_maxHeartbeats_7831_: *mut LeanObject = core::ptr::null_mut();
    let mut v_quotContext_7832_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currMacroScope_7833_: *mut LeanObject = core::ptr::null_mut();
    let mut v_diag_7834_: u8 = 0;
    let mut v_cancelTk_x3f_7835_: *mut LeanObject = core::ptr::null_mut();
    let mut v_suppressElabErrors_7836_: u8 = 0;
    let mut v_inheritedTraceOptions_7837_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7838_: u8 = 0;
    let mut v_ref_7839_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7840_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7841_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_7842_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7843_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_7844_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7846_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7847_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7848_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7849_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7850_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7851_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7852_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7853_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7854_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7855_: u8 = 0;
    let mut v_id_7856_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7858_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7859_: u8 = 0;
    let mut v___x_7860_: u8 = 0;
    let mut v___x_7861_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7862_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7863_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7865_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7866_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7867_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7868_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7869_: u8 = 0;
    let mut v_unused_7870_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7872_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7873_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7874_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7875_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7876_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7877_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7878_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_7879_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7880_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7881_: u8 = 0;
    let mut v___x_7882_: u8 = 0;
    let mut v___y_7884_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7885_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7886_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7887_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7888_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7889_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7890_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_7891_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7892_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_7893_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7894_: u8 = 0;
    let mut v___x_7895_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_7896_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7898_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7899_: u8 = 0;
    let mut v___x_7901_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7902_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7903_: u8 = 0;
    let mut v_a_7904_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7906_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7907_: u8 = 0;
    let mut v___x_7909_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7910_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7911_: u8 = 0;
    let mut v_a_7912_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7914_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7915_: u8 = 0;
    let mut v___x_7917_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7918_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7919_: u8 = 0;
    let mut v___y_7921_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7922_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7923_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7924_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7925_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7926_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7927_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7928_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7929_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7930_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_7931_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7933_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7934_: u8 = 0;
    let mut v___x_7936_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7937_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7938_: u8 = 0;
    let mut v___x_7939_: u8 = 0;
    let mut v___x_7940_: u8 = 0;
    let mut v___x_7941_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_7942_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7944_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7945_: u8 = 0;
    let mut v___x_7947_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7948_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7949_: u8 = 0;
    let mut v_a_7950_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7952_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7953_: u8 = 0;
    let mut v___x_7955_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7956_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7957_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ty_x3f_7816_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__0_spec__0___closed__3), core::ptr::addr_of_mut!(l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__0_spec__0___closed__3_once), _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__0_spec__0___closed__3);
                v___x_7817_ = 1;
                v___x_7818_ = lean_box(0);
                v___x_7819_ = lean_box((v___x_7817_) as usize);
                v___x_7820_ = lean_box((v___x_7817_) as usize);
                lean_inc(v_stx_7808_);
                v___x_7821_ = lean_alloc_closure(
                    l_Lean_Elab_Term_elabTermEnsuringType___boxed as *mut core::ffi::c_void,
                    12,
                    5,
                );
                lean_closure_set(v___x_7821_, 0, v_stx_7808_);
                lean_closure_set(v___x_7821_, 1, v_ty_x3f_7816_);
                lean_closure_set(v___x_7821_, 2, v___x_7819_);
                lean_closure_set(v___x_7821_, 3, v___x_7820_);
                lean_closure_set(v___x_7821_, 4, v___x_7818_);
                v_fileName_7822_ = lean_ctor_get(v_a_7813_, 0);
                v_fileMap_7823_ = lean_ctor_get(v_a_7813_, 1);
                v_options_7824_ = lean_ctor_get(v_a_7813_, 2);
                v_currRecDepth_7825_ = lean_ctor_get(v_a_7813_, 3);
                v_maxRecDepth_7826_ = lean_ctor_get(v_a_7813_, 4);
                v_ref_7827_ = lean_ctor_get(v_a_7813_, 5);
                v_currNamespace_7828_ = lean_ctor_get(v_a_7813_, 6);
                v_openDecls_7829_ = lean_ctor_get(v_a_7813_, 7);
                v_initHeartbeats_7830_ = lean_ctor_get(v_a_7813_, 8);
                v_maxHeartbeats_7831_ = lean_ctor_get(v_a_7813_, 9);
                v_quotContext_7832_ = lean_ctor_get(v_a_7813_, 10);
                v_currMacroScope_7833_ = lean_ctor_get(v_a_7813_, 11);
                v_diag_7834_ = lean_ctor_get_uint8(
                    v_a_7813_,
                    (core::mem::size_of::<*mut LeanObject>() * 14) as u32,
                );
                v_cancelTk_x3f_7835_ = lean_ctor_get(v_a_7813_, 12);
                v_suppressElabErrors_7836_ = lean_ctor_get_uint8(
                    v_a_7813_,
                    (core::mem::size_of::<*mut LeanObject>() * 14 + 1) as u32,
                );
                v_inheritedTraceOptions_7837_ = lean_ctor_get(v_a_7813_, 13);
                v___x_7838_ = 1;
                v_ref_7839_ = l_Lean_replaceRef(v_stx_7808_, v_ref_7827_);
                lean_dec(v_stx_7808_);
                lean_inc_ref(v_inheritedTraceOptions_7837_);
                lean_inc(v_cancelTk_x3f_7835_);
                lean_inc(v_currMacroScope_7833_);
                lean_inc(v_quotContext_7832_);
                lean_inc(v_maxHeartbeats_7831_);
                lean_inc(v_initHeartbeats_7830_);
                lean_inc(v_openDecls_7829_);
                lean_inc(v_currNamespace_7828_);
                lean_inc(v_maxRecDepth_7826_);
                lean_inc(v_currRecDepth_7825_);
                lean_inc_ref(v_options_7824_);
                lean_inc_ref(v_fileMap_7823_);
                lean_inc_ref(v_fileName_7822_);
                v___x_7840_ = lean_alloc_ctor(0, 14, (2) as u32);
                lean_ctor_set(v___x_7840_, 0, v_fileName_7822_);
                lean_ctor_set(v___x_7840_, 1, v_fileMap_7823_);
                lean_ctor_set(v___x_7840_, 2, v_options_7824_);
                lean_ctor_set(v___x_7840_, 3, v_currRecDepth_7825_);
                lean_ctor_set(v___x_7840_, 4, v_maxRecDepth_7826_);
                lean_ctor_set(v___x_7840_, 5, v_ref_7839_);
                lean_ctor_set(v___x_7840_, 6, v_currNamespace_7828_);
                lean_ctor_set(v___x_7840_, 7, v_openDecls_7829_);
                lean_ctor_set(v___x_7840_, 8, v_initHeartbeats_7830_);
                lean_ctor_set(v___x_7840_, 9, v_maxHeartbeats_7831_);
                lean_ctor_set(v___x_7840_, 10, v_quotContext_7832_);
                lean_ctor_set(v___x_7840_, 11, v_currMacroScope_7833_);
                lean_ctor_set(v___x_7840_, 12, v_cancelTk_x3f_7835_);
                lean_ctor_set(v___x_7840_, 13, v_inheritedTraceOptions_7837_);
                lean_ctor_set_uint8(
                    v___x_7840_,
                    (core::mem::size_of::<*mut LeanObject>() * 14) as u32,
                    v_diag_7834_,
                );
                lean_ctor_set_uint8(
                    v___x_7840_,
                    (core::mem::size_of::<*mut LeanObject>() * 14 + 1) as u32,
                    v_suppressElabErrors_7836_,
                );
                v___x_7841_ =
                    l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_withSynthesizeImp(
                        lean_box(0),
                        v___x_7821_,
                        v___x_7838_,
                        v_a_7809_,
                        v_a_7810_,
                        v_a_7811_,
                        v_a_7812_,
                        v___x_7840_,
                        v_a_7814_,
                    );
                if lean_obj_tag(v___x_7841_) == 0 {
                    v_a_7842_ = lean_ctor_get(v___x_7841_, 0);
                    lean_inc(v_a_7842_);
                    lean_dec_ref_known(v___x_7841_, 1);
                    v___x_7843_ = l_Lean_instantiateMVars___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3_spec__6___redArg(v_a_7842_, v_a_7812_);
                    v_a_7844_ = lean_ctor_get(v___x_7843_, 0);
                    lean_inc(v_a_7844_);
                    lean_dec_ref(v___x_7843_);
                    v___x_7939_ = l_Lean_Expr_hasSorry(v_a_7844_);
                    if v___x_7939_ == 0 {
                        v___y_7884_ = v_a_7809_;
                        v___y_7885_ = v_a_7810_;
                        v___y_7886_ = v_a_7811_;
                        v___y_7887_ = v_a_7812_;
                        v___y_7888_ = v___x_7840_;
                        v___y_7889_ = v_a_7814_;
                        state = 5;
                        continue;
                    } else {
                        v___x_7940_ = l_Lean_Expr_hasSyntheticSorry(v_a_7844_);
                        if v___x_7940_ == 0 {
                            v___y_7921_ = v_a_7809_;
                            v___y_7922_ = v_a_7810_;
                            v___y_7923_ = v_a_7811_;
                            v___y_7924_ = v_a_7812_;
                            v___y_7925_ = v___x_7840_;
                            v___y_7926_ = v_a_7814_;
                            state = 12;
                            continue;
                        } else {
                            lean_dec(v_a_7844_);
                            lean_dec_ref_known(v___x_7840_, 14);
                            v___x_7941_ = l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3_spec__8___redArg();
                            v_a_7942_ = lean_ctor_get(v___x_7941_, 0);
                            v_isSharedCheck_7949_ = (!lean_is_exclusive(v___x_7941_)) as u8;
                            if v_isSharedCheck_7949_ == 0 {
                                v___x_7944_ = v___x_7941_;
                                v_isShared_7945_ = v_isSharedCheck_7949_;
                                state = 15;
                                continue;
                            } else {
                                lean_inc(v_a_7942_);
                                lean_dec(v___x_7941_);
                                v___x_7944_ = lean_box(0);
                                v_isShared_7945_ = v_isSharedCheck_7949_;
                                state = 15;
                                continue;
                            }
                        }
                    }
                } else {
                    lean_dec_ref_known(v___x_7840_, 14);
                    v_a_7950_ = lean_ctor_get(v___x_7841_, 0);
                    v_isSharedCheck_7957_ = (!lean_is_exclusive(v___x_7841_)) as u8;
                    if v_isSharedCheck_7957_ == 0 {
                        v___x_7952_ = v___x_7841_;
                        v_isShared_7953_ = v_isSharedCheck_7957_;
                        state = 17;
                        continue;
                    } else {
                        lean_inc(v_a_7950_);
                        lean_dec(v___x_7841_);
                        v___x_7952_ = lean_box(0);
                        v_isShared_7953_ = v_isSharedCheck_7957_;
                        state = 17;
                        continue;
                    }
                }
            }
            1 => {
                if v___y_7855_ == 0 {
                    if lean_obj_tag(v___y_7851_) == 0 {
                        lean_dec_ref_known(v___y_7851_, 2);
                        lean_dec_ref(v___y_7849_);
                        lean_dec(v_a_7844_);
                        return v___y_7846_;
                    } else {
                        v_id_7856_ = lean_ctor_get(v___y_7851_, 0);
                        v_isSharedCheck_7869_ = (!lean_is_exclusive(v___y_7851_)) as u8;
                        if v_isSharedCheck_7869_ == 0 {
                            v_unused_7870_ = lean_ctor_get(v___y_7851_, 1);
                            lean_dec(v_unused_7870_);
                            v___x_7858_ = v___y_7851_;
                            v_isShared_7859_ = v_isSharedCheck_7869_;
                            state = 2;
                            continue;
                        } else {
                            lean_inc(v_id_7856_);
                            lean_dec(v___y_7851_);
                            v___x_7858_ = lean_box(0);
                            v_isShared_7859_ = v_isSharedCheck_7869_;
                            state = 2;
                            continue;
                        }
                    }
                } else {
                    lean_dec_ref(v___y_7851_);
                    lean_dec_ref(v___y_7849_);
                    lean_dec(v_a_7844_);
                    return v___y_7846_;
                }
            }
            2 => {
                v___x_7860_ = l_Lean_instBEqInternalExceptionId_beq(v___y_7853_, v_id_7856_);
                lean_dec(v_id_7856_);
                if v___x_7860_ == 0 {
                    lean_del_object(v___x_7858_);
                    lean_dec_ref(v___y_7849_);
                    lean_dec(v_a_7844_);
                    return v___y_7846_;
                } else {
                    lean_dec_ref(v___y_7846_);
                    v___x_7861_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__0_spec__0___closed__6), core::ptr::addr_of_mut!(l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__0_spec__0___closed__6_once), _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__0_spec__0___closed__6);
                    v___x_7862_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__2_spec__4___closed__10), core::ptr::addr_of_mut!(l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__2_spec__4___closed__10_once), _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__2_spec__4___closed__10);
                    v___x_7863_ = l_Lean_indentExpr(v_a_7844_);
                    if v_isShared_7859_ == 0 {
                        lean_ctor_set_tag(v___x_7858_, 7);
                        lean_ctor_set(v___x_7858_, 1, v___x_7863_);
                        lean_ctor_set(v___x_7858_, 0, v___x_7862_);
                        v___x_7865_ = v___x_7858_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_7868_ = lean_alloc_ctor(7, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_7868_, 0, v___x_7862_);
                        lean_ctor_set(v_reuseFailAlloc_7868_, 1, v___x_7863_);
                        v___x_7865_ = v_reuseFailAlloc_7868_;
                        state = 3;
                        continue;
                    }
                }
            }
            3 => {
                v___x_7866_ = lean_alloc_ctor(7, 2, (0) as u32);
                lean_ctor_set(v___x_7866_, 0, v___x_7865_);
                lean_ctor_set(v___x_7866_, 1, v___x_7861_);
                v___x_7867_ = l_Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3_spec__7___redArg(v___x_7866_, v___y_7854_, v___y_7852_, v___y_7848_, v___y_7847_, v___y_7849_, v___y_7850_);
                lean_dec_ref(v___y_7849_);
                return v___x_7867_;
            }
            4 => {
                lean_inc(v_a_7844_);
                v___x_7878_ = l_Lean_Elab_ConfigEval_instEvalExprTransparencyMode_evalExpr(
                    v_a_7844_,
                    v___y_7874_,
                    v___y_7875_,
                    v___y_7876_,
                    v___y_7877_,
                );
                if lean_obj_tag(v___x_7878_) == 0 {
                    lean_dec_ref(v___y_7876_);
                    lean_dec(v_a_7844_);
                    return v___x_7878_;
                } else {
                    v_a_7879_ = lean_ctor_get(v___x_7878_, 0);
                    lean_inc(v_a_7879_);
                    v___x_7880_ = l_Lean_Elab_unsupportedSyntaxExceptionId;
                    v___x_7881_ = l_Lean_Exception_isInterrupt(v_a_7879_);
                    if v___x_7881_ == 0 {
                        lean_inc(v_a_7879_);
                        v___x_7882_ = l_Lean_Exception_isRuntime(v_a_7879_);
                        v___y_7846_ = v___x_7878_;
                        v___y_7847_ = v___y_7875_;
                        v___y_7848_ = v___y_7874_;
                        v___y_7849_ = v___y_7876_;
                        v___y_7850_ = v___y_7877_;
                        v___y_7851_ = v_a_7879_;
                        v___y_7852_ = v___y_7873_;
                        v___y_7853_ = v___x_7880_;
                        v___y_7854_ = v___y_7872_;
                        v___y_7855_ = v___x_7882_;
                        state = 1;
                        continue;
                    } else {
                        v___y_7846_ = v___x_7878_;
                        v___y_7847_ = v___y_7875_;
                        v___y_7848_ = v___y_7874_;
                        v___y_7849_ = v___y_7876_;
                        v___y_7850_ = v___y_7877_;
                        v___y_7851_ = v_a_7879_;
                        v___y_7852_ = v___y_7873_;
                        v___y_7853_ = v___x_7880_;
                        v___y_7854_ = v___y_7872_;
                        v___y_7855_ = v___x_7881_;
                        state = 1;
                        continue;
                    }
                }
            }
            5 => {
                lean_inc(v_a_7844_);
                v___x_7890_ = l_Lean_Meta_getMVars(
                    v_a_7844_,
                    v___y_7886_,
                    v___y_7887_,
                    v___y_7888_,
                    v___y_7889_,
                );
                if lean_obj_tag(v___x_7890_) == 0 {
                    v_a_7891_ = lean_ctor_get(v___x_7890_, 0);
                    lean_inc(v_a_7891_);
                    lean_dec_ref_known(v___x_7890_, 1);
                    v___x_7892_ = l_Lean_Elab_Term_logUnassignedUsingErrorInfos(
                        v_a_7891_,
                        v___x_7818_,
                        v___y_7884_,
                        v___y_7885_,
                        v___y_7886_,
                        v___y_7887_,
                        v___y_7888_,
                        v___y_7889_,
                    );
                    lean_dec(v_a_7891_);
                    if lean_obj_tag(v___x_7892_) == 0 {
                        v_a_7893_ = lean_ctor_get(v___x_7892_, 0);
                        lean_inc(v_a_7893_);
                        lean_dec_ref_known(v___x_7892_, 1);
                        v___x_7894_ = (lean_unbox(v_a_7893_) as u8);
                        lean_dec(v_a_7893_);
                        if v___x_7894_ == 0 {
                            v___y_7872_ = v___y_7884_;
                            v___y_7873_ = v___y_7885_;
                            v___y_7874_ = v___y_7886_;
                            v___y_7875_ = v___y_7887_;
                            v___y_7876_ = v___y_7888_;
                            v___y_7877_ = v___y_7889_;
                            state = 4;
                            continue;
                        } else {
                            lean_dec_ref(v___y_7888_);
                            lean_dec(v_a_7844_);
                            v___x_7895_ = l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3_spec__8___redArg();
                            v_a_7896_ = lean_ctor_get(v___x_7895_, 0);
                            v_isSharedCheck_7903_ = (!lean_is_exclusive(v___x_7895_)) as u8;
                            if v_isSharedCheck_7903_ == 0 {
                                v___x_7898_ = v___x_7895_;
                                v_isShared_7899_ = v_isSharedCheck_7903_;
                                state = 6;
                                continue;
                            } else {
                                lean_inc(v_a_7896_);
                                lean_dec(v___x_7895_);
                                v___x_7898_ = lean_box(0);
                                v_isShared_7899_ = v_isSharedCheck_7903_;
                                state = 6;
                                continue;
                            }
                        }
                    } else {
                        lean_dec_ref(v___y_7888_);
                        lean_dec(v_a_7844_);
                        v_a_7904_ = lean_ctor_get(v___x_7892_, 0);
                        v_isSharedCheck_7911_ = (!lean_is_exclusive(v___x_7892_)) as u8;
                        if v_isSharedCheck_7911_ == 0 {
                            v___x_7906_ = v___x_7892_;
                            v_isShared_7907_ = v_isSharedCheck_7911_;
                            state = 8;
                            continue;
                        } else {
                            lean_inc(v_a_7904_);
                            lean_dec(v___x_7892_);
                            v___x_7906_ = lean_box(0);
                            v_isShared_7907_ = v_isSharedCheck_7911_;
                            state = 8;
                            continue;
                        }
                    }
                } else {
                    lean_dec_ref(v___y_7888_);
                    lean_dec(v_a_7844_);
                    v_a_7912_ = lean_ctor_get(v___x_7890_, 0);
                    v_isSharedCheck_7919_ = (!lean_is_exclusive(v___x_7890_)) as u8;
                    if v_isSharedCheck_7919_ == 0 {
                        v___x_7914_ = v___x_7890_;
                        v_isShared_7915_ = v_isSharedCheck_7919_;
                        state = 10;
                        continue;
                    } else {
                        lean_inc(v_a_7912_);
                        lean_dec(v___x_7890_);
                        v___x_7914_ = lean_box(0);
                        v_isShared_7915_ = v_isSharedCheck_7919_;
                        state = 10;
                        continue;
                    }
                }
            }
            6 => {
                if v_isShared_7899_ == 0 {
                    v___x_7901_ = v___x_7898_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_7902_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_7902_, 0, v_a_7896_);
                    v___x_7901_ = v_reuseFailAlloc_7902_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_7901_;
            }
            8 => {
                if v_isShared_7907_ == 0 {
                    v___x_7909_ = v___x_7906_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_7910_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_7910_, 0, v_a_7904_);
                    v___x_7909_ = v_reuseFailAlloc_7910_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_7909_;
            }
            10 => {
                if v_isShared_7915_ == 0 {
                    v___x_7917_ = v___x_7914_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_7918_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_7918_, 0, v_a_7912_);
                    v___x_7917_ = v_reuseFailAlloc_7918_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                return v___x_7917_;
            }
            12 => {
                v___x_7927_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__2_spec__4___closed__12), core::ptr::addr_of_mut!(l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__2_spec__4___closed__12_once), _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__2_spec__4___closed__12);
                v___x_7928_ = l_Lean_indentExpr(v_a_7844_);
                v___x_7929_ = lean_alloc_ctor(7, 2, (0) as u32);
                lean_ctor_set(v___x_7929_, 0, v___x_7927_);
                lean_ctor_set(v___x_7929_, 1, v___x_7928_);
                v___x_7930_ = l_Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3_spec__7___redArg(v___x_7929_, v___y_7921_, v___y_7922_, v___y_7923_, v___y_7924_, v___y_7925_, v___y_7926_);
                lean_dec_ref(v___y_7925_);
                v_a_7931_ = lean_ctor_get(v___x_7930_, 0);
                v_isSharedCheck_7938_ = (!lean_is_exclusive(v___x_7930_)) as u8;
                if v_isSharedCheck_7938_ == 0 {
                    v___x_7933_ = v___x_7930_;
                    v_isShared_7934_ = v_isSharedCheck_7938_;
                    state = 13;
                    continue;
                } else {
                    lean_inc(v_a_7931_);
                    lean_dec(v___x_7930_);
                    v___x_7933_ = lean_box(0);
                    v_isShared_7934_ = v_isSharedCheck_7938_;
                    state = 13;
                    continue;
                }
            }
            13 => {
                if v_isShared_7934_ == 0 {
                    v___x_7936_ = v___x_7933_;
                    state = 14;
                    continue;
                } else {
                    v_reuseFailAlloc_7937_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_7937_, 0, v_a_7931_);
                    v___x_7936_ = v_reuseFailAlloc_7937_;
                    state = 14;
                    continue;
                }
            }
            14 => {
                return v___x_7936_;
            }
            15 => {
                if v_isShared_7945_ == 0 {
                    v___x_7947_ = v___x_7944_;
                    state = 16;
                    continue;
                } else {
                    v_reuseFailAlloc_7948_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_7948_, 0, v_a_7942_);
                    v___x_7947_ = v_reuseFailAlloc_7948_;
                    state = 16;
                    continue;
                }
            }
            16 => {
                return v___x_7947_;
            }
            17 => {
                if v_isShared_7953_ == 0 {
                    v___x_7955_ = v___x_7952_;
                    state = 18;
                    continue;
                } else {
                    v_reuseFailAlloc_7956_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_7956_, 0, v_a_7950_);
                    v___x_7955_ = v_reuseFailAlloc_7956_;
                    state = 18;
                    continue;
                }
            }
            18 => {
                return v___x_7955_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__0_spec__0___boxed(
    mut v_stx_7958_: *mut LeanObject,
    mut v_a_7959_: *mut LeanObject,
    mut v_a_7960_: *mut LeanObject,
    mut v_a_7961_: *mut LeanObject,
    mut v_a_7962_: *mut LeanObject,
    mut v_a_7963_: *mut LeanObject,
    mut v_a_7964_: *mut LeanObject,
    mut v_a_7965_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_7966_: *mut LeanObject = core::ptr::null_mut();
    v_res_7966_ = l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__0_spec__0(v_stx_7958_, v_a_7959_, v_a_7960_, v_a_7961_, v_a_7962_, v_a_7963_, v_a_7964_);
    lean_dec(v_a_7964_);
    lean_dec_ref(v_a_7963_);
    lean_dec(v_a_7962_);
    lean_dec_ref(v_a_7961_);
    lean_dec(v_a_7960_);
    lean_dec_ref(v_a_7959_);
    return v_res_7966_;
}
pub unsafe fn l_Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__0(
    mut v_stx_7967_: *mut LeanObject,
    mut v_a_7968_: *mut LeanObject,
    mut v_a_7969_: *mut LeanObject,
    mut v_a_7970_: *mut LeanObject,
    mut v_a_7971_: *mut LeanObject,
    mut v_a_7972_: *mut LeanObject,
    mut v_a_7973_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_fileName_7975_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fileMap_7976_: *mut LeanObject = core::ptr::null_mut();
    let mut v_options_7977_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currRecDepth_7978_: *mut LeanObject = core::ptr::null_mut();
    let mut v_maxRecDepth_7979_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ref_7980_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currNamespace_7981_: *mut LeanObject = core::ptr::null_mut();
    let mut v_openDecls_7982_: *mut LeanObject = core::ptr::null_mut();
    let mut v_initHeartbeats_7983_: *mut LeanObject = core::ptr::null_mut();
    let mut v_maxHeartbeats_7984_: *mut LeanObject = core::ptr::null_mut();
    let mut v_quotContext_7985_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currMacroScope_7986_: *mut LeanObject = core::ptr::null_mut();
    let mut v_diag_7987_: u8 = 0;
    let mut v_cancelTk_x3f_7988_: *mut LeanObject = core::ptr::null_mut();
    let mut v_suppressElabErrors_7989_: u8 = 0;
    let mut v_inheritedTraceOptions_7990_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ref_7991_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7992_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7993_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_7994_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7996_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7997_: u8 = 0;
    let mut v_fst_7998_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8000_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8001_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_8002_: u8 = 0;
    let mut v_a_8003_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8005_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_8006_: u8 = 0;
    let mut v___x_8007_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8009_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_8011_: u8 = 0;
    let mut v_id_8012_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8013_: u8 = 0;
    let mut v___x_8014_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8015_: u8 = 0;
    let mut v___x_8016_: u8 = 0;
    let mut v_reuseFailAlloc_8017_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_8018_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_fileName_7975_ = lean_ctor_get(v_a_7972_, 0);
                v_fileMap_7976_ = lean_ctor_get(v_a_7972_, 1);
                v_options_7977_ = lean_ctor_get(v_a_7972_, 2);
                v_currRecDepth_7978_ = lean_ctor_get(v_a_7972_, 3);
                v_maxRecDepth_7979_ = lean_ctor_get(v_a_7972_, 4);
                v_ref_7980_ = lean_ctor_get(v_a_7972_, 5);
                v_currNamespace_7981_ = lean_ctor_get(v_a_7972_, 6);
                v_openDecls_7982_ = lean_ctor_get(v_a_7972_, 7);
                v_initHeartbeats_7983_ = lean_ctor_get(v_a_7972_, 8);
                v_maxHeartbeats_7984_ = lean_ctor_get(v_a_7972_, 9);
                v_quotContext_7985_ = lean_ctor_get(v_a_7972_, 10);
                v_currMacroScope_7986_ = lean_ctor_get(v_a_7972_, 11);
                v_diag_7987_ = lean_ctor_get_uint8(
                    v_a_7972_,
                    (core::mem::size_of::<*mut LeanObject>() * 14) as u32,
                );
                v_cancelTk_x3f_7988_ = lean_ctor_get(v_a_7972_, 12);
                v_suppressElabErrors_7989_ = lean_ctor_get_uint8(
                    v_a_7972_,
                    (core::mem::size_of::<*mut LeanObject>() * 14 + 1) as u32,
                );
                v_inheritedTraceOptions_7990_ = lean_ctor_get(v_a_7972_, 13);
                v_ref_7991_ = l_Lean_replaceRef(v_stx_7967_, v_ref_7980_);
                lean_inc_ref(v_inheritedTraceOptions_7990_);
                lean_inc(v_cancelTk_x3f_7988_);
                lean_inc(v_currMacroScope_7986_);
                lean_inc(v_quotContext_7985_);
                lean_inc(v_maxHeartbeats_7984_);
                lean_inc(v_initHeartbeats_7983_);
                lean_inc(v_openDecls_7982_);
                lean_inc(v_currNamespace_7981_);
                lean_inc(v_maxRecDepth_7979_);
                lean_inc(v_currRecDepth_7978_);
                lean_inc_ref(v_options_7977_);
                lean_inc_ref(v_fileMap_7976_);
                lean_inc_ref(v_fileName_7975_);
                v___x_7992_ = lean_alloc_ctor(0, 14, (2) as u32);
                lean_ctor_set(v___x_7992_, 0, v_fileName_7975_);
                lean_ctor_set(v___x_7992_, 1, v_fileMap_7976_);
                lean_ctor_set(v___x_7992_, 2, v_options_7977_);
                lean_ctor_set(v___x_7992_, 3, v_currRecDepth_7978_);
                lean_ctor_set(v___x_7992_, 4, v_maxRecDepth_7979_);
                lean_ctor_set(v___x_7992_, 5, v_ref_7991_);
                lean_ctor_set(v___x_7992_, 6, v_currNamespace_7981_);
                lean_ctor_set(v___x_7992_, 7, v_openDecls_7982_);
                lean_ctor_set(v___x_7992_, 8, v_initHeartbeats_7983_);
                lean_ctor_set(v___x_7992_, 9, v_maxHeartbeats_7984_);
                lean_ctor_set(v___x_7992_, 10, v_quotContext_7985_);
                lean_ctor_set(v___x_7992_, 11, v_currMacroScope_7986_);
                lean_ctor_set(v___x_7992_, 12, v_cancelTk_x3f_7988_);
                lean_ctor_set(v___x_7992_, 13, v_inheritedTraceOptions_7990_);
                lean_ctor_set_uint8(
                    v___x_7992_,
                    (core::mem::size_of::<*mut LeanObject>() * 14) as u32,
                    v_diag_7987_,
                );
                lean_ctor_set_uint8(
                    v___x_7992_,
                    (core::mem::size_of::<*mut LeanObject>() * 14 + 1) as u32,
                    v_suppressElabErrors_7989_,
                );
                lean_inc(v_stx_7967_);
                v___x_7993_ = l_Lean_Elab_ConfigEval_instEvalTermTransparencyMode_evalTerm(
                    v_stx_7967_,
                    v_a_7968_,
                    v_a_7969_,
                    v_a_7970_,
                    v_a_7971_,
                    v___x_7992_,
                    v_a_7973_,
                );
                if lean_obj_tag(v___x_7993_) == 0 {
                    lean_dec_ref_known(v___x_7992_, 14);
                    lean_dec(v_stx_7967_);
                    v_a_7994_ = lean_ctor_get(v___x_7993_, 0);
                    v_isSharedCheck_8002_ = (!lean_is_exclusive(v___x_7993_)) as u8;
                    if v_isSharedCheck_8002_ == 0 {
                        v___x_7996_ = v___x_7993_;
                        v_isShared_7997_ = v_isSharedCheck_8002_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_7994_);
                        lean_dec(v___x_7993_);
                        v___x_7996_ = lean_box(0);
                        v_isShared_7997_ = v_isSharedCheck_8002_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_8003_ = lean_ctor_get(v___x_7993_, 0);
                    v_isSharedCheck_8018_ = (!lean_is_exclusive(v___x_7993_)) as u8;
                    if v_isSharedCheck_8018_ == 0 {
                        v___x_8005_ = v___x_7993_;
                        v_isShared_8006_ = v_isSharedCheck_8018_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_8003_);
                        lean_dec(v___x_7993_);
                        v___x_8005_ = lean_box(0);
                        v_isShared_8006_ = v_isSharedCheck_8018_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v_fst_7998_ = lean_ctor_get(v_a_7994_, 0);
                lean_inc(v_fst_7998_);
                lean_dec(v_a_7994_);
                if v_isShared_7997_ == 0 {
                    lean_ctor_set(v___x_7996_, 0, v_fst_7998_);
                    v___x_8000_ = v___x_7996_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_8001_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_8001_, 0, v_fst_7998_);
                    v___x_8000_ = v_reuseFailAlloc_8001_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_8000_;
            }
            3 => {
                v___x_8007_ = l_Lean_Elab_unsupportedSyntaxExceptionId;
                lean_inc(v_a_8003_);
                if v_isShared_8006_ == 0 {
                    v___x_8009_ = v___x_8005_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_8017_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_8017_, 0, v_a_8003_);
                    v___x_8009_ = v_reuseFailAlloc_8017_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_8015_ = l_Lean_Exception_isInterrupt(v_a_8003_);
                if v___x_8015_ == 0 {
                    lean_inc(v_a_8003_);
                    v___x_8016_ = l_Lean_Exception_isRuntime(v_a_8003_);
                    v___y_8011_ = v___x_8016_;
                    state = 5;
                    continue;
                } else {
                    v___y_8011_ = v___x_8015_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                if v___y_8011_ == 0 {
                    if lean_obj_tag(v_a_8003_) == 0 {
                        lean_dec_ref_known(v_a_8003_, 2);
                        lean_dec_ref_known(v___x_7992_, 14);
                        lean_dec(v_stx_7967_);
                        return v___x_8009_;
                    } else {
                        v_id_8012_ = lean_ctor_get(v_a_8003_, 0);
                        lean_inc(v_id_8012_);
                        lean_dec_ref_known(v_a_8003_, 2);
                        v___x_8013_ =
                            l_Lean_instBEqInternalExceptionId_beq(v___x_8007_, v_id_8012_);
                        lean_dec(v_id_8012_);
                        if v___x_8013_ == 0 {
                            lean_dec_ref_known(v___x_7992_, 14);
                            lean_dec(v_stx_7967_);
                            return v___x_8009_;
                        } else {
                            lean_dec_ref(v___x_8009_);
                            v___x_8014_ = l_Lean_Elab_ConfigEval_evalExprWithElab___at___00Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__0_spec__0(v_stx_7967_, v_a_7968_, v_a_7969_, v_a_7970_, v_a_7971_, v___x_7992_, v_a_7973_);
                            lean_dec_ref_known(v___x_7992_, 14);
                            return v___x_8014_;
                        }
                    }
                } else {
                    lean_dec(v_a_8003_);
                    lean_dec_ref_known(v___x_7992_, 14);
                    lean_dec(v_stx_7967_);
                    return v___x_8009_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__0___boxed(
    mut v_stx_8019_: *mut LeanObject,
    mut v_a_8020_: *mut LeanObject,
    mut v_a_8021_: *mut LeanObject,
    mut v_a_8022_: *mut LeanObject,
    mut v_a_8023_: *mut LeanObject,
    mut v_a_8024_: *mut LeanObject,
    mut v_a_8025_: *mut LeanObject,
    mut v_a_8026_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_8027_: *mut LeanObject = core::ptr::null_mut();
    v_res_8027_ = l_Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__0(v_stx_8019_, v_a_8020_, v_a_8021_, v_a_8022_, v_a_8023_, v_a_8024_, v_a_8025_);
    lean_dec(v_a_8025_);
    lean_dec_ref(v_a_8024_);
    lean_dec(v_a_8023_);
    lean_dec_ref(v_a_8022_);
    lean_dec(v_a_8021_);
    lean_dec_ref(v_a_8020_);
    return v_res_8027_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem___lam__0(
    mut v_config_8059_: *mut LeanObject,
    mut v_item_8060_: *mut LeanObject,
    mut v___y_8061_: *mut LeanObject,
    mut v___y_8062_: *mut LeanObject,
    mut v___y_8063_: *mut LeanObject,
    mut v___y_8064_: *mut LeanObject,
    mut v___y_8065_: *mut LeanObject,
    mut v___y_8066_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_item_8069_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_8070_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_8071_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_8072_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_8073_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_8074_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_8075_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8076_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8077_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8078_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8079_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8080_: u8 = 0;
    let mut v___x_8081_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8082_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8083_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8084_: u8 = 0;
    let mut v___x_8085_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8086_: u8 = 0;
    let mut v___x_8087_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8088_: u8 = 0;
    let mut v___x_8089_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8090_: u8 = 0;
    let mut v___x_8091_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8092_: u8 = 0;
    let mut v___x_8093_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8094_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8095_: u8 = 0;
    let mut v___x_8096_: *mut LeanObject = core::ptr::null_mut();
    let mut v_value_8097_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8098_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_8099_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8101_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_8102_: u8 = 0;
    let mut v_offsetCnstrs_8103_: u8 = 0;
    let mut v_occs_8104_: *mut LeanObject = core::ptr::null_mut();
    let mut v_newGoals_8105_: u8 = 0;
    let mut v___x_8107_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_8108_: u8 = 0;
    let mut v___x_8110_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8111_: u8 = 0;
    let mut v___x_8113_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8114_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8115_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_8116_: u8 = 0;
    let mut v_isSharedCheck_8117_: u8 = 0;
    let mut v_a_8118_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8120_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_8121_: u8 = 0;
    let mut v___x_8123_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8124_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_8125_: u8 = 0;
    let mut v_a_8126_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8128_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_8129_: u8 = 0;
    let mut v___x_8131_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8132_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_8133_: u8 = 0;
    let mut v_a_8134_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8136_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_8137_: u8 = 0;
    let mut v___x_8139_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8140_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_8141_: u8 = 0;
    let mut v___x_8142_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8143_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8144_: u8 = 0;
    let mut v___x_8145_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_8146_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8148_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_8149_: u8 = 0;
    let mut v_transparency_8150_: u8 = 0;
    let mut v_occs_8151_: *mut LeanObject = core::ptr::null_mut();
    let mut v_newGoals_8152_: u8 = 0;
    let mut v___x_8154_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_8155_: u8 = 0;
    let mut v___x_8157_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8158_: u8 = 0;
    let mut v___x_8160_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8161_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8162_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_8163_: u8 = 0;
    let mut v_isSharedCheck_8164_: u8 = 0;
    let mut v_a_8165_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8167_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_8168_: u8 = 0;
    let mut v___x_8170_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8171_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_8172_: u8 = 0;
    let mut v_a_8173_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8175_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_8176_: u8 = 0;
    let mut v___x_8178_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8179_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_8180_: u8 = 0;
    let mut v___x_8181_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8182_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8183_: u8 = 0;
    let mut v___x_8184_: *mut LeanObject = core::ptr::null_mut();
    let mut v_value_8185_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8186_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_8187_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8189_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_8190_: u8 = 0;
    let mut v_transparency_8191_: u8 = 0;
    let mut v_offsetCnstrs_8192_: u8 = 0;
    let mut v_newGoals_8193_: u8 = 0;
    let mut v___x_8195_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_8196_: u8 = 0;
    let mut v___x_8198_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8200_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8201_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8202_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_8203_: u8 = 0;
    let mut v_unused_8204_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_8205_: u8 = 0;
    let mut v_a_8206_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8208_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_8209_: u8 = 0;
    let mut v___x_8211_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8212_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_8213_: u8 = 0;
    let mut v_a_8214_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8216_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_8217_: u8 = 0;
    let mut v___x_8219_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8220_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_8221_: u8 = 0;
    let mut v_a_8222_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8224_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_8225_: u8 = 0;
    let mut v___x_8227_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8228_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_8229_: u8 = 0;
    let mut v___x_8230_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8231_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8232_: u8 = 0;
    let mut v___x_8233_: *mut LeanObject = core::ptr::null_mut();
    let mut v_value_8234_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8235_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_8236_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8238_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_8239_: u8 = 0;
    let mut v_transparency_8240_: u8 = 0;
    let mut v_offsetCnstrs_8241_: u8 = 0;
    let mut v_occs_8242_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8244_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_8245_: u8 = 0;
    let mut v___x_8247_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8248_: u8 = 0;
    let mut v___x_8250_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8251_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8252_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_8253_: u8 = 0;
    let mut v_isSharedCheck_8254_: u8 = 0;
    let mut v_a_8255_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8257_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_8258_: u8 = 0;
    let mut v___x_8260_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8261_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_8262_: u8 = 0;
    let mut v_a_8263_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8265_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_8266_: u8 = 0;
    let mut v___x_8268_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8269_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_8270_: u8 = 0;
    let mut v_a_8271_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8273_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_8274_: u8 = 0;
    let mut v___x_8276_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8277_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_8278_: u8 = 0;
    let mut v___x_8279_: u8 = 0;
    let mut v_value_8280_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8281_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_8282_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8284_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_8285_: u8 = 0;
    let mut v___x_8287_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8288_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_8289_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_8078_ = l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_instEvalExprConfig_evalExpr___closed__4;
                v___x_8079_ = l_Lean_Elab_ConfigEval_ConfigItem_addCompletionInfo(
                    v_item_8060_,
                    v___x_8078_,
                    v___y_8061_,
                    v___y_8062_,
                    v___y_8063_,
                    v___y_8064_,
                    v___y_8065_,
                    v___y_8066_,
                );
                if lean_obj_tag(v___x_8079_) == 0 {
                    lean_dec_ref_known(v___x_8079_, 1);
                    v___x_8080_ = l_Lean_Elab_ConfigEval_ConfigItem_isAnonymous(v_item_8060_);
                    if v___x_8080_ == 0 {
                        v___x_8081_ = l_Lean_Elab_ConfigEval_ConfigItem_getRootStr(v_item_8060_);
                        lean_inc_ref(v_item_8060_);
                        v___x_8082_ = l_Lean_Elab_ConfigEval_ConfigItem_shift(v_item_8060_);
                        v___x_8083_ = l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem___lam__0___closed__1;
                        v___x_8084_ = lean_string_dec_eq(v___x_8081_, v___x_8083_);
                        if v___x_8084_ == 0 {
                            v___x_8085_ = l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem___lam__0___closed__2;
                            v___x_8086_ = lean_string_dec_eq(v___x_8081_, v___x_8085_);
                            if v___x_8086_ == 0 {
                                v___x_8087_ = l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem___lam__0___closed__3;
                                v___x_8088_ = lean_string_dec_eq(v___x_8081_, v___x_8087_);
                                if v___x_8088_ == 0 {
                                    v___x_8089_ = l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem___lam__0___closed__4;
                                    v___x_8090_ = lean_string_dec_eq(v___x_8081_, v___x_8089_);
                                    if v___x_8090_ == 0 {
                                        v___x_8091_ = l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem___lam__0___closed__5;
                                        v___x_8092_ = lean_string_dec_eq(v___x_8081_, v___x_8091_);
                                        lean_dec_ref(v___x_8081_);
                                        if v___x_8092_ == 0 {
                                            lean_dec_ref(v_item_8060_);
                                            lean_dec_ref(v_config_8059_);
                                            v_item_8069_ = v___x_8082_;
                                            v___y_8070_ = v___y_8061_;
                                            v___y_8071_ = v___y_8062_;
                                            v___y_8072_ = v___y_8063_;
                                            v___y_8073_ = v___y_8064_;
                                            v___y_8074_ = v___y_8065_;
                                            v___y_8075_ = v___y_8066_;
                                            state = 1;
                                            continue;
                                        } else {
                                            v___x_8093_ = l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem___lam__0___closed__6;
                                            v___x_8094_ =
                                                l_Lean_Elab_ConfigEval_ConfigItem_addConstInfo(
                                                    v_item_8060_,
                                                    v___x_8093_,
                                                    v___y_8061_,
                                                    v___y_8062_,
                                                    v___y_8063_,
                                                    v___y_8064_,
                                                    v___y_8065_,
                                                    v___y_8066_,
                                                );
                                            if lean_obj_tag(v___x_8094_) == 0 {
                                                lean_dec_ref_known(v___x_8094_, 1);
                                                v___x_8095_ =
                                                    l_Lean_Elab_ConfigEval_ConfigItem_isAnonymous(
                                                        v___x_8082_,
                                                    );
                                                if v___x_8095_ == 0 {
                                                    lean_dec_ref(v_item_8060_);
                                                    lean_dec_ref(v_config_8059_);
                                                    v_item_8069_ = v___x_8082_;
                                                    v___y_8070_ = v___y_8061_;
                                                    v___y_8071_ = v___y_8062_;
                                                    v___y_8072_ = v___y_8063_;
                                                    v___y_8073_ = v___y_8064_;
                                                    v___y_8074_ = v___y_8065_;
                                                    v___y_8075_ = v___y_8066_;
                                                    state = 1;
                                                    continue;
                                                } else {
                                                    lean_dec_ref(v___x_8082_);
                                                    lean_inc_ref(v_item_8060_);
                                                    v___x_8096_ = l_Lean_Elab_ConfigEval_ConfigItem_checkNotBool(v_item_8060_, v___y_8061_, v___y_8062_, v___y_8063_, v___y_8064_, v___y_8065_, v___y_8066_);
                                                    if lean_obj_tag(v___x_8096_) == 0 {
                                                        lean_dec_ref_known(v___x_8096_, 1);
                                                        v_value_8097_ =
                                                            lean_ctor_get(v_item_8060_, 2);
                                                        lean_inc(v_value_8097_);
                                                        lean_dec_ref(v_item_8060_);
                                                        v___x_8098_ = l_Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__0(v_value_8097_, v___y_8061_, v___y_8062_, v___y_8063_, v___y_8064_, v___y_8065_, v___y_8066_);
                                                        if lean_obj_tag(v___x_8098_) == 0 {
                                                            v_a_8099_ =
                                                                lean_ctor_get(v___x_8098_, 0);
                                                            v_isSharedCheck_8117_ =
                                                                (!lean_is_exclusive(v___x_8098_))
                                                                    as u8;
                                                            if v_isSharedCheck_8117_ == 0 {
                                                                v___x_8101_ = v___x_8098_;
                                                                v_isShared_8102_ =
                                                                    v_isSharedCheck_8117_;
                                                                state = 2;
                                                                continue;
                                                            } else {
                                                                lean_inc(v_a_8099_);
                                                                lean_dec(v___x_8098_);
                                                                v___x_8101_ = lean_box(0);
                                                                v_isShared_8102_ =
                                                                    v_isSharedCheck_8117_;
                                                                state = 2;
                                                                continue;
                                                            }
                                                        } else {
                                                            lean_dec_ref(v_config_8059_);
                                                            v_a_8118_ =
                                                                lean_ctor_get(v___x_8098_, 0);
                                                            v_isSharedCheck_8125_ =
                                                                (!lean_is_exclusive(v___x_8098_))
                                                                    as u8;
                                                            if v_isSharedCheck_8125_ == 0 {
                                                                v___x_8120_ = v___x_8098_;
                                                                v_isShared_8121_ =
                                                                    v_isSharedCheck_8125_;
                                                                state = 6;
                                                                continue;
                                                            } else {
                                                                lean_inc(v_a_8118_);
                                                                lean_dec(v___x_8098_);
                                                                v___x_8120_ = lean_box(0);
                                                                v_isShared_8121_ =
                                                                    v_isSharedCheck_8125_;
                                                                state = 6;
                                                                continue;
                                                            }
                                                        }
                                                    } else {
                                                        lean_dec_ref(v_item_8060_);
                                                        lean_dec_ref(v_config_8059_);
                                                        v_a_8126_ = lean_ctor_get(v___x_8096_, 0);
                                                        v_isSharedCheck_8133_ =
                                                            (!lean_is_exclusive(v___x_8096_)) as u8;
                                                        if v_isSharedCheck_8133_ == 0 {
                                                            v___x_8128_ = v___x_8096_;
                                                            v_isShared_8129_ =
                                                                v_isSharedCheck_8133_;
                                                            state = 8;
                                                            continue;
                                                        } else {
                                                            lean_inc(v_a_8126_);
                                                            lean_dec(v___x_8096_);
                                                            v___x_8128_ = lean_box(0);
                                                            v_isShared_8129_ =
                                                                v_isSharedCheck_8133_;
                                                            state = 8;
                                                            continue;
                                                        }
                                                    }
                                                }
                                            } else {
                                                lean_dec_ref(v___x_8082_);
                                                lean_dec_ref(v_item_8060_);
                                                lean_dec_ref(v_config_8059_);
                                                v_a_8134_ = lean_ctor_get(v___x_8094_, 0);
                                                v_isSharedCheck_8141_ =
                                                    (!lean_is_exclusive(v___x_8094_)) as u8;
                                                if v_isSharedCheck_8141_ == 0 {
                                                    v___x_8136_ = v___x_8094_;
                                                    v_isShared_8137_ = v_isSharedCheck_8141_;
                                                    state = 10;
                                                    continue;
                                                } else {
                                                    lean_inc(v_a_8134_);
                                                    lean_dec(v___x_8094_);
                                                    v___x_8136_ = lean_box(0);
                                                    v_isShared_8137_ = v_isSharedCheck_8141_;
                                                    state = 10;
                                                    continue;
                                                }
                                            }
                                        }
                                    } else {
                                        lean_dec_ref(v___x_8081_);
                                        v___x_8142_ = l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem___lam__0___closed__7;
                                        v___x_8143_ =
                                            l_Lean_Elab_ConfigEval_ConfigItem_addConstInfo(
                                                v_item_8060_,
                                                v___x_8142_,
                                                v___y_8061_,
                                                v___y_8062_,
                                                v___y_8063_,
                                                v___y_8064_,
                                                v___y_8065_,
                                                v___y_8066_,
                                            );
                                        if lean_obj_tag(v___x_8143_) == 0 {
                                            lean_dec_ref_known(v___x_8143_, 1);
                                            v___x_8144_ =
                                                l_Lean_Elab_ConfigEval_ConfigItem_isAnonymous(
                                                    v___x_8082_,
                                                );
                                            if v___x_8144_ == 0 {
                                                lean_dec_ref(v_item_8060_);
                                                lean_dec_ref(v_config_8059_);
                                                v_item_8069_ = v___x_8082_;
                                                v___y_8070_ = v___y_8061_;
                                                v___y_8071_ = v___y_8062_;
                                                v___y_8072_ = v___y_8063_;
                                                v___y_8073_ = v___y_8064_;
                                                v___y_8074_ = v___y_8065_;
                                                v___y_8075_ = v___y_8066_;
                                                state = 1;
                                                continue;
                                            } else {
                                                lean_dec_ref(v___x_8082_);
                                                v___x_8145_ = l_Lean_Elab_ConfigEval_evalBoolItem(
                                                    v_item_8060_,
                                                    v___y_8061_,
                                                    v___y_8062_,
                                                    v___y_8063_,
                                                    v___y_8064_,
                                                    v___y_8065_,
                                                    v___y_8066_,
                                                );
                                                if lean_obj_tag(v___x_8145_) == 0 {
                                                    v_a_8146_ = lean_ctor_get(v___x_8145_, 0);
                                                    v_isSharedCheck_8164_ =
                                                        (!lean_is_exclusive(v___x_8145_)) as u8;
                                                    if v_isSharedCheck_8164_ == 0 {
                                                        v___x_8148_ = v___x_8145_;
                                                        v_isShared_8149_ = v_isSharedCheck_8164_;
                                                        state = 12;
                                                        continue;
                                                    } else {
                                                        lean_inc(v_a_8146_);
                                                        lean_dec(v___x_8145_);
                                                        v___x_8148_ = lean_box(0);
                                                        v_isShared_8149_ = v_isSharedCheck_8164_;
                                                        state = 12;
                                                        continue;
                                                    }
                                                } else {
                                                    lean_dec_ref(v_config_8059_);
                                                    v_a_8165_ = lean_ctor_get(v___x_8145_, 0);
                                                    v_isSharedCheck_8172_ =
                                                        (!lean_is_exclusive(v___x_8145_)) as u8;
                                                    if v_isSharedCheck_8172_ == 0 {
                                                        v___x_8167_ = v___x_8145_;
                                                        v_isShared_8168_ = v_isSharedCheck_8172_;
                                                        state = 16;
                                                        continue;
                                                    } else {
                                                        lean_inc(v_a_8165_);
                                                        lean_dec(v___x_8145_);
                                                        v___x_8167_ = lean_box(0);
                                                        v_isShared_8168_ = v_isSharedCheck_8172_;
                                                        state = 16;
                                                        continue;
                                                    }
                                                }
                                            }
                                        } else {
                                            lean_dec_ref(v___x_8082_);
                                            lean_dec_ref(v_item_8060_);
                                            lean_dec_ref(v_config_8059_);
                                            v_a_8173_ = lean_ctor_get(v___x_8143_, 0);
                                            v_isSharedCheck_8180_ =
                                                (!lean_is_exclusive(v___x_8143_)) as u8;
                                            if v_isSharedCheck_8180_ == 0 {
                                                v___x_8175_ = v___x_8143_;
                                                v_isShared_8176_ = v_isSharedCheck_8180_;
                                                state = 18;
                                                continue;
                                            } else {
                                                lean_inc(v_a_8173_);
                                                lean_dec(v___x_8143_);
                                                v___x_8175_ = lean_box(0);
                                                v_isShared_8176_ = v_isSharedCheck_8180_;
                                                state = 18;
                                                continue;
                                            }
                                        }
                                    }
                                } else {
                                    lean_dec_ref(v___x_8081_);
                                    v___x_8181_ = l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem___lam__0___closed__8;
                                    v___x_8182_ = l_Lean_Elab_ConfigEval_ConfigItem_addConstInfo(
                                        v_item_8060_,
                                        v___x_8181_,
                                        v___y_8061_,
                                        v___y_8062_,
                                        v___y_8063_,
                                        v___y_8064_,
                                        v___y_8065_,
                                        v___y_8066_,
                                    );
                                    if lean_obj_tag(v___x_8182_) == 0 {
                                        lean_dec_ref_known(v___x_8182_, 1);
                                        v___x_8183_ = l_Lean_Elab_ConfigEval_ConfigItem_isAnonymous(
                                            v___x_8082_,
                                        );
                                        if v___x_8183_ == 0 {
                                            lean_dec_ref(v_item_8060_);
                                            lean_dec_ref(v_config_8059_);
                                            v_item_8069_ = v___x_8082_;
                                            v___y_8070_ = v___y_8061_;
                                            v___y_8071_ = v___y_8062_;
                                            v___y_8072_ = v___y_8063_;
                                            v___y_8073_ = v___y_8064_;
                                            v___y_8074_ = v___y_8065_;
                                            v___y_8075_ = v___y_8066_;
                                            state = 1;
                                            continue;
                                        } else {
                                            lean_dec_ref(v___x_8082_);
                                            lean_inc_ref(v_item_8060_);
                                            v___x_8184_ =
                                                l_Lean_Elab_ConfigEval_ConfigItem_checkNotBool(
                                                    v_item_8060_,
                                                    v___y_8061_,
                                                    v___y_8062_,
                                                    v___y_8063_,
                                                    v___y_8064_,
                                                    v___y_8065_,
                                                    v___y_8066_,
                                                );
                                            if lean_obj_tag(v___x_8184_) == 0 {
                                                lean_dec_ref_known(v___x_8184_, 1);
                                                v_value_8185_ = lean_ctor_get(v_item_8060_, 2);
                                                lean_inc(v_value_8185_);
                                                lean_dec_ref(v_item_8060_);
                                                v___x_8186_ = l_Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__1(v_value_8185_, v___y_8061_, v___y_8062_, v___y_8063_, v___y_8064_, v___y_8065_, v___y_8066_);
                                                if lean_obj_tag(v___x_8186_) == 0 {
                                                    v_a_8187_ = lean_ctor_get(v___x_8186_, 0);
                                                    v_isSharedCheck_8205_ =
                                                        (!lean_is_exclusive(v___x_8186_)) as u8;
                                                    if v_isSharedCheck_8205_ == 0 {
                                                        v___x_8189_ = v___x_8186_;
                                                        v_isShared_8190_ = v_isSharedCheck_8205_;
                                                        state = 20;
                                                        continue;
                                                    } else {
                                                        lean_inc(v_a_8187_);
                                                        lean_dec(v___x_8186_);
                                                        v___x_8189_ = lean_box(0);
                                                        v_isShared_8190_ = v_isSharedCheck_8205_;
                                                        state = 20;
                                                        continue;
                                                    }
                                                } else {
                                                    lean_dec_ref(v_config_8059_);
                                                    v_a_8206_ = lean_ctor_get(v___x_8186_, 0);
                                                    v_isSharedCheck_8213_ =
                                                        (!lean_is_exclusive(v___x_8186_)) as u8;
                                                    if v_isSharedCheck_8213_ == 0 {
                                                        v___x_8208_ = v___x_8186_;
                                                        v_isShared_8209_ = v_isSharedCheck_8213_;
                                                        state = 24;
                                                        continue;
                                                    } else {
                                                        lean_inc(v_a_8206_);
                                                        lean_dec(v___x_8186_);
                                                        v___x_8208_ = lean_box(0);
                                                        v_isShared_8209_ = v_isSharedCheck_8213_;
                                                        state = 24;
                                                        continue;
                                                    }
                                                }
                                            } else {
                                                lean_dec_ref(v_item_8060_);
                                                lean_dec_ref(v_config_8059_);
                                                v_a_8214_ = lean_ctor_get(v___x_8184_, 0);
                                                v_isSharedCheck_8221_ =
                                                    (!lean_is_exclusive(v___x_8184_)) as u8;
                                                if v_isSharedCheck_8221_ == 0 {
                                                    v___x_8216_ = v___x_8184_;
                                                    v_isShared_8217_ = v_isSharedCheck_8221_;
                                                    state = 26;
                                                    continue;
                                                } else {
                                                    lean_inc(v_a_8214_);
                                                    lean_dec(v___x_8184_);
                                                    v___x_8216_ = lean_box(0);
                                                    v_isShared_8217_ = v_isSharedCheck_8221_;
                                                    state = 26;
                                                    continue;
                                                }
                                            }
                                        }
                                    } else {
                                        lean_dec_ref(v___x_8082_);
                                        lean_dec_ref(v_item_8060_);
                                        lean_dec_ref(v_config_8059_);
                                        v_a_8222_ = lean_ctor_get(v___x_8182_, 0);
                                        v_isSharedCheck_8229_ =
                                            (!lean_is_exclusive(v___x_8182_)) as u8;
                                        if v_isSharedCheck_8229_ == 0 {
                                            v___x_8224_ = v___x_8182_;
                                            v_isShared_8225_ = v_isSharedCheck_8229_;
                                            state = 28;
                                            continue;
                                        } else {
                                            lean_inc(v_a_8222_);
                                            lean_dec(v___x_8182_);
                                            v___x_8224_ = lean_box(0);
                                            v_isShared_8225_ = v_isSharedCheck_8229_;
                                            state = 28;
                                            continue;
                                        }
                                    }
                                }
                            } else {
                                lean_dec_ref(v___x_8081_);
                                v___x_8230_ = l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem___lam__0___closed__9;
                                v___x_8231_ = l_Lean_Elab_ConfigEval_ConfigItem_addConstInfo(
                                    v_item_8060_,
                                    v___x_8230_,
                                    v___y_8061_,
                                    v___y_8062_,
                                    v___y_8063_,
                                    v___y_8064_,
                                    v___y_8065_,
                                    v___y_8066_,
                                );
                                if lean_obj_tag(v___x_8231_) == 0 {
                                    lean_dec_ref_known(v___x_8231_, 1);
                                    v___x_8232_ =
                                        l_Lean_Elab_ConfigEval_ConfigItem_isAnonymous(v___x_8082_);
                                    if v___x_8232_ == 0 {
                                        lean_dec_ref(v_item_8060_);
                                        lean_dec_ref(v_config_8059_);
                                        v_item_8069_ = v___x_8082_;
                                        v___y_8070_ = v___y_8061_;
                                        v___y_8071_ = v___y_8062_;
                                        v___y_8072_ = v___y_8063_;
                                        v___y_8073_ = v___y_8064_;
                                        v___y_8074_ = v___y_8065_;
                                        v___y_8075_ = v___y_8066_;
                                        state = 1;
                                        continue;
                                    } else {
                                        lean_dec_ref(v___x_8082_);
                                        lean_inc_ref(v_item_8060_);
                                        v___x_8233_ =
                                            l_Lean_Elab_ConfigEval_ConfigItem_checkNotBool(
                                                v_item_8060_,
                                                v___y_8061_,
                                                v___y_8062_,
                                                v___y_8063_,
                                                v___y_8064_,
                                                v___y_8065_,
                                                v___y_8066_,
                                            );
                                        if lean_obj_tag(v___x_8233_) == 0 {
                                            lean_dec_ref_known(v___x_8233_, 1);
                                            v_value_8234_ = lean_ctor_get(v_item_8060_, 2);
                                            lean_inc(v_value_8234_);
                                            lean_dec_ref(v_item_8060_);
                                            v___x_8235_ = l_Lean_Elab_ConfigEval_evalTermOrExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__2(v_value_8234_, v___y_8061_, v___y_8062_, v___y_8063_, v___y_8064_, v___y_8065_, v___y_8066_);
                                            if lean_obj_tag(v___x_8235_) == 0 {
                                                v_a_8236_ = lean_ctor_get(v___x_8235_, 0);
                                                v_isSharedCheck_8254_ =
                                                    (!lean_is_exclusive(v___x_8235_)) as u8;
                                                if v_isSharedCheck_8254_ == 0 {
                                                    v___x_8238_ = v___x_8235_;
                                                    v_isShared_8239_ = v_isSharedCheck_8254_;
                                                    state = 30;
                                                    continue;
                                                } else {
                                                    lean_inc(v_a_8236_);
                                                    lean_dec(v___x_8235_);
                                                    v___x_8238_ = lean_box(0);
                                                    v_isShared_8239_ = v_isSharedCheck_8254_;
                                                    state = 30;
                                                    continue;
                                                }
                                            } else {
                                                lean_dec_ref(v_config_8059_);
                                                v_a_8255_ = lean_ctor_get(v___x_8235_, 0);
                                                v_isSharedCheck_8262_ =
                                                    (!lean_is_exclusive(v___x_8235_)) as u8;
                                                if v_isSharedCheck_8262_ == 0 {
                                                    v___x_8257_ = v___x_8235_;
                                                    v_isShared_8258_ = v_isSharedCheck_8262_;
                                                    state = 34;
                                                    continue;
                                                } else {
                                                    lean_inc(v_a_8255_);
                                                    lean_dec(v___x_8235_);
                                                    v___x_8257_ = lean_box(0);
                                                    v_isShared_8258_ = v_isSharedCheck_8262_;
                                                    state = 34;
                                                    continue;
                                                }
                                            }
                                        } else {
                                            lean_dec_ref(v_item_8060_);
                                            lean_dec_ref(v_config_8059_);
                                            v_a_8263_ = lean_ctor_get(v___x_8233_, 0);
                                            v_isSharedCheck_8270_ =
                                                (!lean_is_exclusive(v___x_8233_)) as u8;
                                            if v_isSharedCheck_8270_ == 0 {
                                                v___x_8265_ = v___x_8233_;
                                                v_isShared_8266_ = v_isSharedCheck_8270_;
                                                state = 36;
                                                continue;
                                            } else {
                                                lean_inc(v_a_8263_);
                                                lean_dec(v___x_8233_);
                                                v___x_8265_ = lean_box(0);
                                                v_isShared_8266_ = v_isSharedCheck_8270_;
                                                state = 36;
                                                continue;
                                            }
                                        }
                                    }
                                } else {
                                    lean_dec_ref(v___x_8082_);
                                    lean_dec_ref(v_item_8060_);
                                    lean_dec_ref(v_config_8059_);
                                    v_a_8271_ = lean_ctor_get(v___x_8231_, 0);
                                    v_isSharedCheck_8278_ = (!lean_is_exclusive(v___x_8231_)) as u8;
                                    if v_isSharedCheck_8278_ == 0 {
                                        v___x_8273_ = v___x_8231_;
                                        v_isShared_8274_ = v_isSharedCheck_8278_;
                                        state = 38;
                                        continue;
                                    } else {
                                        lean_inc(v_a_8271_);
                                        lean_dec(v___x_8231_);
                                        v___x_8273_ = lean_box(0);
                                        v_isShared_8274_ = v_isSharedCheck_8278_;
                                        state = 38;
                                        continue;
                                    }
                                }
                            }
                        } else {
                            lean_dec_ref(v___x_8081_);
                            lean_dec_ref(v_config_8059_);
                            v___x_8279_ =
                                l_Lean_Elab_ConfigEval_ConfigItem_isAnonymous(v___x_8082_);
                            if v___x_8279_ == 0 {
                                lean_dec_ref(v_item_8060_);
                                v_item_8069_ = v___x_8082_;
                                v___y_8070_ = v___y_8061_;
                                v___y_8071_ = v___y_8062_;
                                v___y_8072_ = v___y_8063_;
                                v___y_8073_ = v___y_8064_;
                                v___y_8074_ = v___y_8065_;
                                v___y_8075_ = v___y_8066_;
                                state = 1;
                                continue;
                            } else {
                                lean_dec_ref(v___x_8082_);
                                v_value_8280_ = lean_ctor_get(v_item_8060_, 2);
                                lean_inc(v_value_8280_);
                                lean_dec_ref(v_item_8060_);
                                v___x_8281_ = l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3(v_value_8280_, v___y_8061_, v___y_8062_, v___y_8063_, v___y_8064_, v___y_8065_, v___y_8066_);
                                return v___x_8281_;
                            }
                        }
                    } else {
                        lean_dec_ref(v_config_8059_);
                        v_item_8069_ = v_item_8060_;
                        v___y_8070_ = v___y_8061_;
                        v___y_8071_ = v___y_8062_;
                        v___y_8072_ = v___y_8063_;
                        v___y_8073_ = v___y_8064_;
                        v___y_8074_ = v___y_8065_;
                        v___y_8075_ = v___y_8066_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec_ref(v_item_8060_);
                    lean_dec_ref(v_config_8059_);
                    v_a_8282_ = lean_ctor_get(v___x_8079_, 0);
                    v_isSharedCheck_8289_ = (!lean_is_exclusive(v___x_8079_)) as u8;
                    if v_isSharedCheck_8289_ == 0 {
                        v___x_8284_ = v___x_8079_;
                        v_isShared_8285_ = v_isSharedCheck_8289_;
                        state = 40;
                        continue;
                    } else {
                        lean_inc(v_a_8282_);
                        lean_dec(v___x_8079_);
                        v___x_8284_ = lean_box(0);
                        v_isShared_8285_ = v_isSharedCheck_8289_;
                        state = 40;
                        continue;
                    }
                }
            }
            1 => {
                v___x_8076_ = l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem___lam__0___closed__0;
                v___x_8077_ = l_Lean_Elab_ConfigEval_ConfigItem_throwInvalidOption___redArg(
                    v_item_8069_,
                    v___x_8076_,
                    v___y_8070_,
                    v___y_8071_,
                    v___y_8072_,
                    v___y_8073_,
                    v___y_8074_,
                    v___y_8075_,
                );
                return v___x_8077_;
            }
            2 => {
                v_offsetCnstrs_8103_ = lean_ctor_get_uint8(
                    v_config_8059_,
                    (core::mem::size_of::<*mut LeanObject>() * 1 + 1) as u32,
                );
                v_occs_8104_ = lean_ctor_get(v_config_8059_, 0);
                v_newGoals_8105_ = lean_ctor_get_uint8(
                    v_config_8059_,
                    (core::mem::size_of::<*mut LeanObject>() * 1 + 2) as u32,
                );
                v_isSharedCheck_8116_ = (!lean_is_exclusive(v_config_8059_)) as u8;
                if v_isSharedCheck_8116_ == 0 {
                    v___x_8107_ = v_config_8059_;
                    v_isShared_8108_ = v_isSharedCheck_8116_;
                    state = 3;
                    continue;
                } else {
                    lean_inc(v_occs_8104_);
                    lean_dec(v_config_8059_);
                    v___x_8107_ = lean_box(0);
                    v_isShared_8108_ = v_isSharedCheck_8116_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_8108_ == 0 {
                    v___x_8110_ = v___x_8107_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_8115_ = lean_alloc_ctor(0, 1, (3) as u32);
                    lean_ctor_set(v_reuseFailAlloc_8115_, 0, v_occs_8104_);
                    v___x_8110_ = v_reuseFailAlloc_8115_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_8111_ = (lean_unbox(v_a_8099_) as u8);
                lean_dec(v_a_8099_);
                lean_ctor_set_uint8(
                    v___x_8110_,
                    (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                    v___x_8111_,
                );
                lean_ctor_set_uint8(
                    v___x_8110_,
                    (core::mem::size_of::<*mut LeanObject>() * 1 + 1) as u32,
                    v_offsetCnstrs_8103_,
                );
                lean_ctor_set_uint8(
                    v___x_8110_,
                    (core::mem::size_of::<*mut LeanObject>() * 1 + 2) as u32,
                    v_newGoals_8105_,
                );
                if v_isShared_8102_ == 0 {
                    lean_ctor_set(v___x_8101_, 0, v___x_8110_);
                    v___x_8113_ = v___x_8101_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_8114_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_8114_, 0, v___x_8110_);
                    v___x_8113_ = v_reuseFailAlloc_8114_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_8113_;
            }
            6 => {
                if v_isShared_8121_ == 0 {
                    v___x_8123_ = v___x_8120_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_8124_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_8124_, 0, v_a_8118_);
                    v___x_8123_ = v_reuseFailAlloc_8124_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_8123_;
            }
            8 => {
                if v_isShared_8129_ == 0 {
                    v___x_8131_ = v___x_8128_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_8132_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_8132_, 0, v_a_8126_);
                    v___x_8131_ = v_reuseFailAlloc_8132_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_8131_;
            }
            10 => {
                if v_isShared_8137_ == 0 {
                    v___x_8139_ = v___x_8136_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_8140_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_8140_, 0, v_a_8134_);
                    v___x_8139_ = v_reuseFailAlloc_8140_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                return v___x_8139_;
            }
            12 => {
                v_transparency_8150_ = lean_ctor_get_uint8(
                    v_config_8059_,
                    (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                );
                v_occs_8151_ = lean_ctor_get(v_config_8059_, 0);
                v_newGoals_8152_ = lean_ctor_get_uint8(
                    v_config_8059_,
                    (core::mem::size_of::<*mut LeanObject>() * 1 + 2) as u32,
                );
                v_isSharedCheck_8163_ = (!lean_is_exclusive(v_config_8059_)) as u8;
                if v_isSharedCheck_8163_ == 0 {
                    v___x_8154_ = v_config_8059_;
                    v_isShared_8155_ = v_isSharedCheck_8163_;
                    state = 13;
                    continue;
                } else {
                    lean_inc(v_occs_8151_);
                    lean_dec(v_config_8059_);
                    v___x_8154_ = lean_box(0);
                    v_isShared_8155_ = v_isSharedCheck_8163_;
                    state = 13;
                    continue;
                }
            }
            13 => {
                if v_isShared_8155_ == 0 {
                    v___x_8157_ = v___x_8154_;
                    state = 14;
                    continue;
                } else {
                    v_reuseFailAlloc_8162_ = lean_alloc_ctor(0, 1, (3) as u32);
                    lean_ctor_set(v_reuseFailAlloc_8162_, 0, v_occs_8151_);
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_8162_,
                        (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                        v_transparency_8150_,
                    );
                    v___x_8157_ = v_reuseFailAlloc_8162_;
                    state = 14;
                    continue;
                }
            }
            14 => {
                v___x_8158_ = (lean_unbox(v_a_8146_) as u8);
                lean_dec(v_a_8146_);
                lean_ctor_set_uint8(
                    v___x_8157_,
                    (core::mem::size_of::<*mut LeanObject>() * 1 + 1) as u32,
                    v___x_8158_,
                );
                lean_ctor_set_uint8(
                    v___x_8157_,
                    (core::mem::size_of::<*mut LeanObject>() * 1 + 2) as u32,
                    v_newGoals_8152_,
                );
                if v_isShared_8149_ == 0 {
                    lean_ctor_set(v___x_8148_, 0, v___x_8157_);
                    v___x_8160_ = v___x_8148_;
                    state = 15;
                    continue;
                } else {
                    v_reuseFailAlloc_8161_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_8161_, 0, v___x_8157_);
                    v___x_8160_ = v_reuseFailAlloc_8161_;
                    state = 15;
                    continue;
                }
            }
            15 => {
                return v___x_8160_;
            }
            16 => {
                if v_isShared_8168_ == 0 {
                    v___x_8170_ = v___x_8167_;
                    state = 17;
                    continue;
                } else {
                    v_reuseFailAlloc_8171_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_8171_, 0, v_a_8165_);
                    v___x_8170_ = v_reuseFailAlloc_8171_;
                    state = 17;
                    continue;
                }
            }
            17 => {
                return v___x_8170_;
            }
            18 => {
                if v_isShared_8176_ == 0 {
                    v___x_8178_ = v___x_8175_;
                    state = 19;
                    continue;
                } else {
                    v_reuseFailAlloc_8179_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_8179_, 0, v_a_8173_);
                    v___x_8178_ = v_reuseFailAlloc_8179_;
                    state = 19;
                    continue;
                }
            }
            19 => {
                return v___x_8178_;
            }
            20 => {
                v_transparency_8191_ = lean_ctor_get_uint8(
                    v_config_8059_,
                    (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                );
                v_offsetCnstrs_8192_ = lean_ctor_get_uint8(
                    v_config_8059_,
                    (core::mem::size_of::<*mut LeanObject>() * 1 + 1) as u32,
                );
                v_newGoals_8193_ = lean_ctor_get_uint8(
                    v_config_8059_,
                    (core::mem::size_of::<*mut LeanObject>() * 1 + 2) as u32,
                );
                v_isSharedCheck_8203_ = (!lean_is_exclusive(v_config_8059_)) as u8;
                if v_isSharedCheck_8203_ == 0 {
                    v_unused_8204_ = lean_ctor_get(v_config_8059_, 0);
                    lean_dec(v_unused_8204_);
                    v___x_8195_ = v_config_8059_;
                    v_isShared_8196_ = v_isSharedCheck_8203_;
                    state = 21;
                    continue;
                } else {
                    lean_dec(v_config_8059_);
                    v___x_8195_ = lean_box(0);
                    v_isShared_8196_ = v_isSharedCheck_8203_;
                    state = 21;
                    continue;
                }
            }
            21 => {
                if v_isShared_8196_ == 0 {
                    lean_ctor_set(v___x_8195_, 0, v_a_8187_);
                    v___x_8198_ = v___x_8195_;
                    state = 22;
                    continue;
                } else {
                    v_reuseFailAlloc_8202_ = lean_alloc_ctor(0, 1, (3) as u32);
                    lean_ctor_set(v_reuseFailAlloc_8202_, 0, v_a_8187_);
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_8202_,
                        (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                        v_transparency_8191_,
                    );
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_8202_,
                        (core::mem::size_of::<*mut LeanObject>() * 1 + 1) as u32,
                        v_offsetCnstrs_8192_,
                    );
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_8202_,
                        (core::mem::size_of::<*mut LeanObject>() * 1 + 2) as u32,
                        v_newGoals_8193_,
                    );
                    v___x_8198_ = v_reuseFailAlloc_8202_;
                    state = 22;
                    continue;
                }
            }
            22 => {
                if v_isShared_8190_ == 0 {
                    lean_ctor_set(v___x_8189_, 0, v___x_8198_);
                    v___x_8200_ = v___x_8189_;
                    state = 23;
                    continue;
                } else {
                    v_reuseFailAlloc_8201_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_8201_, 0, v___x_8198_);
                    v___x_8200_ = v_reuseFailAlloc_8201_;
                    state = 23;
                    continue;
                }
            }
            23 => {
                return v___x_8200_;
            }
            24 => {
                if v_isShared_8209_ == 0 {
                    v___x_8211_ = v___x_8208_;
                    state = 25;
                    continue;
                } else {
                    v_reuseFailAlloc_8212_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_8212_, 0, v_a_8206_);
                    v___x_8211_ = v_reuseFailAlloc_8212_;
                    state = 25;
                    continue;
                }
            }
            25 => {
                return v___x_8211_;
            }
            26 => {
                if v_isShared_8217_ == 0 {
                    v___x_8219_ = v___x_8216_;
                    state = 27;
                    continue;
                } else {
                    v_reuseFailAlloc_8220_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_8220_, 0, v_a_8214_);
                    v___x_8219_ = v_reuseFailAlloc_8220_;
                    state = 27;
                    continue;
                }
            }
            27 => {
                return v___x_8219_;
            }
            28 => {
                if v_isShared_8225_ == 0 {
                    v___x_8227_ = v___x_8224_;
                    state = 29;
                    continue;
                } else {
                    v_reuseFailAlloc_8228_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_8228_, 0, v_a_8222_);
                    v___x_8227_ = v_reuseFailAlloc_8228_;
                    state = 29;
                    continue;
                }
            }
            29 => {
                return v___x_8227_;
            }
            30 => {
                v_transparency_8240_ = lean_ctor_get_uint8(
                    v_config_8059_,
                    (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                );
                v_offsetCnstrs_8241_ = lean_ctor_get_uint8(
                    v_config_8059_,
                    (core::mem::size_of::<*mut LeanObject>() * 1 + 1) as u32,
                );
                v_occs_8242_ = lean_ctor_get(v_config_8059_, 0);
                v_isSharedCheck_8253_ = (!lean_is_exclusive(v_config_8059_)) as u8;
                if v_isSharedCheck_8253_ == 0 {
                    v___x_8244_ = v_config_8059_;
                    v_isShared_8245_ = v_isSharedCheck_8253_;
                    state = 31;
                    continue;
                } else {
                    lean_inc(v_occs_8242_);
                    lean_dec(v_config_8059_);
                    v___x_8244_ = lean_box(0);
                    v_isShared_8245_ = v_isSharedCheck_8253_;
                    state = 31;
                    continue;
                }
            }
            31 => {
                if v_isShared_8245_ == 0 {
                    v___x_8247_ = v___x_8244_;
                    state = 32;
                    continue;
                } else {
                    v_reuseFailAlloc_8252_ = lean_alloc_ctor(0, 1, (3) as u32);
                    lean_ctor_set(v_reuseFailAlloc_8252_, 0, v_occs_8242_);
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_8252_,
                        (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                        v_transparency_8240_,
                    );
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_8252_,
                        (core::mem::size_of::<*mut LeanObject>() * 1 + 1) as u32,
                        v_offsetCnstrs_8241_,
                    );
                    v___x_8247_ = v_reuseFailAlloc_8252_;
                    state = 32;
                    continue;
                }
            }
            32 => {
                v___x_8248_ = (lean_unbox(v_a_8236_) as u8);
                lean_dec(v_a_8236_);
                lean_ctor_set_uint8(
                    v___x_8247_,
                    (core::mem::size_of::<*mut LeanObject>() * 1 + 2) as u32,
                    v___x_8248_,
                );
                if v_isShared_8239_ == 0 {
                    lean_ctor_set(v___x_8238_, 0, v___x_8247_);
                    v___x_8250_ = v___x_8238_;
                    state = 33;
                    continue;
                } else {
                    v_reuseFailAlloc_8251_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_8251_, 0, v___x_8247_);
                    v___x_8250_ = v_reuseFailAlloc_8251_;
                    state = 33;
                    continue;
                }
            }
            33 => {
                return v___x_8250_;
            }
            34 => {
                if v_isShared_8258_ == 0 {
                    v___x_8260_ = v___x_8257_;
                    state = 35;
                    continue;
                } else {
                    v_reuseFailAlloc_8261_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_8261_, 0, v_a_8255_);
                    v___x_8260_ = v_reuseFailAlloc_8261_;
                    state = 35;
                    continue;
                }
            }
            35 => {
                return v___x_8260_;
            }
            36 => {
                if v_isShared_8266_ == 0 {
                    v___x_8268_ = v___x_8265_;
                    state = 37;
                    continue;
                } else {
                    v_reuseFailAlloc_8269_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_8269_, 0, v_a_8263_);
                    v___x_8268_ = v_reuseFailAlloc_8269_;
                    state = 37;
                    continue;
                }
            }
            37 => {
                return v___x_8268_;
            }
            38 => {
                if v_isShared_8274_ == 0 {
                    v___x_8276_ = v___x_8273_;
                    state = 39;
                    continue;
                } else {
                    v_reuseFailAlloc_8277_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_8277_, 0, v_a_8271_);
                    v___x_8276_ = v_reuseFailAlloc_8277_;
                    state = 39;
                    continue;
                }
            }
            39 => {
                return v___x_8276_;
            }
            40 => {
                if v_isShared_8285_ == 0 {
                    v___x_8287_ = v___x_8284_;
                    state = 41;
                    continue;
                } else {
                    v_reuseFailAlloc_8288_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_8288_, 0, v_a_8282_);
                    v___x_8287_ = v_reuseFailAlloc_8288_;
                    state = 41;
                    continue;
                }
            }
            41 => {
                return v___x_8287_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem___lam__0___boxed(
    mut v_config_8290_: *mut LeanObject,
    mut v_item_8291_: *mut LeanObject,
    mut v___y_8292_: *mut LeanObject,
    mut v___y_8293_: *mut LeanObject,
    mut v___y_8294_: *mut LeanObject,
    mut v___y_8295_: *mut LeanObject,
    mut v___y_8296_: *mut LeanObject,
    mut v___y_8297_: *mut LeanObject,
    mut v___y_8298_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_8299_: *mut LeanObject = core::ptr::null_mut();
    v_res_8299_ = l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem___lam__0(v_config_8290_, v_item_8291_, v___y_8292_, v___y_8293_, v___y_8294_, v___y_8295_, v___y_8296_, v___y_8297_);
    lean_dec(v___y_8297_);
    lean_dec_ref(v___y_8296_);
    lean_dec(v___y_8295_);
    lean_dec_ref(v___y_8294_);
    lean_dec(v___y_8293_);
    lean_dec_ref(v___y_8292_);
    return v_res_8299_;
}
pub unsafe fn l_Lean_instantiateMVars___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3_spec__6(
    mut v_e_8302_: *mut LeanObject,
    mut v___y_8303_: *mut LeanObject,
    mut v___y_8304_: *mut LeanObject,
    mut v___y_8305_: *mut LeanObject,
    mut v___y_8306_: *mut LeanObject,
    mut v___y_8307_: *mut LeanObject,
    mut v___y_8308_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_8310_: *mut LeanObject = core::ptr::null_mut();
    v___x_8310_ = l_Lean_instantiateMVars___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3_spec__6___redArg(v_e_8302_, v___y_8306_);
    return v___x_8310_;
}
pub unsafe fn l_Lean_instantiateMVars___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3_spec__6___boxed(
    mut v_e_8311_: *mut LeanObject,
    mut v___y_8312_: *mut LeanObject,
    mut v___y_8313_: *mut LeanObject,
    mut v___y_8314_: *mut LeanObject,
    mut v___y_8315_: *mut LeanObject,
    mut v___y_8316_: *mut LeanObject,
    mut v___y_8317_: *mut LeanObject,
    mut v___y_8318_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_8319_: *mut LeanObject = core::ptr::null_mut();
    v_res_8319_ = l_Lean_instantiateMVars___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3_spec__6(v_e_8311_, v___y_8312_, v___y_8313_, v___y_8314_, v___y_8315_, v___y_8316_, v___y_8317_);
    lean_dec(v___y_8317_);
    lean_dec_ref(v___y_8316_);
    lean_dec(v___y_8315_);
    lean_dec_ref(v___y_8314_);
    lean_dec(v___y_8313_);
    lean_dec_ref(v___y_8312_);
    return v_res_8319_;
}
pub unsafe fn l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3_spec__8(
    mut v_00_u03b1_8320_: *mut LeanObject,
    mut v___y_8321_: *mut LeanObject,
    mut v___y_8322_: *mut LeanObject,
    mut v___y_8323_: *mut LeanObject,
    mut v___y_8324_: *mut LeanObject,
    mut v___y_8325_: *mut LeanObject,
    mut v___y_8326_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_8328_: *mut LeanObject = core::ptr::null_mut();
    v___x_8328_ = l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3_spec__8___redArg();
    return v___x_8328_;
}
pub unsafe fn l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3_spec__8___boxed(
    mut v_00_u03b1_8329_: *mut LeanObject,
    mut v___y_8330_: *mut LeanObject,
    mut v___y_8331_: *mut LeanObject,
    mut v___y_8332_: *mut LeanObject,
    mut v___y_8333_: *mut LeanObject,
    mut v___y_8334_: *mut LeanObject,
    mut v___y_8335_: *mut LeanObject,
    mut v___y_8336_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_8337_: *mut LeanObject = core::ptr::null_mut();
    v_res_8337_ = l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3_spec__8(v_00_u03b1_8329_, v___y_8330_, v___y_8331_, v___y_8332_, v___y_8333_, v___y_8334_, v___y_8335_);
    lean_dec(v___y_8335_);
    lean_dec_ref(v___y_8334_);
    lean_dec(v___y_8333_);
    lean_dec_ref(v___y_8332_);
    lean_dec(v___y_8331_);
    lean_dec_ref(v___y_8330_);
    return v_res_8337_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3_spec__7(
    mut v_00_u03b1_8338_: *mut LeanObject,
    mut v_msg_8339_: *mut LeanObject,
    mut v___y_8340_: *mut LeanObject,
    mut v___y_8341_: *mut LeanObject,
    mut v___y_8342_: *mut LeanObject,
    mut v___y_8343_: *mut LeanObject,
    mut v___y_8344_: *mut LeanObject,
    mut v___y_8345_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_8347_: *mut LeanObject = core::ptr::null_mut();
    v___x_8347_ = l_Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3_spec__7___redArg(v_msg_8339_, v___y_8340_, v___y_8341_, v___y_8342_, v___y_8343_, v___y_8344_, v___y_8345_);
    return v___x_8347_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3_spec__7___boxed(
    mut v_00_u03b1_8348_: *mut LeanObject,
    mut v_msg_8349_: *mut LeanObject,
    mut v___y_8350_: *mut LeanObject,
    mut v___y_8351_: *mut LeanObject,
    mut v___y_8352_: *mut LeanObject,
    mut v___y_8353_: *mut LeanObject,
    mut v___y_8354_: *mut LeanObject,
    mut v___y_8355_: *mut LeanObject,
    mut v___y_8356_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_8357_: *mut LeanObject = core::ptr::null_mut();
    v_res_8357_ = l_Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3_spec__7(v_00_u03b1_8348_, v_msg_8349_, v___y_8350_, v___y_8351_, v___y_8352_, v___y_8353_, v___y_8354_, v___y_8355_);
    lean_dec(v___y_8355_);
    lean_dec_ref(v___y_8354_);
    lean_dec(v___y_8353_);
    lean_dec_ref(v___y_8352_);
    lean_dec(v___y_8351_);
    lean_dec_ref(v___y_8350_);
    return v_res_8357_;
}
pub unsafe fn l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3_spec__7_spec__8(
    mut v_msgData_8358_: *mut LeanObject,
    mut v_macroStack_8359_: *mut LeanObject,
    mut v___y_8360_: *mut LeanObject,
    mut v___y_8361_: *mut LeanObject,
    mut v___y_8362_: *mut LeanObject,
    mut v___y_8363_: *mut LeanObject,
    mut v___y_8364_: *mut LeanObject,
    mut v___y_8365_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_8367_: *mut LeanObject = core::ptr::null_mut();
    v___x_8367_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3_spec__7_spec__8___redArg(v_msgData_8358_, v_macroStack_8359_, v___y_8364_);
    return v___x_8367_;
}
pub unsafe fn l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3_spec__7_spec__8___boxed(
    mut v_msgData_8368_: *mut LeanObject,
    mut v_macroStack_8369_: *mut LeanObject,
    mut v___y_8370_: *mut LeanObject,
    mut v___y_8371_: *mut LeanObject,
    mut v___y_8372_: *mut LeanObject,
    mut v___y_8373_: *mut LeanObject,
    mut v___y_8374_: *mut LeanObject,
    mut v___y_8375_: *mut LeanObject,
    mut v___y_8376_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_8377_: *mut LeanObject = core::ptr::null_mut();
    v_res_8377_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem_spec__3_spec__7_spec__8(v_msgData_8368_, v_macroStack_8369_, v___y_8370_, v___y_8371_, v___y_8372_, v___y_8373_, v___y_8374_, v___y_8375_);
    lean_dec(v___y_8375_);
    lean_dec_ref(v___y_8374_);
    lean_dec(v___y_8373_);
    lean_dec_ref(v___y_8372_);
    lean_dec(v___y_8371_);
    lean_dec_ref(v___y_8370_);
    return v_res_8377_;
}
pub unsafe fn _init_l_Lean_Elab_Tactic_elabRewriteConfig___redArg___lam__0___closed__0()
-> *mut LeanObject {
    let mut v___x_8378_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8379_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8380_: *mut LeanObject = core::ptr::null_mut();
    v___x_8378_ = lean_box(0);
    v___x_8379_ = l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_instEvalExprConfig_evalExpr___closed__4;
    v___x_8380_ = l_Lean_mkConst(v___x_8379_, v___x_8378_);
    return v___x_8380_;
}
pub unsafe fn _init_l_Lean_Elab_Tactic_elabRewriteConfig___redArg___lam__0___closed__1()
-> *mut LeanObject {
    let mut v___x_8381_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8382_: *mut LeanObject = core::ptr::null_mut();
    v___x_8381_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_elabRewriteConfig___redArg___lam__0___closed__0),
        core::ptr::addr_of_mut!(
            l_Lean_Elab_Tactic_elabRewriteConfig___redArg___lam__0___closed__0_once
        ),
        _init_l_Lean_Elab_Tactic_elabRewriteConfig___redArg___lam__0___closed__0,
    );
    v___x_8382_ = lean_alloc_ctor(1, 1, (0) as u32);
    lean_ctor_set(v___x_8382_, 0, v___x_8381_);
    return v___x_8382_;
}
pub unsafe fn l_Lean_Elab_Tactic_elabRewriteConfig___redArg___lam__0(
    mut v_cfg_8383_: *mut LeanObject,
    mut v_cfgItem_8384_: *mut LeanObject,
    mut v___y_8385_: *mut LeanObject,
    mut v___y_8386_: *mut LeanObject,
    mut v___y_8387_: *mut LeanObject,
    mut v___y_8388_: *mut LeanObject,
    mut v___y_8389_: *mut LeanObject,
    mut v___y_8390_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_8392_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8393_: *mut LeanObject = core::ptr::null_mut();
    v___x_8392_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_elabRewriteConfig___redArg___lam__0___closed__1),
        core::ptr::addr_of_mut!(
            l_Lean_Elab_Tactic_elabRewriteConfig___redArg___lam__0___closed__1_once
        ),
        _init_l_Lean_Elab_Tactic_elabRewriteConfig___redArg___lam__0___closed__1,
    );
    v___x_8393_ = l_Lean_Elab_ConfigEval_EvalConfigItem_defaultOnErr___redArg(
        v_cfg_8383_,
        v_cfgItem_8384_,
        v___x_8392_,
        v___y_8385_,
        v___y_8386_,
        v___y_8387_,
        v___y_8388_,
        v___y_8389_,
        v___y_8390_,
    );
    return v___x_8393_;
}
pub unsafe fn l_Lean_Elab_Tactic_elabRewriteConfig___redArg___lam__0___boxed(
    mut v_cfg_8394_: *mut LeanObject,
    mut v_cfgItem_8395_: *mut LeanObject,
    mut v___y_8396_: *mut LeanObject,
    mut v___y_8397_: *mut LeanObject,
    mut v___y_8398_: *mut LeanObject,
    mut v___y_8399_: *mut LeanObject,
    mut v___y_8400_: *mut LeanObject,
    mut v___y_8401_: *mut LeanObject,
    mut v___y_8402_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_8403_: *mut LeanObject = core::ptr::null_mut();
    v_res_8403_ = l_Lean_Elab_Tactic_elabRewriteConfig___redArg___lam__0(
        v_cfg_8394_,
        v_cfgItem_8395_,
        v___y_8396_,
        v___y_8397_,
        v___y_8398_,
        v___y_8399_,
        v___y_8400_,
        v___y_8401_,
    );
    lean_dec(v___y_8401_);
    lean_dec_ref(v___y_8400_);
    lean_dec(v___y_8399_);
    lean_dec_ref(v___y_8398_);
    lean_dec(v___y_8397_);
    lean_dec_ref(v___y_8396_);
    lean_dec(v_cfgItem_8395_);
    return v_res_8403_;
}
pub unsafe fn l_Lean_Elab_Tactic_elabRewriteConfig___redArg(
    mut v_cfg_8405_: *mut LeanObject,
    mut v_init_8406_: *mut LeanObject,
    mut v_logExceptions_8407_: u8,
    mut v_a_8408_: *mut LeanObject,
    mut v_a_8409_: *mut LeanObject,
    mut v_a_8410_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_onErr_8412_: *mut LeanObject = core::ptr::null_mut();
    let mut v_eval_8413_: *mut LeanObject = core::ptr::null_mut();
    v_onErr_8412_ = l_Lean_Elab_Tactic_elabRewriteConfig___redArg___closed__0;
    v_eval_8413_ = l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_elabRewriteConfig_evalConfigItem___closed__0;
    if v_logExceptions_8407_ == 0 {
        let mut v___x_8414_: *mut LeanObject = core::ptr::null_mut();
        v___x_8414_ = l_Lean_Elab_ConfigEval_EvalConfigItem_setConfig_x27___redArg(
            v_eval_8413_,
            v_init_8406_,
            v_cfg_8405_,
            v_onErr_8412_,
            v_logExceptions_8407_,
            v_a_8409_,
            v_a_8410_,
        );
        return v___x_8414_;
    } else {
        let mut v_recover_8415_: u8 = 0;
        let mut v___x_8416_: *mut LeanObject = core::ptr::null_mut();
        v_recover_8415_ = lean_ctor_get_uint8(
            v_a_8408_,
            (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
        );
        v___x_8416_ = l_Lean_Elab_ConfigEval_EvalConfigItem_setConfig_x27___redArg(
            v_eval_8413_,
            v_init_8406_,
            v_cfg_8405_,
            v_onErr_8412_,
            v_recover_8415_,
            v_a_8409_,
            v_a_8410_,
        );
        return v___x_8416_;
    }
}
pub unsafe fn l_Lean_Elab_Tactic_elabRewriteConfig___redArg___boxed(
    mut v_cfg_8417_: *mut LeanObject,
    mut v_init_8418_: *mut LeanObject,
    mut v_logExceptions_8419_: *mut LeanObject,
    mut v_a_8420_: *mut LeanObject,
    mut v_a_8421_: *mut LeanObject,
    mut v_a_8422_: *mut LeanObject,
    mut v_a_8423_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_logExceptions_boxed_8424_: u8 = 0;
    let mut v_res_8425_: *mut LeanObject = core::ptr::null_mut();
    v_logExceptions_boxed_8424_ = (lean_unbox(v_logExceptions_8419_) as u8);
    v_res_8425_ = l_Lean_Elab_Tactic_elabRewriteConfig___redArg(
        v_cfg_8417_,
        v_init_8418_,
        v_logExceptions_boxed_8424_,
        v_a_8420_,
        v_a_8421_,
        v_a_8422_,
    );
    lean_dec(v_a_8422_);
    lean_dec_ref(v_a_8421_);
    lean_dec_ref(v_a_8420_);
    return v_res_8425_;
}
pub unsafe fn l_Lean_Elab_Tactic_elabRewriteConfig(
    mut v_cfg_8426_: *mut LeanObject,
    mut v_init_8427_: *mut LeanObject,
    mut v_logExceptions_8428_: u8,
    mut v_a_8429_: *mut LeanObject,
    mut v_a_8430_: *mut LeanObject,
    mut v_a_8431_: *mut LeanObject,
    mut v_a_8432_: *mut LeanObject,
    mut v_a_8433_: *mut LeanObject,
    mut v_a_8434_: *mut LeanObject,
    mut v_a_8435_: *mut LeanObject,
    mut v_a_8436_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_8438_: *mut LeanObject = core::ptr::null_mut();
    v___x_8438_ = l_Lean_Elab_Tactic_elabRewriteConfig___redArg(
        v_cfg_8426_,
        v_init_8427_,
        v_logExceptions_8428_,
        v_a_8429_,
        v_a_8435_,
        v_a_8436_,
    );
    return v___x_8438_;
}
pub unsafe fn l_Lean_Elab_Tactic_elabRewriteConfig___boxed(
    mut v_cfg_8439_: *mut LeanObject,
    mut v_init_8440_: *mut LeanObject,
    mut v_logExceptions_8441_: *mut LeanObject,
    mut v_a_8442_: *mut LeanObject,
    mut v_a_8443_: *mut LeanObject,
    mut v_a_8444_: *mut LeanObject,
    mut v_a_8445_: *mut LeanObject,
    mut v_a_8446_: *mut LeanObject,
    mut v_a_8447_: *mut LeanObject,
    mut v_a_8448_: *mut LeanObject,
    mut v_a_8449_: *mut LeanObject,
    mut v_a_8450_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_logExceptions_boxed_8451_: u8 = 0;
    let mut v_res_8452_: *mut LeanObject = core::ptr::null_mut();
    v_logExceptions_boxed_8451_ = (lean_unbox(v_logExceptions_8441_) as u8);
    v_res_8452_ = l_Lean_Elab_Tactic_elabRewriteConfig(
        v_cfg_8439_,
        v_init_8440_,
        v_logExceptions_boxed_8451_,
        v_a_8442_,
        v_a_8443_,
        v_a_8444_,
        v_a_8445_,
        v_a_8446_,
        v_a_8447_,
        v_a_8448_,
        v_a_8449_,
    );
    lean_dec(v_a_8449_);
    lean_dec_ref(v_a_8448_);
    lean_dec(v_a_8447_);
    lean_dec_ref(v_a_8446_);
    lean_dec(v_a_8445_);
    lean_dec_ref(v_a_8444_);
    lean_dec(v_a_8443_);
    lean_dec_ref(v_a_8442_);
    return v_res_8452_;
}
pub unsafe fn _init_l_Lean_Elab_Tactic_evalRewriteSeq___lam__0___closed__4() -> *mut LeanObject {
    let mut v___x_8459_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8460_: *mut LeanObject = core::ptr::null_mut();
    v___x_8459_ = l_Lean_Elab_Tactic_evalRewriteSeq___lam__0___closed__3;
    v___x_8460_ = l_Lean_MessageData_ofFormat(v___x_8459_);
    return v___x_8460_;
}
pub unsafe fn _init_l_Lean_Elab_Tactic_evalRewriteSeq___lam__0___closed__5() -> *mut LeanObject {
    let mut v___x_8461_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8462_: *mut LeanObject = core::ptr::null_mut();
    v___x_8461_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_evalRewriteSeq___lam__0___closed__4),
        core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_evalRewriteSeq___lam__0___closed__4_once),
        _init_l_Lean_Elab_Tactic_evalRewriteSeq___lam__0___closed__4,
    );
    v___x_8462_ = lean_alloc_ctor(1, 1, (0) as u32);
    lean_ctor_set(v___x_8462_, 0, v___x_8461_);
    return v___x_8462_;
}
pub unsafe fn l_Lean_Elab_Tactic_evalRewriteSeq___lam__0(
    mut v_x_8463_: *mut LeanObject,
    mut v___y_8464_: *mut LeanObject,
    mut v___y_8465_: *mut LeanObject,
    mut v___y_8466_: *mut LeanObject,
    mut v___y_8467_: *mut LeanObject,
    mut v___y_8468_: *mut LeanObject,
    mut v___y_8469_: *mut LeanObject,
    mut v___y_8470_: *mut LeanObject,
    mut v___y_8471_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_8473_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8474_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8475_: *mut LeanObject = core::ptr::null_mut();
    v___x_8473_ = l_Lean_Elab_Tactic_evalRewriteSeq___lam__0___closed__1;
    v___x_8474_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_evalRewriteSeq___lam__0___closed__5),
        core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_evalRewriteSeq___lam__0___closed__5_once),
        _init_l_Lean_Elab_Tactic_evalRewriteSeq___lam__0___closed__5,
    );
    v___x_8475_ = l_Lean_Meta_throwTacticEx___redArg(
        v___x_8473_,
        v_x_8463_,
        v___x_8474_,
        v___y_8468_,
        v___y_8469_,
        v___y_8470_,
        v___y_8471_,
    );
    return v___x_8475_;
}
pub unsafe fn l_Lean_Elab_Tactic_evalRewriteSeq___lam__0___boxed(
    mut v_x_8476_: *mut LeanObject,
    mut v___y_8477_: *mut LeanObject,
    mut v___y_8478_: *mut LeanObject,
    mut v___y_8479_: *mut LeanObject,
    mut v___y_8480_: *mut LeanObject,
    mut v___y_8481_: *mut LeanObject,
    mut v___y_8482_: *mut LeanObject,
    mut v___y_8483_: *mut LeanObject,
    mut v___y_8484_: *mut LeanObject,
    mut v___y_8485_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_8486_: *mut LeanObject = core::ptr::null_mut();
    v_res_8486_ = l_Lean_Elab_Tactic_evalRewriteSeq___lam__0(
        v_x_8476_,
        v___y_8477_,
        v___y_8478_,
        v___y_8479_,
        v___y_8480_,
        v___y_8481_,
        v___y_8482_,
        v___y_8483_,
        v___y_8484_,
    );
    lean_dec(v___y_8484_);
    lean_dec_ref(v___y_8483_);
    lean_dec(v___y_8482_);
    lean_dec_ref(v___y_8481_);
    lean_dec(v___y_8480_);
    lean_dec_ref(v___y_8479_);
    lean_dec(v___y_8478_);
    lean_dec_ref(v___y_8477_);
    return v_res_8486_;
}
pub unsafe fn l_Lean_Elab_Tactic_evalRewriteSeq___lam__1(
    mut v_term_8487_: *mut LeanObject,
    mut v_symm_8488_: u8,
    mut v_a_8489_: *mut LeanObject,
    mut v_x_8490_: *mut LeanObject,
    mut v___y_8491_: *mut LeanObject,
    mut v___y_8492_: *mut LeanObject,
    mut v___y_8493_: *mut LeanObject,
    mut v___y_8494_: *mut LeanObject,
    mut v___y_8495_: *mut LeanObject,
    mut v___y_8496_: *mut LeanObject,
    mut v___y_8497_: *mut LeanObject,
    mut v___y_8498_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_8500_: *mut LeanObject = core::ptr::null_mut();
    v___x_8500_ = l_Lean_Elab_Tactic_rewriteLocalDecl(
        v_term_8487_,
        v_symm_8488_,
        v_x_8490_,
        v_a_8489_,
        v___y_8491_,
        v___y_8492_,
        v___y_8493_,
        v___y_8494_,
        v___y_8495_,
        v___y_8496_,
        v___y_8497_,
        v___y_8498_,
    );
    return v___x_8500_;
}
pub unsafe fn l_Lean_Elab_Tactic_evalRewriteSeq___lam__1___boxed(
    mut v_term_8501_: *mut LeanObject,
    mut v_symm_8502_: *mut LeanObject,
    mut v_a_8503_: *mut LeanObject,
    mut v_x_8504_: *mut LeanObject,
    mut v___y_8505_: *mut LeanObject,
    mut v___y_8506_: *mut LeanObject,
    mut v___y_8507_: *mut LeanObject,
    mut v___y_8508_: *mut LeanObject,
    mut v___y_8509_: *mut LeanObject,
    mut v___y_8510_: *mut LeanObject,
    mut v___y_8511_: *mut LeanObject,
    mut v___y_8512_: *mut LeanObject,
    mut v___y_8513_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_symm_boxed_8514_: u8 = 0;
    let mut v_res_8515_: *mut LeanObject = core::ptr::null_mut();
    v_symm_boxed_8514_ = (lean_unbox(v_symm_8502_) as u8);
    v_res_8515_ = l_Lean_Elab_Tactic_evalRewriteSeq___lam__1(
        v_term_8501_,
        v_symm_boxed_8514_,
        v_a_8503_,
        v_x_8504_,
        v___y_8505_,
        v___y_8506_,
        v___y_8507_,
        v___y_8508_,
        v___y_8509_,
        v___y_8510_,
        v___y_8511_,
        v___y_8512_,
    );
    lean_dec(v___y_8512_);
    lean_dec_ref(v___y_8511_);
    lean_dec(v___y_8510_);
    lean_dec_ref(v___y_8509_);
    lean_dec(v___y_8508_);
    lean_dec_ref(v___y_8507_);
    lean_dec(v___y_8506_);
    lean_dec_ref(v___y_8505_);
    return v_res_8515_;
}
pub unsafe fn l_Lean_Elab_Tactic_evalRewriteSeq___lam__2(
    mut v_a_8516_: *mut LeanObject,
    mut v___x_8517_: *mut LeanObject,
    mut v___f_8518_: *mut LeanObject,
    mut v_symm_8519_: u8,
    mut v_term_8520_: *mut LeanObject,
    mut v___y_8521_: *mut LeanObject,
    mut v___y_8522_: *mut LeanObject,
    mut v___y_8523_: *mut LeanObject,
    mut v___y_8524_: *mut LeanObject,
    mut v___y_8525_: *mut LeanObject,
    mut v___y_8526_: *mut LeanObject,
    mut v___y_8527_: *mut LeanObject,
    mut v___y_8528_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_8530_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_8531_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8532_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8533_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8534_: *mut LeanObject = core::ptr::null_mut();
    v___x_8530_ = lean_box((v_symm_8519_) as usize);
    lean_inc_ref(v_a_8516_);
    lean_inc(v_term_8520_);
    v___f_8531_ = lean_alloc_closure(
        l_Lean_Elab_Tactic_evalRewriteSeq___lam__1___boxed as *mut core::ffi::c_void,
        13,
        3,
    );
    lean_closure_set(v___f_8531_, 0, v_term_8520_);
    lean_closure_set(v___f_8531_, 1, v___x_8530_);
    lean_closure_set(v___f_8531_, 2, v_a_8516_);
    v___x_8532_ = lean_box((v_symm_8519_) as usize);
    v___x_8533_ = lean_alloc_closure(
        l_Lean_Elab_Tactic_rewriteTarget___boxed as *mut core::ffi::c_void,
        12,
        3,
    );
    lean_closure_set(v___x_8533_, 0, v_term_8520_);
    lean_closure_set(v___x_8533_, 1, v___x_8532_);
    lean_closure_set(v___x_8533_, 2, v_a_8516_);
    v___x_8534_ = l_Lean_Elab_Tactic_withLocation(
        v___x_8517_,
        v___f_8531_,
        v___x_8533_,
        v___f_8518_,
        v___y_8521_,
        v___y_8522_,
        v___y_8523_,
        v___y_8524_,
        v___y_8525_,
        v___y_8526_,
        v___y_8527_,
        v___y_8528_,
    );
    return v___x_8534_;
}
pub unsafe fn l_Lean_Elab_Tactic_evalRewriteSeq___lam__2___boxed(
    mut v_a_8535_: *mut LeanObject,
    mut v___x_8536_: *mut LeanObject,
    mut v___f_8537_: *mut LeanObject,
    mut v_symm_8538_: *mut LeanObject,
    mut v_term_8539_: *mut LeanObject,
    mut v___y_8540_: *mut LeanObject,
    mut v___y_8541_: *mut LeanObject,
    mut v___y_8542_: *mut LeanObject,
    mut v___y_8543_: *mut LeanObject,
    mut v___y_8544_: *mut LeanObject,
    mut v___y_8545_: *mut LeanObject,
    mut v___y_8546_: *mut LeanObject,
    mut v___y_8547_: *mut LeanObject,
    mut v___y_8548_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_symm_boxed_8549_: u8 = 0;
    let mut v_res_8550_: *mut LeanObject = core::ptr::null_mut();
    v_symm_boxed_8549_ = (lean_unbox(v_symm_8538_) as u8);
    v_res_8550_ = l_Lean_Elab_Tactic_evalRewriteSeq___lam__2(
        v_a_8535_,
        v___x_8536_,
        v___f_8537_,
        v_symm_boxed_8549_,
        v_term_8539_,
        v___y_8540_,
        v___y_8541_,
        v___y_8542_,
        v___y_8543_,
        v___y_8544_,
        v___y_8545_,
        v___y_8546_,
        v___y_8547_,
    );
    lean_dec(v___y_8547_);
    lean_dec_ref(v___y_8546_);
    lean_dec(v___y_8545_);
    lean_dec_ref(v___y_8544_);
    lean_dec(v___y_8543_);
    lean_dec_ref(v___y_8542_);
    lean_dec(v___y_8541_);
    lean_dec_ref(v___y_8540_);
    lean_dec(v___x_8536_);
    return v_res_8550_;
}
pub unsafe fn l_Lean_Elab_Tactic_evalRewriteSeq(
    mut v_stx_8557_: *mut LeanObject,
    mut v_a_8558_: *mut LeanObject,
    mut v_a_8559_: *mut LeanObject,
    mut v_a_8560_: *mut LeanObject,
    mut v_a_8561_: *mut LeanObject,
    mut v_a_8562_: *mut LeanObject,
    mut v_a_8563_: *mut LeanObject,
    mut v_a_8564_: *mut LeanObject,
    mut v_a_8565_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_8567_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8568_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8569_: u8 = 0;
    let mut v___x_8570_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8571_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_8572_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_8573_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8574_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8575_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8576_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_8577_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8578_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8579_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8580_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8581_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8582_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_8583_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8585_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_8586_: u8 = 0;
    let mut v___x_8588_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8589_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_8590_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_8567_ = lean_unsigned_to_nat(1);
                v___x_8568_ = l_Lean_Syntax_getArg(v_stx_8557_, v___x_8567_);
                v___x_8569_ = 1;
                v___x_8570_ = l_Lean_Elab_Tactic_evalRewriteSeq___closed__0;
                v___x_8571_ = l_Lean_Elab_Tactic_elabRewriteConfig___redArg(
                    v___x_8568_,
                    v___x_8570_,
                    v___x_8569_,
                    v_a_8558_,
                    v_a_8564_,
                    v_a_8565_,
                );
                if lean_obj_tag(v___x_8571_) == 0 {
                    v_a_8572_ = lean_ctor_get(v___x_8571_, 0);
                    lean_inc(v_a_8572_);
                    lean_dec_ref_known(v___x_8571_, 1);
                    v___f_8573_ = l_Lean_Elab_Tactic_evalRewriteSeq___closed__1;
                    v___x_8574_ = lean_unsigned_to_nat(3);
                    v___x_8575_ = l_Lean_Syntax_getArg(v_stx_8557_, v___x_8574_);
                    v___x_8576_ = l_Lean_Elab_Tactic_expandOptLocation(v___x_8575_);
                    lean_dec(v___x_8575_);
                    v___f_8577_ = lean_alloc_closure(
                        l_Lean_Elab_Tactic_evalRewriteSeq___lam__2___boxed
                            as *mut core::ffi::c_void,
                        14,
                        3,
                    );
                    lean_closure_set(v___f_8577_, 0, v_a_8572_);
                    lean_closure_set(v___f_8577_, 1, v___x_8576_);
                    lean_closure_set(v___f_8577_, 2, v___f_8573_);
                    v___x_8578_ = lean_unsigned_to_nat(0);
                    v___x_8579_ = l_Lean_Syntax_getArg(v_stx_8557_, v___x_8578_);
                    v___x_8580_ = lean_unsigned_to_nat(2);
                    v___x_8581_ = l_Lean_Syntax_getArg(v_stx_8557_, v___x_8580_);
                    v___x_8582_ = l_Lean_Elab_Tactic_withRWRulesSeq(
                        v___x_8579_,
                        v___x_8581_,
                        v___f_8577_,
                        v_a_8558_,
                        v_a_8559_,
                        v_a_8560_,
                        v_a_8561_,
                        v_a_8562_,
                        v_a_8563_,
                        v_a_8564_,
                        v_a_8565_,
                    );
                    lean_dec(v___x_8581_);
                    return v___x_8582_;
                } else {
                    v_a_8583_ = lean_ctor_get(v___x_8571_, 0);
                    v_isSharedCheck_8590_ = (!lean_is_exclusive(v___x_8571_)) as u8;
                    if v_isSharedCheck_8590_ == 0 {
                        v___x_8585_ = v___x_8571_;
                        v_isShared_8586_ = v_isSharedCheck_8590_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_8583_);
                        lean_dec(v___x_8571_);
                        v___x_8585_ = lean_box(0);
                        v_isShared_8586_ = v_isSharedCheck_8590_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_8586_ == 0 {
                    v___x_8588_ = v___x_8585_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_8589_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_8589_, 0, v_a_8583_);
                    v___x_8588_ = v_reuseFailAlloc_8589_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_8588_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_Tactic_evalRewriteSeq___boxed(
    mut v_stx_8591_: *mut LeanObject,
    mut v_a_8592_: *mut LeanObject,
    mut v_a_8593_: *mut LeanObject,
    mut v_a_8594_: *mut LeanObject,
    mut v_a_8595_: *mut LeanObject,
    mut v_a_8596_: *mut LeanObject,
    mut v_a_8597_: *mut LeanObject,
    mut v_a_8598_: *mut LeanObject,
    mut v_a_8599_: *mut LeanObject,
    mut v_a_8600_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_8601_: *mut LeanObject = core::ptr::null_mut();
    v_res_8601_ = l_Lean_Elab_Tactic_evalRewriteSeq(
        v_stx_8591_,
        v_a_8592_,
        v_a_8593_,
        v_a_8594_,
        v_a_8595_,
        v_a_8596_,
        v_a_8597_,
        v_a_8598_,
        v_a_8599_,
    );
    lean_dec(v_a_8599_);
    lean_dec_ref(v_a_8598_);
    lean_dec(v_a_8597_);
    lean_dec_ref(v_a_8596_);
    lean_dec(v_a_8595_);
    lean_dec_ref(v_a_8594_);
    lean_dec(v_a_8593_);
    lean_dec_ref(v_a_8592_);
    lean_dec(v_stx_8591_);
    return v_res_8601_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_evalRewriteSeq___regBuiltin_Lean_Elab_Tactic_evalRewriteSeq__1()
-> *mut LeanObject {
    let mut v___x_8617_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8618_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8619_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8620_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8621_: *mut LeanObject = core::ptr::null_mut();
    v___x_8617_ = l_Lean_Elab_Tactic_tacticElabAttribute;
    v___x_8618_ = l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_evalRewriteSeq___regBuiltin_Lean_Elab_Tactic_evalRewriteSeq__1___closed__2;
    v___x_8619_ = l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_evalRewriteSeq___regBuiltin_Lean_Elab_Tactic_evalRewriteSeq__1___closed__5;
    v___x_8620_ = lean_alloc_closure(
        l_Lean_Elab_Tactic_evalRewriteSeq___boxed as *mut core::ffi::c_void,
        10,
        0,
    );
    v___x_8621_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(
        v___x_8617_,
        v___x_8618_,
        v___x_8619_,
        v___x_8620_,
    );
    return v___x_8621_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_evalRewriteSeq___regBuiltin_Lean_Elab_Tactic_evalRewriteSeq__1___boxed(
    mut v_a_8622_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_8623_: *mut LeanObject = core::ptr::null_mut();
    v_res_8623_ = l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_evalRewriteSeq___regBuiltin_Lean_Elab_Tactic_evalRewriteSeq__1();
    return v_res_8623_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_evalRewriteSeq___regBuiltin_Lean_Elab_Tactic_evalRewriteSeq_declRange__3()
-> *mut LeanObject {
    let mut v___x_8650_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8651_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_8652_: *mut LeanObject = core::ptr::null_mut();
    v___x_8650_ = l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_evalRewriteSeq___regBuiltin_Lean_Elab_Tactic_evalRewriteSeq__1___closed__5;
    v___x_8651_ = l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_evalRewriteSeq___regBuiltin_Lean_Elab_Tactic_evalRewriteSeq_declRange__3___closed__6;
    v___x_8652_ = l_Lean_addBuiltinDeclarationRanges(v___x_8650_, v___x_8651_);
    return v___x_8652_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_evalRewriteSeq___regBuiltin_Lean_Elab_Tactic_evalRewriteSeq_declRange__3___boxed(
    mut v_a_8653_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_8654_: *mut LeanObject = core::ptr::null_mut();
    v_res_8654_ = l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_evalRewriteSeq___regBuiltin_Lean_Elab_Tactic_evalRewriteSeq_declRange__3();
    return v_res_8654_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Elab_Tactic_Rewrite(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Meta_Tactic_Rewrite(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Replace(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_Tactic_Location(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_ConfigEval(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Eqns(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_instEvalExprConfig =
        _init_l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_instEvalExprConfig();
    lean_mark_persistent(
        l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_instEvalExprConfig,
    );
    res = l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_evalRewriteSeq___regBuiltin_Lean_Elab_Tactic_evalRewriteSeq__1();
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = l___private_Lean_Elab_Tactic_Rewrite_0__Lean_Elab_Tactic_evalRewriteSeq___regBuiltin_Lean_Elab_Tactic_evalRewriteSeq_declRange__3();
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Elab_Tactic_Rewrite(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Elab_Tactic_Rewrite(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Meta_Tactic_Rewrite(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Meta_Tactic_Replace(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Elab_Tactic_Location(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Elab_ConfigEval(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Meta_Eqns(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_Tactic_Rewrite(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Lean_Elab_Tactic_Rewrite(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Lean_Elab_Tactic_Rewrite(builtin);
}
