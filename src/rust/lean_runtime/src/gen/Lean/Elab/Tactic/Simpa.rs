// Lean compiler output
// Module: Lean.Elab.Tactic.Simpa
// Imports: Lean.Meta.Tactic.TryThis Lean.Elab.Tactic.Simp Lean.Elab.App
use crate::r#gen::Init::Data::Array::Basic::l_Array_append___redArg;
use crate::r#gen::Init::Meta::Defs::{
    l_Lean_Syntax_isNone, l_Lean_Syntax_unsetTrailing, lean_mk_syntax_ident,
};
use crate::r#gen::Init::Prelude::{
    l_Array_mkArray0, l_Array_mkArray1___redArg, l_Array_mkArray2___redArg,
    l_Array_mkArray3___redArg, l_Lean_Name_mkStr1, l_Lean_Name_mkStr4, l_Lean_SourceInfo_fromRef,
    l_Lean_Syntax_getArg, l_Lean_Syntax_getArgs, l_Lean_Syntax_getOptional_x3f,
    l_Lean_Syntax_getPos_x3f, l_Lean_Syntax_getTailPos_x3f, l_Lean_Syntax_isOfKind,
    l_Lean_Syntax_matchesNull, l_Lean_Syntax_node1, l_Lean_Syntax_node2, l_Lean_Syntax_node3,
    l_Lean_Syntax_node4, l_Lean_Syntax_node5, l_Lean_Syntax_node6, l_Lean_replaceRef,
};
use crate::r#gen::Init::Util::l_mkPanicMessageWithDecl;
use crate::r#gen::Lean::CoreM::l_Lean_Core_mkFreshUserName;
use crate::r#gen::Lean::Data::NameMap::Basic::l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg;
use crate::r#gen::Lean::Data::Options::lean_register_option;
use crate::r#gen::Lean::Data::PersistentArray::l_Lean_PersistentArray_push___redArg;
use crate::r#gen::Lean::Data::PersistentHashMap::{
    l_Lean_PersistentHashMap_getCollisionNodeSize___redArg,
    l_Lean_PersistentHashMap_mkCollisionNode___redArg, l_Lean_PersistentHashMap_mkEmptyEntries,
    l_Lean_PersistentHashMap_mkEmptyEntriesArray,
};
use crate::r#gen::Lean::Data::Position::l_Lean_FileMap_toPosition;
use crate::r#gen::Lean::DeclarationRange::l_Lean_addBuiltinDeclarationRanges;
use crate::r#gen::Lean::Elab::App::{initialize_Lean_Elab_App, runtime_initialize_Lean_Elab_App};
use crate::r#gen::Lean::Elab::Exception::l_Lean_Elab_unsupportedSyntaxExceptionId;
use crate::r#gen::Lean::Elab::SyntheticMVars::l_Lean_Elab_Term_synthesizeSyntheticMVarsNoPostponing;
use crate::r#gen::Lean::Elab::Tactic::Basic::{
    l_Lean_Elab_Tactic_closeMainGoal___redArg, l_Lean_Elab_Tactic_focus___redArg,
    l_Lean_Elab_Tactic_getMainGoal___redArg,
    l_Lean_Elab_Tactic_instInhabitedTacticM___lam__0___boxed,
    l_Lean_Elab_Tactic_mkInitialTacticInfo, l_Lean_Elab_Tactic_pushGoal___redArg,
    l_Lean_Elab_Tactic_replaceMainGoal___redArg, l_Lean_Elab_Tactic_tacticElabAttribute,
    l_Lean_Elab_Tactic_withMainContext___redArg,
};
use crate::r#gen::Lean::Elab::Tactic::ElabTerm::{
    l_Lean_Elab_Tactic_elabTerm, l_Lean_Elab_Tactic_filterOldMVars___redArg,
    l_Lean_Elab_Tactic_logUnassignedAndAbort,
};
use crate::r#gen::Lean::Elab::Tactic::Simp::{
    initialize_Lean_Elab_Tactic_Simp, l_Lean_Elab_Tactic_Simp_DischargeWrapper_with___redArg,
    l_Lean_Elab_Tactic_mkSimpContext___boxed, l_Lean_Elab_Tactic_mkSimpOnly,
    l_Lean_Elab_Tactic_tactic_simp_trace, l_Lean_Elab_Tactic_withSimpDiagnostics___boxed,
    runtime_initialize_Lean_Elab_Tactic_Simp,
};
use crate::r#gen::Lean::Elab::Term::TermElabM::{
    l_Lean_Elab_Term_elabTerm, l_Lean_Elab_Term_throwTypeMismatchError___redArg,
};
use crate::r#gen::Lean::EnvExtension::l_Lean_SimplePersistentEnvExtension_getState___redArg;
use crate::r#gen::Lean::Expr::{
    l_Lean_Expr_hasExprMVar, l_Lean_Expr_hash, l_Lean_Expr_mvar___override, l_Lean_Expr_mvarId_x21,
    l_Lean_instBEqMVarId_beq, l_Lean_instHashableMVarId_hash,
};
use crate::r#gen::Lean::KeyedDeclsAttribute::l_Lean_KeyedDeclsAttribute_addBuiltin___redArg;
use crate::r#gen::Lean::Linter::Init::{
    l_Lean_Linter_getLinterValue, l_Lean_Linter_linterMessageTag, l_Lean_Linter_linterSetsExt,
};
use crate::r#gen::Lean::LocalContext::{
    l_Lean_LocalContext_findFromUserName_x3f, l_Lean_LocalContext_getRoundtrippingUserName_x3f,
    l_Lean_LocalDecl_fvarId,
};
use crate::r#gen::Lean::Log::{
    l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed, l_Lean_warningAsError,
};
use crate::r#gen::Lean::Message::{
    l_Lean_MessageData_hasSyntheticSorry, l_Lean_MessageData_hasTag, l_Lean_MessageData_nil,
    l_Lean_MessageData_note, l_Lean_MessageData_ofExpr, l_Lean_MessageData_ofFormat,
    l_Lean_MessageData_ofName, l_Lean_MessageLog_add, l_Lean_indentExpr,
    l_Lean_instBEqMessageSeverity_beq, l_Lean_stringToMessageData,
};
use crate::r#gen::Lean::Meta::Basic::{
    l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey,
    l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp, l_Lean_Meta_Context_config,
    l_Lean_Meta_Context_configKey, l_Lean_Meta_TransparencyMode_toUInt64, l_Lean_Meta_isExprDefEq,
};
use crate::r#gen::Lean::Meta::CollectMVars::l_Lean_Meta_getMVars;
use crate::r#gen::Lean::Meta::Tactic::Assert::l_Lean_MVarId_note;
use crate::r#gen::Lean::Meta::Tactic::Assumption::l_Lean_MVarId_assumption;
use crate::r#gen::Lean::Meta::Tactic::Rename::l_Lean_MVarId_rename;
use crate::r#gen::Lean::Meta::Tactic::Simp::Attr::l_Lean_Meta_getSimpTheorems___boxed;
use crate::r#gen::Lean::Meta::Tactic::Simp::Main::l_Lean_Meta_simpGoal;
use crate::r#gen::Lean::Meta::Tactic::Simp::Types::{
    l_Lean_Meta_Simp_Context_setAutoUnfold, l_Lean_Meta_Simp_Context_setFailIfUnchanged,
};
use crate::r#gen::Lean::Meta::Tactic::TryThis::{
    initialize_Lean_Meta_Tactic_TryThis, l_Lean_Meta_Tactic_TryThis_addSuggestion,
    runtime_initialize_Lean_Meta_Tactic_TryThis,
};
use crate::r#gen::Lean::Meta::Tactic::Util::{
    l_Lean_MVarId_getTag, l_Lean_MVarId_getType, l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar,
};
use crate::r#gen::Lean::MetavarContext::{
    l_Lean_MetavarContext_getDelayedMVarAssignmentCore_x3f,
    l_Lean_MetavarContext_getExprAssignmentCore_x3f,
};
use crate::lean_imports_rs::Init::Data::Array::Basic::{
    lean_array_uget_borrowed, lean_array_uset, lean_mk_array,
};
use crate::lean_imports_rs::Init::Data::Array::Set::lean_array_fset;
use crate::lean_imports_rs::Init::Data::UInt::Basic::{
    lean_uint64_lor, lean_uint64_shift_left, lean_uint64_shift_right, lean_uint64_to_usize,
    lean_uint64_xor, lean_usize_land, lean_usize_mul, lean_usize_shift_left,
    lean_usize_shift_right,
};
use crate::lean_imports_rs::Init::Data::UInt::BasicAux::{
    lean_usize_add, lean_usize_dec_le, lean_usize_of_nat, lean_usize_sub, lean_usize_to_nat,
};
use crate::lean_imports_rs::Init::Prelude::{
    lean_array_fget, lean_array_fget_borrowed, lean_array_get_size, lean_array_push,
    lean_mk_empty_array_with_capacity, lean_nat_add, lean_nat_dec_le, lean_nat_dec_lt,
    lean_nat_div, lean_nat_mul, lean_panic_fn_borrowed, lean_string_dec_eq,
};
use crate::lean_imports_rs::Init::System::ST::{
    lean_st_ref_get, lean_st_ref_set, lean_st_ref_take,
};
use crate::lean_imports_rs::Lean::Expr::lean_expr_eqv;
use crate::lean_imports_rs::Lean::Meta::Basic::lean_infer_type;
pub static l___private_Lean_Elab_Tactic_Simpa_0__initFn___closed__0_00___x40_Lean_Elab_Tactic_Simpa_363244304____hygCtx___hyg_4__value: crate::leanh::LeanStringObject<7> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [108, 105, 110, 116, 101, 114, 0]};
static mut l___private_Lean_Elab_Tactic_Simpa_0__initFn___closed__0_00___x40_Lean_Elab_Tactic_Simpa_363244304____hygCtx___hyg_4_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Simpa_0__initFn___closed__0_00___x40_Lean_Elab_Tactic_Simpa_363244304____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Simpa_0__initFn___closed__1_00___x40_Lean_Elab_Tactic_Simpa_363244304____hygCtx___hyg_4__value: crate::leanh::LeanStringObject<17> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 17, m_capacity: 17, m_length: 16, m_data: [117, 110, 110, 101, 99, 101, 115, 115, 97, 114, 121, 83, 105, 109, 112, 97, 0]};
static mut l___private_Lean_Elab_Tactic_Simpa_0__initFn___closed__1_00___x40_Lean_Elab_Tactic_Simpa_363244304____hygCtx___hyg_4_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Simpa_0__initFn___closed__1_00___x40_Lean_Elab_Tactic_Simpa_363244304____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject;
static l___private_Lean_Elab_Tactic_Simpa_0__initFn___closed__2_00___x40_Lean_Elab_Tactic_Simpa_363244304____hygCtx___hyg_4__value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Simpa_0__initFn___closed__0_00___x40_Lean_Elab_Tactic_Simpa_363244304____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject,5701751079888345786 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Elab_Tactic_Simpa_0__initFn___closed__2_00___x40_Lean_Elab_Tactic_Simpa_363244304____hygCtx___hyg_4__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Simpa_0__initFn___closed__2_00___x40_Lean_Elab_Tactic_Simpa_363244304____hygCtx___hyg_4__value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Simpa_0__initFn___closed__1_00___x40_Lean_Elab_Tactic_Simpa_363244304____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject,74774201128064950 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_Simpa_0__initFn___closed__2_00___x40_Lean_Elab_Tactic_Simpa_363244304____hygCtx___hyg_4_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Simpa_0__initFn___closed__2_00___x40_Lean_Elab_Tactic_Simpa_363244304____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Simpa_0__initFn___closed__3_00___x40_Lean_Elab_Tactic_Simpa_363244304____hygCtx___hyg_4__value: crate::leanh::LeanStringObject<38> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 38, m_capacity: 38, m_length: 37, m_data: [101, 110, 97, 98, 108, 101, 32, 116, 104, 101, 32, 39, 117, 110, 110, 101, 99, 101, 115, 115, 97, 114, 121, 32, 115, 105, 109, 112, 97, 39, 32, 108, 105, 110, 116, 101, 114, 0]};
static mut l___private_Lean_Elab_Tactic_Simpa_0__initFn___closed__3_00___x40_Lean_Elab_Tactic_Simpa_363244304____hygCtx___hyg_4_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Simpa_0__initFn___closed__3_00___x40_Lean_Elab_Tactic_Simpa_363244304____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Simpa_0__initFn___closed__4_00___x40_Lean_Elab_Tactic_Simpa_363244304____hygCtx___hyg_4__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*3 + 0) as u16, other: 3, tag: 0 }, m_objs: [((( 1 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Simpa_0__initFn___closed__3_00___x40_Lean_Elab_Tactic_Simpa_363244304____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_Simpa_0__initFn___closed__4_00___x40_Lean_Elab_Tactic_Simpa_363244304____hygCtx___hyg_4_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Simpa_0__initFn___closed__4_00___x40_Lean_Elab_Tactic_Simpa_363244304____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject;
pub static mut l_linter_unnecessarySimpa: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__0___redArg___closed__0_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__0___redArg___closed__0: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__7___redArg___closed__0_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__7___redArg___closed__0: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__7___redArg___closed__1_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__7___redArg___closed__1: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_panic___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__9___closed__0_value: crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Elab_Tactic_instInhabitedTacticM___lam__0___boxed as *const core::ffi::c_void, m_arity: 9, m_num_fixed: 0, m_objs: [] };
static mut l_panic___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__9___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_panic___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__9___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__2___closed__0_value: crate::leanh::LeanStringObject<42> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 42, m_capacity: 42, m_length: 41, m_data: [84, 121, 112, 101, 32, 109, 105, 115, 109, 97, 116, 99, 104, 58, 32, 65, 102, 116, 101, 114, 32, 115, 105, 109, 112, 108, 105, 102, 105, 99, 97, 116, 105, 111, 110, 44, 32, 116, 101, 114, 109, 0]};
static mut l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__2___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__2___closed__0_value) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__2___closed__1_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__2___closed__1: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__2___closed__2_value: crate::leanh::LeanStringObject<2> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [10, 0]};
static mut l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__2___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__2___closed__2_value) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__2___closed__3_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__2___closed__3: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__2___closed__4_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__2___closed__4: u64 = 0;
pub static l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__8___closed__0_value: crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__8___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__8___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__8___closed__1_value: crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 0 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__8___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__8___closed__1_value) as *mut crate::leanh::LeanObject;
static mut l_Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1___closed__0_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1___closed__0: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1___closed__1_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1___closed__1: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__2_spec__3_spec__11___redArg___closed__0_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__2_spec__3_spec__11___redArg___closed__0: usize = 0;
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__2_spec__3_spec__11___redArg___closed__1_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__2_spec__3_spec__11___redArg___closed__1: usize = 0;
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__2_spec__3_spec__11___redArg___closed__2_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__2_spec__3_spec__11___redArg___closed__2: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4_spec__7_spec__16___redArg___lam__0___closed__0_value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [69, 108, 97, 98, 0]};
static mut l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4_spec__7_spec__16___redArg___lam__0___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4_spec__7_spec__16___redArg___lam__0___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4_spec__7_spec__16___redArg___lam__0___closed__1_value: crate::leanh::LeanStringObject<7> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [84, 97, 99, 116, 105, 99, 0]};
static mut l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4_spec__7_spec__16___redArg___lam__0___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4_spec__7_spec__16___redArg___lam__0___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4_spec__7_spec__16___redArg___lam__0___closed__2_value: crate::leanh::LeanStringObject<14> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 14, m_capacity: 14, m_length: 13, m_data: [117, 110, 115, 111, 108, 118, 101, 100, 71, 111, 97, 108, 115, 0]};
static mut l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4_spec__7_spec__16___redArg___lam__0___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4_spec__7_spec__16___redArg___lam__0___closed__2_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4_spec__7_spec__16___redArg___lam__0___closed__3_value: crate::leanh::LeanStringObject<17> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 17, m_capacity: 17, m_length: 16, m_data: [115, 121, 110, 116, 104, 80, 108, 97, 99, 101, 104, 111, 108, 100, 101, 114, 0]};
static mut l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4_spec__7_spec__16___redArg___lam__0___closed__3: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4_spec__7_spec__16___redArg___lam__0___closed__3_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4_spec__7_spec__16___redArg___lam__0___closed__4_value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [108, 101, 97, 110, 0]};
static mut l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4_spec__7_spec__16___redArg___lam__0___closed__4: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4_spec__7_spec__16___redArg___lam__0___closed__4_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4_spec__7_spec__16___redArg___lam__0___closed__5_value: crate::leanh::LeanStringObject<20> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 20, m_capacity: 20, m_length: 19, m_data: [105, 110, 100, 117, 99, 116, 105, 111, 110, 87, 105, 116, 104, 78, 111, 65, 108, 116, 115, 0]};
static mut l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4_spec__7_spec__16___redArg___lam__0___closed__5: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4_spec__7_spec__16___redArg___lam__0___closed__5_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4_spec__7_spec__16___redArg___lam__0___closed__6_value: crate::leanh::LeanStringObject<12> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 12, m_capacity: 12, m_length: 11, m_data: [95, 110, 97, 109, 101, 100, 69, 114, 114, 111, 114, 0]};
static mut l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4_spec__7_spec__16___redArg___lam__0___closed__6: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4_spec__7_spec__16___redArg___lam__0___closed__6_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4_spec__7_spec__16___redArg___lam__0___closed__7_value: crate::leanh::LeanStringObject<6> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [116, 114, 97, 99, 101, 0]};
static mut l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4_spec__7_spec__16___redArg___lam__0___closed__7: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4_spec__7_spec__16___redArg___lam__0___closed__7_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4_spec__7_spec__16___redArg___closed__0_value: crate::leanh::LeanStringObject<1> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 1, m_capacity: 1, m_length: 0, m_data: [0]};
static mut l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4_spec__7_spec__16___redArg___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4_spec__7_spec__16___redArg___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4___closed__0_value: crate::leanh::LeanStringObject<46> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 46, m_capacity: 46, m_length: 45, m_data: [84, 104, 105, 115, 32, 108, 105, 110, 116, 101, 114, 32, 99, 97, 110, 32, 98, 101, 32, 100, 105, 115, 97, 98, 108, 101, 100, 32, 119, 105, 116, 104, 32, 96, 115, 101, 116, 95, 111, 112, 116, 105, 111, 110, 32, 0]};
static mut l_Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4___closed__0_value) as *mut crate::leanh::LeanObject;
static mut l_Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4___closed__1_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4___closed__1: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4___closed__2_value: crate::leanh::LeanStringObject<8> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [32, 102, 97, 108, 115, 101, 96, 0]};
static mut l_Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4___closed__2_value) as *mut crate::leanh::LeanObject;
static mut l_Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4___closed__3_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4___closed__3: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__4___closed__0_value: crate::leanh::LeanStringObject<2> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [104, 0]};
static mut l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__4___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__4___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__4___closed__1_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__4___closed__0_value) as *mut crate::leanh::LeanObject,8738205681931236784 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__4___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__4___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__4___closed__2_value: crate::leanh::LeanStringObject<14> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 14, m_capacity: 14, m_length: 13, m_data: [84, 114, 121, 32, 96, 115, 105, 109, 112, 32, 97, 116, 32, 0]};
static mut l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__4___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__4___closed__2_value) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__4___closed__3_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__4___closed__3: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__4___closed__4_value: crate::leanh::LeanStringObject<27> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 27, m_capacity: 27, m_length: 26, m_data: [96, 32, 105, 110, 115, 116, 101, 97, 100, 32, 111, 102, 32, 96, 115, 105, 109, 112, 97, 32, 117, 115, 105, 110, 103, 32, 0]};
static mut l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__4___closed__4: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__4___closed__4_value) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__4___closed__5_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__4___closed__5: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__4___closed__6_value: crate::leanh::LeanStringObject<2> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [96, 0]};
static mut l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__4___closed__6: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__4___closed__6_value) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__4___closed__7_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__4___closed__7: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__4___closed__8_value: crate::leanh::LeanStringObject<32> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 32, m_capacity: 32, m_length: 31, m_data: [79, 99, 99, 117, 114, 115, 32, 99, 104, 101, 99, 107, 32, 102, 97, 105, 108, 101, 100, 58, 32, 69, 120, 112, 114, 101, 115, 115, 105, 111, 110, 0]};
static mut l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__4___closed__8: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__4___closed__8_value) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__4___closed__9_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__4___closed__9: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__4___closed__10_value: crate::leanh::LeanStringObject<20> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 20, m_capacity: 20, m_length: 19, m_data: [10, 99, 111, 110, 116, 97, 105, 110, 115, 32, 116, 104, 101, 32, 103, 111, 97, 108, 32, 0]};
static mut l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__4___closed__10: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__4___closed__10_value) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__4___closed__11_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__4___closed__11: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__4___closed__12_value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [116, 104, 105, 115, 0]};
static mut l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__4___closed__12: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__4___closed__12_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__4___closed__13_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__4___closed__12_value) as *mut crate::leanh::LeanObject,10861733237677782054 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__4___closed__13: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__4___closed__13_value) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__5___closed__0_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__5___closed__0: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__5___closed__1_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__5___closed__1: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__5___closed__2_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__5___closed__2: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__5___closed__3_value: crate::leanh::LeanStringObject<30> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 30, m_capacity: 30, m_length: 29, m_data: [116, 114, 121, 32, 39, 115, 105, 109, 112, 39, 32, 105, 110, 115, 116, 101, 97, 100, 32, 111, 102, 32, 39, 115, 105, 109, 112, 97, 39, 0]};
static mut l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__5___closed__3: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__5___closed__3_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__5___closed__4_value: crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 3 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__5___closed__3_value) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__5___closed__4: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__5___closed__4_value) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__5___closed__5_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__5___closed__5: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__0_value: crate::leanh::LeanStringObject<7> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [116, 97, 99, 116, 105, 99, 0]};
static mut l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__1_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__0_value) as *mut crate::leanh::LeanObject,16145843736367156323 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__2_value: crate::leanh::LeanStringObject<10> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [84, 114, 121, 32, 116, 104, 105, 115, 58, 0]};
static mut l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__2_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__3_value: crate::leanh::LeanStringObject<23> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 23, m_capacity: 23, m_length: 22, m_data: [76, 101, 97, 110, 46, 69, 108, 97, 98, 46, 84, 97, 99, 116, 105, 99, 46, 83, 105, 109, 112, 97, 0]};
static mut l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__3: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__3_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__4_value: crate::leanh::LeanStringObject<71> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 71, m_capacity: 71, m_length: 70, m_data: [95, 112, 114, 105, 118, 97, 116, 101, 46, 76, 101, 97, 110, 46, 69, 108, 97, 98, 46, 84, 97, 99, 116, 105, 99, 46, 83, 105, 109, 112, 97, 46, 48, 46, 76, 101, 97, 110, 46, 69, 108, 97, 98, 46, 84, 97, 99, 116, 105, 99, 46, 83, 105, 109, 112, 97, 46, 101, 118, 97, 108, 83, 105, 109, 112, 97, 67, 111, 114, 101, 0]};
static mut l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__4: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__4_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__5_value: crate::leanh::LeanStringObject<34> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 34, m_capacity: 34, m_length: 33, m_data: [117, 110, 114, 101, 97, 99, 104, 97, 98, 108, 101, 32, 99, 111, 100, 101, 32, 104, 97, 115, 32, 98, 101, 101, 110, 32, 114, 101, 97, 99, 104, 101, 100, 0]};
static mut l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__5: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__5_value) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__6_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__6: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__7_value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [115, 105, 109, 112, 0]};
static mut l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__7: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__7_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__8_value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [110, 117, 108, 108, 0]};
static mut l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__8: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__8_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__9_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__8_value) as *mut crate::leanh::LeanObject,9855511589286918680 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__9: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__9_value) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__10_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__10: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__11_value: crate::leanh::LeanStringObject<6> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [117, 115, 105, 110, 103, 0]};
static mut l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__11: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__11_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__12_value: crate::leanh::LeanStringObject<9> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [115, 105, 109, 112, 65, 114, 103, 115, 0]};
static mut l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__12: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__12_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__13_value: crate::leanh::LeanStringObject<2> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [91, 0]};
static mut l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__13: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__13_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__14_value: crate::leanh::LeanStringObject<2> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [93, 0]};
static mut l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__14: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__14_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__15_value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [111, 110, 108, 121, 0]};
static mut l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__15: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__15_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__16_value: crate::leanh::LeanStringObject<7> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [117, 115, 105, 110, 103, 33, 0]};
static mut l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__16: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__16_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__17_value: crate::leanh::LeanStringObject<15> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 15, m_capacity: 15, m_length: 14, m_data: [115, 105, 109, 112, 97, 85, 115, 105, 110, 103, 66, 97, 110, 103, 0]};
static mut l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__17: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__17_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__18_value: crate::leanh::LeanStringObject<23> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 23, m_capacity: 23, m_length: 22, m_data: [115, 105, 109, 112, 97, 85, 115, 105, 110, 103, 66, 97, 110, 103, 65, 114, 103, 115, 82, 101, 115, 116, 0]};
static mut l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__18: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__18_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__19_value: crate::leanh::LeanStringObject<2> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [33, 0]};
static mut l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__19: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__19_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__20_value: crate::leanh::LeanStringObject<14> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 14, m_capacity: 14, m_length: 13, m_data: [116, 97, 99, 116, 105, 99, 83, 105, 109, 112, 97, 33, 95, 0]};
static mut l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__20: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__20_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__21_value: crate::leanh::LeanStringObject<7> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [115, 105, 109, 112, 97, 33, 0]};
static mut l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__21: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__21_value) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__22_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__22: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__23_value: crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Meta_getSimpTheorems___boxed as *const core::ffi::c_void, m_arity: 3, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__23: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__23_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___closed__0_value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [76, 101, 97, 110, 0]};
static mut l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___closed__1_value: crate::leanh::LeanStringObject<7> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [80, 97, 114, 115, 101, 114, 0]};
static mut l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___closed__2_value: crate::leanh::LeanStringObject<6> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [115, 105, 109, 112, 97, 0]};
static mut l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___closed__2_value) as *mut crate::leanh::LeanObject;
static l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___closed__3_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___closed__0_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___closed__3_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___closed__3_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___closed__1_value) as *mut crate::leanh::LeanObject,8018486133748762727 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___closed__3_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___closed__3_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4_spec__7_spec__16___redArg___lam__0___closed__1_value) as *mut crate::leanh::LeanObject,18344149449936419494 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___closed__3_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___closed__3_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___closed__2_value) as *mut crate::leanh::LeanObject,8158499707934325445 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___closed__3: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___closed__3_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___closed__4_value: crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__0___boxed as *const core::ffi::c_void, m_arity: 9, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___closed__4: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___closed__4_value) as *mut crate::leanh::LeanObject;
static l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___closed__5_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___closed__0_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___closed__5_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___closed__5_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___closed__1_value) as *mut crate::leanh::LeanObject,8018486133748762727 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___closed__5_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___closed__5_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4_spec__7_spec__16___redArg___lam__0___closed__1_value) as *mut crate::leanh::LeanObject,18344149449936419494 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___closed__5_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___closed__5_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__12_value) as *mut crate::leanh::LeanObject,15056235328782124702 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___closed__5: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___closed__5_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___closed__6_value: crate::leanh::LeanStringObject<14> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 14, m_capacity: 14, m_length: 13, m_data: [115, 105, 109, 112, 97, 65, 114, 103, 115, 82, 101, 115, 116, 0]};
static mut l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___closed__6: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___closed__6_value) as *mut crate::leanh::LeanObject;
static l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___closed__7_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___closed__0_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___closed__7_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___closed__7_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___closed__1_value) as *mut crate::leanh::LeanObject,8018486133748762727 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___closed__7_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___closed__7_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4_spec__7_spec__16___redArg___lam__0___closed__1_value) as *mut crate::leanh::LeanObject,18344149449936419494 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___closed__7_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___closed__7_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___closed__6_value) as *mut crate::leanh::LeanObject,15058711512568137097 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___closed__7: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___closed__7_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___closed__8_value: crate::leanh::LeanStringObject<10> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [111, 112, 116, 67, 111, 110, 102, 105, 103, 0]};
static mut l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___closed__8: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___closed__8_value) as *mut crate::leanh::LeanObject;
static l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___closed__9_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___closed__0_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___closed__9_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___closed__9_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___closed__1_value) as *mut crate::leanh::LeanObject,8018486133748762727 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___closed__9_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___closed__9_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4_spec__7_spec__16___redArg___lam__0___closed__1_value) as *mut crate::leanh::LeanObject,18344149449936419494 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___closed__9_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___closed__9_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___closed__8_value) as *mut crate::leanh::LeanObject,3488656302031949961 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___closed__9: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___closed__9_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpa___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpa__1___closed__0_value: crate::leanh::LeanStringObject<6> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [83, 105, 109, 112, 97, 0]};
static mut l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpa___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpa__1___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpa___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpa__1___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpa___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpa__1___closed__1_value: crate::leanh::LeanStringObject<10> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [101, 118, 97, 108, 83, 105, 109, 112, 97, 0]};
static mut l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpa___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpa__1___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpa___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpa__1___closed__1_value) as *mut crate::leanh::LeanObject;
static l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpa___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpa__1___closed__2_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___closed__0_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpa___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpa__1___closed__2_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpa___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpa__1___closed__2_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4_spec__7_spec__16___redArg___lam__0___closed__0_value) as *mut crate::leanh::LeanObject,11510100434945111860 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpa___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpa__1___closed__2_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpa___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpa__1___closed__2_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4_spec__7_spec__16___redArg___lam__0___closed__1_value) as *mut crate::leanh::LeanObject,12733524109236233889 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpa___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpa__1___closed__2_value_aux_3: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpa___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpa__1___closed__2_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpa___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpa__1___closed__0_value) as *mut crate::leanh::LeanObject,9997224922833086140 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpa___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpa__1___closed__2_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpa___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpa__1___closed__2_value_aux_3) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpa___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpa__1___closed__1_value) as *mut crate::leanh::LeanObject,15936663740303437796 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpa___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpa__1___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpa___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpa__1___closed__2_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpa___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpa_declRange__3___closed__0_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 31 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,((( 43 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpa___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpa_declRange__3___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpa___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpa_declRange__3___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpa___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpa_declRange__3___closed__1_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 90 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,((( 33 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpa___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpa_declRange__3___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpa___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpa_declRange__3___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpa___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpa_declRange__3___closed__2_value: crate::leanh::LeanCtorObject<4> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*4 + 0) as u16, other: 4, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpa___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpa_declRange__3___closed__0_value) as *mut crate::leanh::LeanObject,((( 43 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpa___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpa_declRange__3___closed__1_value) as *mut crate::leanh::LeanObject,((( 33 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpa___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpa_declRange__3___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpa___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpa_declRange__3___closed__2_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpa___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpa_declRange__3___closed__3_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 31 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,((( 47 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpa___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpa_declRange__3___closed__3: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpa___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpa_declRange__3___closed__3_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpa___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpa_declRange__3___closed__4_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 31 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,((( 56 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpa___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpa_declRange__3___closed__4: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpa___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpa_declRange__3___closed__4_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpa___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpa_declRange__3___closed__5_value: crate::leanh::LeanCtorObject<4> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*4 + 0) as u16, other: 4, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpa___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpa_declRange__3___closed__3_value) as *mut crate::leanh::LeanObject,((( 47 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpa___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpa_declRange__3___closed__4_value) as *mut crate::leanh::LeanObject,((( 56 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpa___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpa_declRange__3___closed__5: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpa___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpa_declRange__3___closed__5_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpa___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpa_declRange__3___closed__6_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpa___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpa_declRange__3___closed__2_value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpa___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpa_declRange__3___closed__5_value) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpa___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpa_declRange__3___closed__6: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpa___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpa_declRange__3___closed__6_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Tactic_Simpa_evalSimpaUsingBang___lam__0___closed__0_value:
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
static mut l_Lean_Elab_Tactic_Simpa_evalSimpaUsingBang___lam__0___closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Simpa_evalSimpaUsingBang___lam__0___closed__0_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Elab_Tactic_Simpa_evalSimpaUsingBang___closed__0_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___closed__0_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l_Lean_Elab_Tactic_Simpa_evalSimpaUsingBang___closed__0_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Elab_Tactic_Simpa_evalSimpaUsingBang___closed__0_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___closed__1_value) as *mut crate::leanh::LeanObject,8018486133748762727 as *mut crate::leanh::LeanObject] };
static l_Lean_Elab_Tactic_Simpa_evalSimpaUsingBang___closed__0_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Elab_Tactic_Simpa_evalSimpaUsingBang___closed__0_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4_spec__7_spec__16___redArg___lam__0___closed__1_value) as *mut crate::leanh::LeanObject,18344149449936419494 as *mut crate::leanh::LeanObject] };
pub static l_Lean_Elab_Tactic_Simpa_evalSimpaUsingBang___closed__0_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Elab_Tactic_Simpa_evalSimpaUsingBang___closed__0_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__17_value) as *mut crate::leanh::LeanObject,4028380270007415247 as *mut crate::leanh::LeanObject] };
static mut l_Lean_Elab_Tactic_Simpa_evalSimpaUsingBang___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Simpa_evalSimpaUsingBang___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Tactic_Simpa_evalSimpaUsingBang___closed__1_value:
    crate::leanh::LeanStringObject<2> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 2,
    m_capacity: 2,
    m_length: 1,
    m_data: [63, 0],
};
static mut l_Lean_Elab_Tactic_Simpa_evalSimpaUsingBang___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Simpa_evalSimpaUsingBang___closed__1_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Elab_Tactic_Simpa_evalSimpaUsingBang___closed__2_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___closed__0_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l_Lean_Elab_Tactic_Simpa_evalSimpaUsingBang___closed__2_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Elab_Tactic_Simpa_evalSimpaUsingBang___closed__2_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___closed__1_value) as *mut crate::leanh::LeanObject,8018486133748762727 as *mut crate::leanh::LeanObject] };
static l_Lean_Elab_Tactic_Simpa_evalSimpaUsingBang___closed__2_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Elab_Tactic_Simpa_evalSimpaUsingBang___closed__2_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4_spec__7_spec__16___redArg___lam__0___closed__1_value) as *mut crate::leanh::LeanObject,18344149449936419494 as *mut crate::leanh::LeanObject] };
pub static l_Lean_Elab_Tactic_Simpa_evalSimpaUsingBang___closed__2_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Elab_Tactic_Simpa_evalSimpaUsingBang___closed__2_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__18_value) as *mut crate::leanh::LeanObject,8494989222425758984 as *mut crate::leanh::LeanObject] };
static mut l_Lean_Elab_Tactic_Simpa_evalSimpaUsingBang___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Simpa_evalSimpaUsingBang___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaUsingBang___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpaUsingBang__1___closed__0_value: crate::leanh::LeanStringObject<19> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 19, m_capacity: 19, m_length: 18, m_data: [101, 118, 97, 108, 83, 105, 109, 112, 97, 85, 115, 105, 110, 103, 66, 97, 110, 103, 0]};
static mut l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaUsingBang___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpaUsingBang__1___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaUsingBang___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpaUsingBang__1___closed__0_value) as *mut crate::leanh::LeanObject;
static l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaUsingBang___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpaUsingBang__1___closed__1_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___closed__0_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaUsingBang___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpaUsingBang__1___closed__1_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaUsingBang___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpaUsingBang__1___closed__1_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4_spec__7_spec__16___redArg___lam__0___closed__0_value) as *mut crate::leanh::LeanObject,11510100434945111860 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaUsingBang___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpaUsingBang__1___closed__1_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaUsingBang___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpaUsingBang__1___closed__1_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4_spec__7_spec__16___redArg___lam__0___closed__1_value) as *mut crate::leanh::LeanObject,12733524109236233889 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaUsingBang___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpaUsingBang__1___closed__1_value_aux_3: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaUsingBang___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpaUsingBang__1___closed__1_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpa___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpa__1___closed__0_value) as *mut crate::leanh::LeanObject,9997224922833086140 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaUsingBang___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpaUsingBang__1___closed__1_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaUsingBang___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpaUsingBang__1___closed__1_value_aux_3) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaUsingBang___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpaUsingBang__1___closed__0_value) as *mut crate::leanh::LeanObject,17113284790989950578 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaUsingBang___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpaUsingBang__1___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaUsingBang___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpaUsingBang__1___closed__1_value) as *mut crate::leanh::LeanObject;
pub unsafe fn l_Lean_Option_register___at___00__private_Lean_Elab_Tactic_Simpa_0__initFn_00___x40_Lean_Elab_Tactic_Simpa_363244304____hygCtx___hyg_4__spec__0(
    mut v_name_4045_: *mut crate::leanh::LeanObject,
    mut v_decl_4046_: *mut crate::leanh::LeanObject,
    mut v_ref_4047_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_defValue_4049_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_descr_4050_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_deprecation_x3f_4051_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4052_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4053_: u8 = 0;
    let mut v___x_4054_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4055_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4057_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4058_: u8 = 0;
    let mut v___x_4059_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4061_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4062_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4063_: u8 = 0;
    let mut v_unused_4064_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4065_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4067_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4068_: u8 = 0;
    let mut v___x_4070_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4071_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4072_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_defValue_4049_ = crate::leanh::lean_ctor_get(v_decl_4046_, 0);
                v_descr_4050_ = crate::leanh::lean_ctor_get(v_decl_4046_, 1);
                v_deprecation_x3f_4051_ = crate::leanh::lean_ctor_get(v_decl_4046_, 2);
                v___x_4052_ = crate::leanh::lean_alloc_ctor(1, 0, (1) as u32);
                v___x_4053_ = (crate::leanh::lean_unbox(v_defValue_4049_) as u8);
                crate::leanh::lean_ctor_set_uint8(v___x_4052_, 0 as u32, v___x_4053_);
                crate::leanh::lean_inc(v_deprecation_x3f_4051_);
                crate::leanh::lean_inc_ref(v_descr_4050_);
                crate::leanh::lean_inc_n(v_name_4045_, 2);
                v___x_4054_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4054_, 0, v_name_4045_);
                crate::leanh::lean_ctor_set(v___x_4054_, 1, v_ref_4047_);
                crate::leanh::lean_ctor_set(v___x_4054_, 2, v___x_4052_);
                crate::leanh::lean_ctor_set(v___x_4054_, 3, v_descr_4050_);
                crate::leanh::lean_ctor_set(v___x_4054_, 4, v_deprecation_x3f_4051_);
                v___x_4055_ = lean_register_option(v_name_4045_, v___x_4054_);
                if crate::leanh::lean_obj_tag(v___x_4055_) == 0 {
                    v_isSharedCheck_4063_ = (!crate::leanh::lean_is_exclusive(v___x_4055_)) as u8;
                    if v_isSharedCheck_4063_ == 0 {
                        v_unused_4064_ = crate::leanh::lean_ctor_get(v___x_4055_, 0);
                        crate::leanh::lean_dec(v_unused_4064_);
                        v___x_4057_ = v___x_4055_;
                        v_isShared_4058_ = v_isSharedCheck_4063_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v___x_4055_);
                        v___x_4057_ = crate::leanh::lean_box(0);
                        v_isShared_4058_ = v_isSharedCheck_4063_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_name_4045_);
                    v_a_4065_ = crate::leanh::lean_ctor_get(v___x_4055_, 0);
                    v_isSharedCheck_4072_ = (!crate::leanh::lean_is_exclusive(v___x_4055_)) as u8;
                    if v_isSharedCheck_4072_ == 0 {
                        v___x_4067_ = v___x_4055_;
                        v_isShared_4068_ = v_isSharedCheck_4072_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4065_);
                        crate::leanh::lean_dec(v___x_4055_);
                        v___x_4067_ = crate::leanh::lean_box(0);
                        v_isShared_4068_ = v_isSharedCheck_4072_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                crate::leanh::lean_inc(v_defValue_4049_);
                v___x_4059_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4059_, 0, v_name_4045_);
                crate::leanh::lean_ctor_set(v___x_4059_, 1, v_defValue_4049_);
                if v_isShared_4058_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4057_, 0, v___x_4059_);
                    v___x_4061_ = v___x_4057_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4062_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4062_, 0, v___x_4059_);
                    v___x_4061_ = v_reuseFailAlloc_4062_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_4061_;
            }
            3 => {
                if v_isShared_4068_ == 0 {
                    v___x_4070_ = v___x_4067_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4071_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4071_, 0, v_a_4065_);
                    v___x_4070_ = v_reuseFailAlloc_4071_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_4070_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Option_register___at___00__private_Lean_Elab_Tactic_Simpa_0__initFn_00___x40_Lean_Elab_Tactic_Simpa_363244304____hygCtx___hyg_4__spec__0___boxed(
    mut v_name_4073_: *mut crate::leanh::LeanObject,
    mut v_decl_4074_: *mut crate::leanh::LeanObject,
    mut v_ref_4075_: *mut crate::leanh::LeanObject,
    mut v_a_4076_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4077_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4077_ = l_Lean_Option_register___at___00__private_Lean_Elab_Tactic_Simpa_0__initFn_00___x40_Lean_Elab_Tactic_Simpa_363244304____hygCtx___hyg_4__spec__0(v_name_4073_, v_decl_4074_, v_ref_4075_);
    crate::leanh::lean_dec_ref(v_decl_4074_);
    return v_res_4077_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Simpa_0__initFn_00___x40_Lean_Elab_Tactic_Simpa_363244304____hygCtx___hyg_4_()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4090_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4091_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4092_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4090_ = l___private_Lean_Elab_Tactic_Simpa_0__initFn___closed__2_00___x40_Lean_Elab_Tactic_Simpa_363244304____hygCtx___hyg_4_;
    v___x_4091_ = l___private_Lean_Elab_Tactic_Simpa_0__initFn___closed__4_00___x40_Lean_Elab_Tactic_Simpa_363244304____hygCtx___hyg_4_;
    v___x_4092_ = l_Lean_Option_register___at___00__private_Lean_Elab_Tactic_Simpa_0__initFn_00___x40_Lean_Elab_Tactic_Simpa_363244304____hygCtx___hyg_4__spec__0(v___x_4090_, v___x_4091_, v___x_4090_);
    return v___x_4092_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Simpa_0__initFn_00___x40_Lean_Elab_Tactic_Simpa_363244304____hygCtx___hyg_4____boxed(
    mut v_a_4093_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4094_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4094_ = l___private_Lean_Elab_Tactic_Simpa_0__initFn_00___x40_Lean_Elab_Tactic_Simpa_363244304____hygCtx___hyg_4_();
    return v_res_4094_;
}
pub unsafe fn l_Lean_Elab_Tactic_Simpa_getLinterUnnecessarySimpa(
    mut v_o_4095_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_4096_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4097_: u8 = 0;
    v___x_4096_ = l_linter_unnecessarySimpa;
    v___x_4097_ = l_Lean_Linter_getLinterValue(v___x_4096_, v_o_4095_);
    return v___x_4097_;
}
pub unsafe fn l_Lean_Elab_Tactic_Simpa_getLinterUnnecessarySimpa___boxed(
    mut v_o_4098_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4099_: u8 = 0;
    let mut v_r_4100_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4099_ = l_Lean_Elab_Tactic_Simpa_getLinterUnnecessarySimpa(v_o_4098_);
    crate::leanh::lean_dec_ref(v_o_4098_);
    v_r_4100_ = crate::leanh::lean_box((v_res_4099_) as usize);
    return v_r_4100_;
}
pub unsafe fn _init_l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__0___redArg___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4101_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4102_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4103_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4101_ = crate::leanh::lean_box(0);
    v___x_4102_ = l_Lean_Elab_unsupportedSyntaxExceptionId;
    v___x_4103_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_4103_, 0, v___x_4102_);
    crate::leanh::lean_ctor_set(v___x_4103_, 1, v___x_4101_);
    return v___x_4103_;
}
pub unsafe fn l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__0___redArg()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4105_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4106_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4105_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__0___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__0___redArg___closed__0_once), _init_l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__0___redArg___closed__0);
    v___x_4106_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_4106_, 0, v___x_4105_);
    return v___x_4106_;
}
pub unsafe fn l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__0___redArg___boxed(
    mut v___y_4107_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4108_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4108_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__0___redArg();
    return v_res_4108_;
}
pub unsafe fn l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__0(
    mut v_00_u03b1_4109_: *mut crate::leanh::LeanObject,
    mut v___y_4110_: *mut crate::leanh::LeanObject,
    mut v___y_4111_: *mut crate::leanh::LeanObject,
    mut v___y_4112_: *mut crate::leanh::LeanObject,
    mut v___y_4113_: *mut crate::leanh::LeanObject,
    mut v___y_4114_: *mut crate::leanh::LeanObject,
    mut v___y_4115_: *mut crate::leanh::LeanObject,
    mut v___y_4116_: *mut crate::leanh::LeanObject,
    mut v___y_4117_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4119_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4119_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__0___redArg();
    return v___x_4119_;
}
pub unsafe fn l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__0___boxed(
    mut v_00_u03b1_4120_: *mut crate::leanh::LeanObject,
    mut v___y_4121_: *mut crate::leanh::LeanObject,
    mut v___y_4122_: *mut crate::leanh::LeanObject,
    mut v___y_4123_: *mut crate::leanh::LeanObject,
    mut v___y_4124_: *mut crate::leanh::LeanObject,
    mut v___y_4125_: *mut crate::leanh::LeanObject,
    mut v___y_4126_: *mut crate::leanh::LeanObject,
    mut v___y_4127_: *mut crate::leanh::LeanObject,
    mut v___y_4128_: *mut crate::leanh::LeanObject,
    mut v___y_4129_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4130_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4130_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__0(v_00_u03b1_4120_, v___y_4121_, v___y_4122_, v___y_4123_, v___y_4124_, v___y_4125_, v___y_4126_, v___y_4127_, v___y_4128_);
    crate::leanh::lean_dec(v___y_4128_);
    crate::leanh::lean_dec_ref(v___y_4127_);
    crate::leanh::lean_dec(v___y_4126_);
    crate::leanh::lean_dec_ref(v___y_4125_);
    crate::leanh::lean_dec(v___y_4124_);
    crate::leanh::lean_dec_ref(v___y_4123_);
    crate::leanh::lean_dec(v___y_4122_);
    crate::leanh::lean_dec_ref(v___y_4121_);
    return v_res_4130_;
}
pub unsafe fn l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__5___redArg___lam__0(
    mut v_x_4131_: *mut crate::leanh::LeanObject,
    mut v___y_4132_: *mut crate::leanh::LeanObject,
    mut v___y_4133_: *mut crate::leanh::LeanObject,
    mut v___y_4134_: *mut crate::leanh::LeanObject,
    mut v___y_4135_: *mut crate::leanh::LeanObject,
    mut v___y_4136_: *mut crate::leanh::LeanObject,
    mut v___y_4137_: *mut crate::leanh::LeanObject,
    mut v___y_4138_: *mut crate::leanh::LeanObject,
    mut v___y_4139_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4141_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    crate::leanh::lean_inc(v___y_4135_);
    crate::leanh::lean_inc_ref(v___y_4134_);
    crate::leanh::lean_inc(v___y_4133_);
    crate::leanh::lean_inc_ref(v___y_4132_);
    v___x_4141_ = crate::leanh::lean_apply_9(
        v_x_4131_,
        v___y_4132_,
        v___y_4133_,
        v___y_4134_,
        v___y_4135_,
        v___y_4136_,
        v___y_4137_,
        v___y_4138_,
        v___y_4139_,
        crate::leanh::lean_box(0),
    );
    return v___x_4141_;
}
pub unsafe fn l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__5___redArg___lam__0___boxed(
    mut v_x_4142_: *mut crate::leanh::LeanObject,
    mut v___y_4143_: *mut crate::leanh::LeanObject,
    mut v___y_4144_: *mut crate::leanh::LeanObject,
    mut v___y_4145_: *mut crate::leanh::LeanObject,
    mut v___y_4146_: *mut crate::leanh::LeanObject,
    mut v___y_4147_: *mut crate::leanh::LeanObject,
    mut v___y_4148_: *mut crate::leanh::LeanObject,
    mut v___y_4149_: *mut crate::leanh::LeanObject,
    mut v___y_4150_: *mut crate::leanh::LeanObject,
    mut v___y_4151_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4152_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4152_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__5___redArg___lam__0(v_x_4142_, v___y_4143_, v___y_4144_, v___y_4145_, v___y_4146_, v___y_4147_, v___y_4148_, v___y_4149_, v___y_4150_);
    crate::leanh::lean_dec(v___y_4146_);
    crate::leanh::lean_dec_ref(v___y_4145_);
    crate::leanh::lean_dec(v___y_4144_);
    crate::leanh::lean_dec_ref(v___y_4143_);
    return v_res_4152_;
}
pub unsafe fn l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__5___redArg(
    mut v_mvarId_4153_: *mut crate::leanh::LeanObject,
    mut v_x_4154_: *mut crate::leanh::LeanObject,
    mut v___y_4155_: *mut crate::leanh::LeanObject,
    mut v___y_4156_: *mut crate::leanh::LeanObject,
    mut v___y_4157_: *mut crate::leanh::LeanObject,
    mut v___y_4158_: *mut crate::leanh::LeanObject,
    mut v___y_4159_: *mut crate::leanh::LeanObject,
    mut v___y_4160_: *mut crate::leanh::LeanObject,
    mut v___y_4161_: *mut crate::leanh::LeanObject,
    mut v___y_4162_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_4164_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4165_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4166_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4168_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4169_: u8 = 0;
    let mut v___x_4171_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4172_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4173_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                crate::leanh::lean_inc(v___y_4158_);
                crate::leanh::lean_inc_ref(v___y_4157_);
                crate::leanh::lean_inc(v___y_4156_);
                crate::leanh::lean_inc_ref(v___y_4155_);
                v___f_4164_ = crate::leanh::lean_alloc_closure(l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__5___redArg___lam__0___boxed as *mut core::ffi::c_void, 10, 5);
                crate::leanh::lean_closure_set(v___f_4164_, 0, v_x_4154_);
                crate::leanh::lean_closure_set(v___f_4164_, 1, v___y_4155_);
                crate::leanh::lean_closure_set(v___f_4164_, 2, v___y_4156_);
                crate::leanh::lean_closure_set(v___f_4164_, 3, v___y_4157_);
                crate::leanh::lean_closure_set(v___f_4164_, 4, v___y_4158_);
                v___x_4165_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(
                    crate::leanh::lean_box(0),
                    v_mvarId_4153_,
                    v___f_4164_,
                    v___y_4159_,
                    v___y_4160_,
                    v___y_4161_,
                    v___y_4162_,
                );
                if crate::leanh::lean_obj_tag(v___x_4165_) == 0 {
                    return v___x_4165_;
                } else {
                    v_a_4166_ = crate::leanh::lean_ctor_get(v___x_4165_, 0);
                    v_isSharedCheck_4173_ = (!crate::leanh::lean_is_exclusive(v___x_4165_)) as u8;
                    if v_isSharedCheck_4173_ == 0 {
                        v___x_4168_ = v___x_4165_;
                        v_isShared_4169_ = v_isSharedCheck_4173_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4166_);
                        crate::leanh::lean_dec(v___x_4165_);
                        v___x_4168_ = crate::leanh::lean_box(0);
                        v_isShared_4169_ = v_isSharedCheck_4173_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_4169_ == 0 {
                    v___x_4171_ = v___x_4168_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4172_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4172_, 0, v_a_4166_);
                    v___x_4171_ = v_reuseFailAlloc_4172_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_4171_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__5___redArg___boxed(
    mut v_mvarId_4174_: *mut crate::leanh::LeanObject,
    mut v_x_4175_: *mut crate::leanh::LeanObject,
    mut v___y_4176_: *mut crate::leanh::LeanObject,
    mut v___y_4177_: *mut crate::leanh::LeanObject,
    mut v___y_4178_: *mut crate::leanh::LeanObject,
    mut v___y_4179_: *mut crate::leanh::LeanObject,
    mut v___y_4180_: *mut crate::leanh::LeanObject,
    mut v___y_4181_: *mut crate::leanh::LeanObject,
    mut v___y_4182_: *mut crate::leanh::LeanObject,
    mut v___y_4183_: *mut crate::leanh::LeanObject,
    mut v___y_4184_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4185_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4185_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__5___redArg(v_mvarId_4174_, v_x_4175_, v___y_4176_, v___y_4177_, v___y_4178_, v___y_4179_, v___y_4180_, v___y_4181_, v___y_4182_, v___y_4183_);
    crate::leanh::lean_dec(v___y_4183_);
    crate::leanh::lean_dec_ref(v___y_4182_);
    crate::leanh::lean_dec(v___y_4181_);
    crate::leanh::lean_dec_ref(v___y_4180_);
    crate::leanh::lean_dec(v___y_4179_);
    crate::leanh::lean_dec_ref(v___y_4178_);
    crate::leanh::lean_dec(v___y_4177_);
    crate::leanh::lean_dec_ref(v___y_4176_);
    return v_res_4185_;
}
pub unsafe fn l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__5(
    mut v_00_u03b1_4186_: *mut crate::leanh::LeanObject,
    mut v_mvarId_4187_: *mut crate::leanh::LeanObject,
    mut v_x_4188_: *mut crate::leanh::LeanObject,
    mut v___y_4189_: *mut crate::leanh::LeanObject,
    mut v___y_4190_: *mut crate::leanh::LeanObject,
    mut v___y_4191_: *mut crate::leanh::LeanObject,
    mut v___y_4192_: *mut crate::leanh::LeanObject,
    mut v___y_4193_: *mut crate::leanh::LeanObject,
    mut v___y_4194_: *mut crate::leanh::LeanObject,
    mut v___y_4195_: *mut crate::leanh::LeanObject,
    mut v___y_4196_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4198_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4198_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__5___redArg(v_mvarId_4187_, v_x_4188_, v___y_4189_, v___y_4190_, v___y_4191_, v___y_4192_, v___y_4193_, v___y_4194_, v___y_4195_, v___y_4196_);
    return v___x_4198_;
}
pub unsafe fn l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__5___boxed(
    mut v_00_u03b1_4199_: *mut crate::leanh::LeanObject,
    mut v_mvarId_4200_: *mut crate::leanh::LeanObject,
    mut v_x_4201_: *mut crate::leanh::LeanObject,
    mut v___y_4202_: *mut crate::leanh::LeanObject,
    mut v___y_4203_: *mut crate::leanh::LeanObject,
    mut v___y_4204_: *mut crate::leanh::LeanObject,
    mut v___y_4205_: *mut crate::leanh::LeanObject,
    mut v___y_4206_: *mut crate::leanh::LeanObject,
    mut v___y_4207_: *mut crate::leanh::LeanObject,
    mut v___y_4208_: *mut crate::leanh::LeanObject,
    mut v___y_4209_: *mut crate::leanh::LeanObject,
    mut v___y_4210_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4211_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4211_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__5(v_00_u03b1_4199_, v_mvarId_4200_, v_x_4201_, v___y_4202_, v___y_4203_, v___y_4204_, v___y_4205_, v___y_4206_, v___y_4207_, v___y_4208_, v___y_4209_);
    crate::leanh::lean_dec(v___y_4209_);
    crate::leanh::lean_dec_ref(v___y_4208_);
    crate::leanh::lean_dec(v___y_4207_);
    crate::leanh::lean_dec_ref(v___y_4206_);
    crate::leanh::lean_dec(v___y_4205_);
    crate::leanh::lean_dec_ref(v___y_4204_);
    crate::leanh::lean_dec(v___y_4203_);
    crate::leanh::lean_dec_ref(v___y_4202_);
    return v_res_4211_;
}
pub unsafe fn _init_l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__7___redArg___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4212_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4213_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4214_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4212_ = crate::leanh::lean_unsigned_to_nat(32);
    v___x_4213_ = lean_mk_empty_array_with_capacity(v___x_4212_);
    v___x_4214_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_4214_, 0, v___x_4213_);
    return v___x_4214_;
}
pub unsafe fn _init_l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__7___redArg___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4215_: usize = 0;
    let mut v___x_4216_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4217_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4218_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4219_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4220_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4215_ = 5usize;
    v___x_4216_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_4217_ = crate::leanh::lean_unsigned_to_nat(32);
    v___x_4218_ = lean_mk_empty_array_with_capacity(v___x_4217_);
    v___x_4219_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__7___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__7___redArg___closed__0_once), _init_l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__7___redArg___closed__0);
    v___x_4220_ = crate::leanh::lean_alloc_ctor(0, 4, (core::mem::size_of::<usize>() * 1) as u32);
    crate::leanh::lean_ctor_set(v___x_4220_, 0, v___x_4219_);
    crate::leanh::lean_ctor_set(v___x_4220_, 1, v___x_4218_);
    crate::leanh::lean_ctor_set(v___x_4220_, 2, v___x_4216_);
    crate::leanh::lean_ctor_set(v___x_4220_, 3, v___x_4216_);
    crate::leanh::lean_ctor_set_usize(v___x_4220_, 4, v___x_4215_);
    return v___x_4220_;
}
pub unsafe fn l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__7___redArg(
    mut v___y_4221_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4223_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_infoState_4224_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_trees_4225_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4226_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_infoState_4227_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_4228_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_4229_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ngen_4230_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_4231_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_traceState_4232_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_cache_4233_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_messages_4234_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_4235_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4237_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4238_: u8 = 0;
    let mut v_enabled_4239_: u8 = 0;
    let mut v_assignment_4240_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_lazyAssignment_4241_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4243_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4244_: u8 = 0;
    let mut v___x_4245_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4247_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4249_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4250_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4251_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4252_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4253_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4254_: u8 = 0;
    let mut v_unused_4255_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4256_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4223_ = lean_st_ref_get(v___y_4221_);
                v_infoState_4224_ = crate::leanh::lean_ctor_get(v___x_4223_, 7);
                crate::leanh::lean_inc_ref(v_infoState_4224_);
                crate::leanh::lean_dec(v___x_4223_);
                v_trees_4225_ = crate::leanh::lean_ctor_get(v_infoState_4224_, 2);
                crate::leanh::lean_inc_ref(v_trees_4225_);
                crate::leanh::lean_dec_ref(v_infoState_4224_);
                v___x_4226_ = lean_st_ref_take(v___y_4221_);
                v_infoState_4227_ = crate::leanh::lean_ctor_get(v___x_4226_, 7);
                v_env_4228_ = crate::leanh::lean_ctor_get(v___x_4226_, 0);
                v_nextMacroScope_4229_ = crate::leanh::lean_ctor_get(v___x_4226_, 1);
                v_ngen_4230_ = crate::leanh::lean_ctor_get(v___x_4226_, 2);
                v_auxDeclNGen_4231_ = crate::leanh::lean_ctor_get(v___x_4226_, 3);
                v_traceState_4232_ = crate::leanh::lean_ctor_get(v___x_4226_, 4);
                v_cache_4233_ = crate::leanh::lean_ctor_get(v___x_4226_, 5);
                v_messages_4234_ = crate::leanh::lean_ctor_get(v___x_4226_, 6);
                v_snapshotTasks_4235_ = crate::leanh::lean_ctor_get(v___x_4226_, 8);
                v_isSharedCheck_4256_ = (!crate::leanh::lean_is_exclusive(v___x_4226_)) as u8;
                if v_isSharedCheck_4256_ == 0 {
                    v___x_4237_ = v___x_4226_;
                    v_isShared_4238_ = v_isSharedCheck_4256_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snapshotTasks_4235_);
                    crate::leanh::lean_inc(v_infoState_4227_);
                    crate::leanh::lean_inc(v_messages_4234_);
                    crate::leanh::lean_inc(v_cache_4233_);
                    crate::leanh::lean_inc(v_traceState_4232_);
                    crate::leanh::lean_inc(v_auxDeclNGen_4231_);
                    crate::leanh::lean_inc(v_ngen_4230_);
                    crate::leanh::lean_inc(v_nextMacroScope_4229_);
                    crate::leanh::lean_inc(v_env_4228_);
                    crate::leanh::lean_dec(v___x_4226_);
                    v___x_4237_ = crate::leanh::lean_box(0);
                    v_isShared_4238_ = v_isSharedCheck_4256_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_enabled_4239_ = crate::leanh::lean_ctor_get_uint8(
                    v_infoState_4227_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u32,
                );
                v_assignment_4240_ = crate::leanh::lean_ctor_get(v_infoState_4227_, 0);
                v_lazyAssignment_4241_ = crate::leanh::lean_ctor_get(v_infoState_4227_, 1);
                v_isSharedCheck_4254_ = (!crate::leanh::lean_is_exclusive(v_infoState_4227_)) as u8;
                if v_isSharedCheck_4254_ == 0 {
                    v_unused_4255_ = crate::leanh::lean_ctor_get(v_infoState_4227_, 2);
                    crate::leanh::lean_dec(v_unused_4255_);
                    v___x_4243_ = v_infoState_4227_;
                    v_isShared_4244_ = v_isSharedCheck_4254_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_lazyAssignment_4241_);
                    crate::leanh::lean_inc(v_assignment_4240_);
                    crate::leanh::lean_dec(v_infoState_4227_);
                    v___x_4243_ = crate::leanh::lean_box(0);
                    v_isShared_4244_ = v_isSharedCheck_4254_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_4245_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__7___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__7___redArg___closed__1_once), _init_l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__7___redArg___closed__1);
                if v_isShared_4244_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4243_, 2, v___x_4245_);
                    v___x_4247_ = v___x_4243_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_4253_ = crate::leanh::lean_alloc_ctor(0, 3, (1) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4253_, 0, v_assignment_4240_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4253_, 1, v_lazyAssignment_4241_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4253_, 2, v___x_4245_);
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_4253_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u32,
                        v_enabled_4239_,
                    );
                    v___x_4247_ = v_reuseFailAlloc_4253_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_4238_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4237_, 7, v___x_4247_);
                    v___x_4249_ = v___x_4237_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4252_ = crate::leanh::lean_alloc_ctor(0, 9, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4252_, 0, v_env_4228_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4252_, 1, v_nextMacroScope_4229_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4252_, 2, v_ngen_4230_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4252_, 3, v_auxDeclNGen_4231_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4252_, 4, v_traceState_4232_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4252_, 5, v_cache_4233_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4252_, 6, v_messages_4234_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4252_, 7, v___x_4247_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4252_, 8, v_snapshotTasks_4235_);
                    v___x_4249_ = v_reuseFailAlloc_4252_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_4250_ = lean_st_ref_set(v___y_4221_, v___x_4249_);
                v___x_4251_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4251_, 0, v_trees_4225_);
                return v___x_4251_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__7___redArg___boxed(
    mut v___y_4257_: *mut crate::leanh::LeanObject,
    mut v___y_4258_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4259_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4259_ = l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__7___redArg(v___y_4257_);
    crate::leanh::lean_dec(v___y_4257_);
    return v_res_4259_;
}
pub unsafe fn l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__7(
    mut v___y_4260_: *mut crate::leanh::LeanObject,
    mut v___y_4261_: *mut crate::leanh::LeanObject,
    mut v___y_4262_: *mut crate::leanh::LeanObject,
    mut v___y_4263_: *mut crate::leanh::LeanObject,
    mut v___y_4264_: *mut crate::leanh::LeanObject,
    mut v___y_4265_: *mut crate::leanh::LeanObject,
    mut v___y_4266_: *mut crate::leanh::LeanObject,
    mut v___y_4267_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4269_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4269_ = l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__7___redArg(v___y_4267_);
    return v___x_4269_;
}
pub unsafe fn l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__7___boxed(
    mut v___y_4270_: *mut crate::leanh::LeanObject,
    mut v___y_4271_: *mut crate::leanh::LeanObject,
    mut v___y_4272_: *mut crate::leanh::LeanObject,
    mut v___y_4273_: *mut crate::leanh::LeanObject,
    mut v___y_4274_: *mut crate::leanh::LeanObject,
    mut v___y_4275_: *mut crate::leanh::LeanObject,
    mut v___y_4276_: *mut crate::leanh::LeanObject,
    mut v___y_4277_: *mut crate::leanh::LeanObject,
    mut v___y_4278_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4279_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4279_ = l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__7(v___y_4270_, v___y_4271_, v___y_4272_, v___y_4273_, v___y_4274_, v___y_4275_, v___y_4276_, v___y_4277_);
    crate::leanh::lean_dec(v___y_4277_);
    crate::leanh::lean_dec_ref(v___y_4276_);
    crate::leanh::lean_dec(v___y_4275_);
    crate::leanh::lean_dec_ref(v___y_4274_);
    crate::leanh::lean_dec(v___y_4273_);
    crate::leanh::lean_dec_ref(v___y_4272_);
    crate::leanh::lean_dec(v___y_4271_);
    crate::leanh::lean_dec_ref(v___y_4270_);
    return v_res_4279_;
}
pub unsafe fn l_panic___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__9(
    mut v_msg_4281_: *mut crate::leanh::LeanObject,
    mut v___y_4282_: *mut crate::leanh::LeanObject,
    mut v___y_4283_: *mut crate::leanh::LeanObject,
    mut v___y_4284_: *mut crate::leanh::LeanObject,
    mut v___y_4285_: *mut crate::leanh::LeanObject,
    mut v___y_4286_: *mut crate::leanh::LeanObject,
    mut v___y_4287_: *mut crate::leanh::LeanObject,
    mut v___y_4288_: *mut crate::leanh::LeanObject,
    mut v___y_4289_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_4291_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_80917__overap_4292_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4293_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_4291_ = l_panic___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__9___closed__0;
    v___x_80917__overap_4292_ = lean_panic_fn_borrowed(v___f_4291_, v_msg_4281_);
    crate::leanh::lean_inc(v___y_4289_);
    crate::leanh::lean_inc_ref(v___y_4288_);
    crate::leanh::lean_inc(v___y_4287_);
    crate::leanh::lean_inc_ref(v___y_4286_);
    crate::leanh::lean_inc(v___y_4285_);
    crate::leanh::lean_inc_ref(v___y_4284_);
    crate::leanh::lean_inc(v___y_4283_);
    crate::leanh::lean_inc_ref(v___y_4282_);
    v___x_4293_ = crate::leanh::lean_apply_9(
        v___x_80917__overap_4292_,
        v___y_4282_,
        v___y_4283_,
        v___y_4284_,
        v___y_4285_,
        v___y_4286_,
        v___y_4287_,
        v___y_4288_,
        v___y_4289_,
        crate::leanh::lean_box(0),
    );
    return v___x_4293_;
}
pub unsafe fn l_panic___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__9___boxed(
    mut v_msg_4294_: *mut crate::leanh::LeanObject,
    mut v___y_4295_: *mut crate::leanh::LeanObject,
    mut v___y_4296_: *mut crate::leanh::LeanObject,
    mut v___y_4297_: *mut crate::leanh::LeanObject,
    mut v___y_4298_: *mut crate::leanh::LeanObject,
    mut v___y_4299_: *mut crate::leanh::LeanObject,
    mut v___y_4300_: *mut crate::leanh::LeanObject,
    mut v___y_4301_: *mut crate::leanh::LeanObject,
    mut v___y_4302_: *mut crate::leanh::LeanObject,
    mut v___y_4303_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4304_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4304_ = l_panic___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__9(v_msg_4294_, v___y_4295_, v___y_4296_, v___y_4297_, v___y_4298_, v___y_4299_, v___y_4300_, v___y_4301_, v___y_4302_);
    crate::leanh::lean_dec(v___y_4302_);
    crate::leanh::lean_dec_ref(v___y_4301_);
    crate::leanh::lean_dec(v___y_4300_);
    crate::leanh::lean_dec_ref(v___y_4299_);
    crate::leanh::lean_dec(v___y_4298_);
    crate::leanh::lean_dec_ref(v___y_4297_);
    crate::leanh::lean_dec(v___y_4296_);
    crate::leanh::lean_dec_ref(v___y_4295_);
    return v_res_4304_;
}
pub unsafe fn l_Lean_Option_get___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__10(
    mut v_opts_4305_: *mut crate::leanh::LeanObject,
    mut v_opt_4306_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v_name_4307_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_defValue_4308_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_map_4309_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4310_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_name_4307_ = crate::leanh::lean_ctor_get(v_opt_4306_, 0);
    v_defValue_4308_ = crate::leanh::lean_ctor_get(v_opt_4306_, 1);
    v_map_4309_ = crate::leanh::lean_ctor_get(v_opts_4305_, 0);
    v___x_4310_ =
        l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(
            v_map_4309_,
            v_name_4307_,
        );
    if crate::leanh::lean_obj_tag(v___x_4310_) == 0 {
        let mut v___x_4311_: u8 = 0;
        v___x_4311_ = (crate::leanh::lean_unbox(v_defValue_4308_) as u8);
        return v___x_4311_;
    } else {
        let mut v_val_4312_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_val_4312_ = crate::leanh::lean_ctor_get(v___x_4310_, 0);
        crate::leanh::lean_inc(v_val_4312_);
        crate::leanh::lean_dec_ref_known(v___x_4310_, 1);
        if crate::leanh::lean_obj_tag(v_val_4312_) == 1 {
            let mut v_v_4313_: u8 = 0;
            v_v_4313_ = crate::leanh::lean_ctor_get_uint8(v_val_4312_, 0 as u32);
            crate::leanh::lean_dec_ref_known(v_val_4312_, 0);
            return v_v_4313_;
        } else {
            let mut v___x_4314_: u8 = 0;
            crate::leanh::lean_dec(v_val_4312_);
            v___x_4314_ = (crate::leanh::lean_unbox(v_defValue_4308_) as u8);
            return v___x_4314_;
        }
    }
}
pub unsafe fn l_Lean_Option_get___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__10___boxed(
    mut v_opts_4315_: *mut crate::leanh::LeanObject,
    mut v_opt_4316_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4317_: u8 = 0;
    let mut v_r_4318_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4317_ = l_Lean_Option_get___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__10(v_opts_4315_, v_opt_4316_);
    crate::leanh::lean_dec_ref(v_opt_4316_);
    crate::leanh::lean_dec_ref(v_opts_4315_);
    v_r_4318_ = crate::leanh::lean_box((v_res_4317_) as usize);
    return v_r_4318_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__0(
    mut v___y_4319_: *mut crate::leanh::LeanObject,
    mut v___y_4320_: *mut crate::leanh::LeanObject,
    mut v___y_4321_: *mut crate::leanh::LeanObject,
    mut v___y_4322_: *mut crate::leanh::LeanObject,
    mut v___y_4323_: *mut crate::leanh::LeanObject,
    mut v___y_4324_: *mut crate::leanh::LeanObject,
    mut v___y_4325_: *mut crate::leanh::LeanObject,
    mut v___y_4326_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_ref_4328_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4329_: u8 = 0;
    let mut v___x_4330_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4331_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_ref_4328_ = crate::leanh::lean_ctor_get(v___y_4325_, 5);
    v___x_4329_ = 0;
    v___x_4330_ = l_Lean_SourceInfo_fromRef(v_ref_4328_, v___x_4329_);
    v___x_4331_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_4331_, 0, v___x_4330_);
    return v___x_4331_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__0___boxed(
    mut v___y_4332_: *mut crate::leanh::LeanObject,
    mut v___y_4333_: *mut crate::leanh::LeanObject,
    mut v___y_4334_: *mut crate::leanh::LeanObject,
    mut v___y_4335_: *mut crate::leanh::LeanObject,
    mut v___y_4336_: *mut crate::leanh::LeanObject,
    mut v___y_4337_: *mut crate::leanh::LeanObject,
    mut v___y_4338_: *mut crate::leanh::LeanObject,
    mut v___y_4339_: *mut crate::leanh::LeanObject,
    mut v___y_4340_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4341_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4341_ =
        l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__0(
            v___y_4332_,
            v___y_4333_,
            v___y_4334_,
            v___y_4335_,
            v___y_4336_,
            v___y_4337_,
            v___y_4338_,
            v___y_4339_,
        );
    crate::leanh::lean_dec(v___y_4339_);
    crate::leanh::lean_dec_ref(v___y_4338_);
    crate::leanh::lean_dec(v___y_4337_);
    crate::leanh::lean_dec_ref(v___y_4336_);
    crate::leanh::lean_dec(v___y_4335_);
    crate::leanh::lean_dec_ref(v___y_4334_);
    crate::leanh::lean_dec(v___y_4333_);
    crate::leanh::lean_dec_ref(v___y_4332_);
    return v_res_4341_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__1(
    mut v_a_4342_: *mut crate::leanh::LeanObject,
    mut v_trees_4343_: *mut crate::leanh::LeanObject,
    mut v___y_4344_: *mut crate::leanh::LeanObject,
    mut v___y_4345_: *mut crate::leanh::LeanObject,
    mut v___y_4346_: *mut crate::leanh::LeanObject,
    mut v___y_4347_: *mut crate::leanh::LeanObject,
    mut v___y_4348_: *mut crate::leanh::LeanObject,
    mut v___y_4349_: *mut crate::leanh::LeanObject,
    mut v___y_4350_: *mut crate::leanh::LeanObject,
    mut v___y_4351_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4353_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4354_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4356_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4357_: u8 = 0;
    let mut v___x_4358_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4360_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4361_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4362_: u8 = 0;
    let mut v_a_4363_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4365_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4366_: u8 = 0;
    let mut v___x_4368_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4369_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4370_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                crate::leanh::lean_inc(v___y_4351_);
                crate::leanh::lean_inc_ref(v___y_4350_);
                crate::leanh::lean_inc(v___y_4349_);
                crate::leanh::lean_inc_ref(v___y_4348_);
                crate::leanh::lean_inc(v___y_4347_);
                crate::leanh::lean_inc_ref(v___y_4346_);
                crate::leanh::lean_inc(v___y_4345_);
                crate::leanh::lean_inc_ref(v___y_4344_);
                v___x_4353_ = crate::leanh::lean_apply_9(
                    v_a_4342_,
                    v___y_4344_,
                    v___y_4345_,
                    v___y_4346_,
                    v___y_4347_,
                    v___y_4348_,
                    v___y_4349_,
                    v___y_4350_,
                    v___y_4351_,
                    crate::leanh::lean_box(0),
                );
                if crate::leanh::lean_obj_tag(v___x_4353_) == 0 {
                    v_a_4354_ = crate::leanh::lean_ctor_get(v___x_4353_, 0);
                    v_isSharedCheck_4362_ = (!crate::leanh::lean_is_exclusive(v___x_4353_)) as u8;
                    if v_isSharedCheck_4362_ == 0 {
                        v___x_4356_ = v___x_4353_;
                        v_isShared_4357_ = v_isSharedCheck_4362_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4354_);
                        crate::leanh::lean_dec(v___x_4353_);
                        v___x_4356_ = crate::leanh::lean_box(0);
                        v_isShared_4357_ = v_isSharedCheck_4362_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_trees_4343_);
                    v_a_4363_ = crate::leanh::lean_ctor_get(v___x_4353_, 0);
                    v_isSharedCheck_4370_ = (!crate::leanh::lean_is_exclusive(v___x_4353_)) as u8;
                    if v_isSharedCheck_4370_ == 0 {
                        v___x_4365_ = v___x_4353_;
                        v_isShared_4366_ = v_isSharedCheck_4370_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4363_);
                        crate::leanh::lean_dec(v___x_4353_);
                        v___x_4365_ = crate::leanh::lean_box(0);
                        v_isShared_4366_ = v_isSharedCheck_4370_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v___x_4358_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4358_, 0, v_a_4354_);
                crate::leanh::lean_ctor_set(v___x_4358_, 1, v_trees_4343_);
                if v_isShared_4357_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4356_, 0, v___x_4358_);
                    v___x_4360_ = v___x_4356_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4361_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4361_, 0, v___x_4358_);
                    v___x_4360_ = v_reuseFailAlloc_4361_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_4360_;
            }
            3 => {
                if v_isShared_4366_ == 0 {
                    v___x_4368_ = v___x_4365_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4369_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4369_, 0, v_a_4363_);
                    v___x_4368_ = v_reuseFailAlloc_4369_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_4368_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__1___boxed(
    mut v_a_4371_: *mut crate::leanh::LeanObject,
    mut v_trees_4372_: *mut crate::leanh::LeanObject,
    mut v___y_4373_: *mut crate::leanh::LeanObject,
    mut v___y_4374_: *mut crate::leanh::LeanObject,
    mut v___y_4375_: *mut crate::leanh::LeanObject,
    mut v___y_4376_: *mut crate::leanh::LeanObject,
    mut v___y_4377_: *mut crate::leanh::LeanObject,
    mut v___y_4378_: *mut crate::leanh::LeanObject,
    mut v___y_4379_: *mut crate::leanh::LeanObject,
    mut v___y_4380_: *mut crate::leanh::LeanObject,
    mut v___y_4381_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4382_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4382_ =
        l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__1(
            v_a_4371_,
            v_trees_4372_,
            v___y_4373_,
            v___y_4374_,
            v___y_4375_,
            v___y_4376_,
            v___y_4377_,
            v___y_4378_,
            v___y_4379_,
            v___y_4380_,
        );
    crate::leanh::lean_dec(v___y_4380_);
    crate::leanh::lean_dec_ref(v___y_4379_);
    crate::leanh::lean_dec(v___y_4378_);
    crate::leanh::lean_dec_ref(v___y_4377_);
    crate::leanh::lean_dec(v___y_4376_);
    crate::leanh::lean_dec_ref(v___y_4375_);
    crate::leanh::lean_dec(v___y_4374_);
    crate::leanh::lean_dec_ref(v___y_4373_);
    return v_res_4382_;
}
pub unsafe fn _init_l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__2___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4384_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4385_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4384_ = l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__2___closed__0;
    v___x_4385_ = l_Lean_stringToMessageData(v___x_4384_);
    return v___x_4385_;
}
pub unsafe fn _init_l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__2___closed__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4387_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4388_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4387_ = l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__2___closed__2;
    v___x_4388_ = l_Lean_stringToMessageData(v___x_4387_);
    return v___x_4388_;
}
pub unsafe fn _init_l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__2___closed__4()
-> u64 {
    let mut v___x_4389_: u8 = 0;
    let mut v___x_4390_: u64 = 0;
    v___x_4389_ = 2;
    v___x_4390_ = l_Lean_Meta_TransparencyMode_toUInt64(v___x_4389_);
    return v___x_4390_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__2(
    mut v_a_4391_: *mut crate::leanh::LeanObject,
    mut v_a_4392_: *mut crate::leanh::LeanObject,
    mut v___x_4393_: u8,
    mut v___x_4394_: u8,
    mut v_a_4395_: *mut crate::leanh::LeanObject,
    mut v_mvarCounter_4396_: *mut crate::leanh::LeanObject,
    mut v___x_4397_: *mut crate::leanh::LeanObject,
    mut v___x_4398_: *mut crate::leanh::LeanObject,
    mut v_useReducible_4399_: u8,
    mut v___x_4400_: u8,
    mut v___y_4401_: *mut crate::leanh::LeanObject,
    mut v___y_4402_: *mut crate::leanh::LeanObject,
    mut v___y_4403_: *mut crate::leanh::LeanObject,
    mut v___y_4404_: *mut crate::leanh::LeanObject,
    mut v___y_4405_: *mut crate::leanh::LeanObject,
    mut v___y_4406_: *mut crate::leanh::LeanObject,
    mut v___y_4407_: *mut crate::leanh::LeanObject,
    mut v___y_4408_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4410_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4411_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4412_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4413_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4414_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4415_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4417_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4418_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4419_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4420_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4421_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4422_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4423_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4424_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4425_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4426_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4427_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4428_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4429_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4430_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4431_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4432_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4433_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4435_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4436_: u8 = 0;
    let mut v___x_4438_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4439_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4440_: u8 = 0;
    let mut v_a_4441_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4443_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4444_: u8 = 0;
    let mut v___x_4446_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4447_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4448_: u8 = 0;
    let mut v___x_4449_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4451_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4452_: u8 = 0;
    let mut v___x_4453_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4454_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4456_: u8 = 0;
    let mut v___x_4457_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4458_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4459_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4460_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4461_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4463_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4464_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4465_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4467_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4468_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4469_: u8 = 0;
    let mut v_a_4470_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4472_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4473_: u8 = 0;
    let mut v___x_4475_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4476_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4477_: u8 = 0;
    let mut v___x_4478_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_foApprox_4479_: u8 = 0;
    let mut v_ctxApprox_4480_: u8 = 0;
    let mut v_quasiPatternApprox_4481_: u8 = 0;
    let mut v_constApprox_4482_: u8 = 0;
    let mut v_isDefEqStuckEx_4483_: u8 = 0;
    let mut v_unificationHints_4484_: u8 = 0;
    let mut v_proofIrrelevance_4485_: u8 = 0;
    let mut v_offsetCnstrs_4486_: u8 = 0;
    let mut v_transparency_4487_: u8 = 0;
    let mut v_etaStruct_4488_: u8 = 0;
    let mut v_univApprox_4489_: u8 = 0;
    let mut v_iota_4490_: u8 = 0;
    let mut v_beta_4491_: u8 = 0;
    let mut v_proj_4492_: u8 = 0;
    let mut v_zeta_4493_: u8 = 0;
    let mut v_zetaDelta_4494_: u8 = 0;
    let mut v_zetaUnused_4495_: u8 = 0;
    let mut v_zetaHave_4496_: u8 = 0;
    let mut v___x_4498_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4499_: u8 = 0;
    let mut v_trackZetaDelta_4500_: u8 = 0;
    let mut v_zetaDeltaSet_4501_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_lctx_4502_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_localInstances_4503_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_defEqCtx_x3f_4504_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_synthPendingDepth_4505_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_canUnfold_x3f_4506_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_univApprox_4507_: u8 = 0;
    let mut v_inTypeClassResolution_4508_: u8 = 0;
    let mut v_cacheInferType_4509_: u8 = 0;
    let mut v___x_4511_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4512_: u64 = 0;
    let mut v___x_4513_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4514_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4515_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4516_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4517_: u8 = 0;
    let mut v___x_4518_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_foApprox_4519_: u8 = 0;
    let mut v_ctxApprox_4520_: u8 = 0;
    let mut v_quasiPatternApprox_4521_: u8 = 0;
    let mut v_constApprox_4522_: u8 = 0;
    let mut v_isDefEqStuckEx_4523_: u8 = 0;
    let mut v_unificationHints_4524_: u8 = 0;
    let mut v_proofIrrelevance_4525_: u8 = 0;
    let mut v_assignSyntheticOpaque_4526_: u8 = 0;
    let mut v_offsetCnstrs_4527_: u8 = 0;
    let mut v_etaStruct_4528_: u8 = 0;
    let mut v_univApprox_4529_: u8 = 0;
    let mut v_iota_4530_: u8 = 0;
    let mut v_beta_4531_: u8 = 0;
    let mut v_proj_4532_: u8 = 0;
    let mut v_zeta_4533_: u8 = 0;
    let mut v_zetaDelta_4534_: u8 = 0;
    let mut v_zetaUnused_4535_: u8 = 0;
    let mut v_zetaHave_4536_: u8 = 0;
    let mut v___x_4538_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4539_: u8 = 0;
    let mut v_trackZetaDelta_4540_: u8 = 0;
    let mut v_zetaDeltaSet_4541_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_lctx_4542_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_localInstances_4543_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_defEqCtx_x3f_4544_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_synthPendingDepth_4545_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_canUnfold_x3f_4546_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_univApprox_4547_: u8 = 0;
    let mut v_inTypeClassResolution_4548_: u8 = 0;
    let mut v_cacheInferType_4549_: u8 = 0;
    let mut v___x_4550_: u8 = 0;
    let mut v_config_4552_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4553_: u64 = 0;
    let mut v___x_4554_: u64 = 0;
    let mut v___x_4555_: u64 = 0;
    let mut v___x_4556_: u64 = 0;
    let mut v___x_4557_: u64 = 0;
    let mut v_key_4558_: u64 = 0;
    let mut v___x_4559_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4560_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4561_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_foApprox_4562_: u8 = 0;
    let mut v_ctxApprox_4563_: u8 = 0;
    let mut v_quasiPatternApprox_4564_: u8 = 0;
    let mut v_constApprox_4565_: u8 = 0;
    let mut v_isDefEqStuckEx_4566_: u8 = 0;
    let mut v_unificationHints_4567_: u8 = 0;
    let mut v_proofIrrelevance_4568_: u8 = 0;
    let mut v_offsetCnstrs_4569_: u8 = 0;
    let mut v_transparency_4570_: u8 = 0;
    let mut v_etaStruct_4571_: u8 = 0;
    let mut v_univApprox_4572_: u8 = 0;
    let mut v_iota_4573_: u8 = 0;
    let mut v_beta_4574_: u8 = 0;
    let mut v_proj_4575_: u8 = 0;
    let mut v_zeta_4576_: u8 = 0;
    let mut v_zetaDelta_4577_: u8 = 0;
    let mut v_zetaUnused_4578_: u8 = 0;
    let mut v_zetaHave_4579_: u8 = 0;
    let mut v___x_4581_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4582_: u8 = 0;
    let mut v___x_4584_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4585_: u64 = 0;
    let mut v___x_4586_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4587_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4588_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4589_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4590_: u8 = 0;
    let mut v_reuseFailAlloc_4591_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4592_: u8 = 0;
    let mut v_reuseFailAlloc_4593_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4594_: u8 = 0;
    let mut v_a_4595_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4597_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4598_: u8 = 0;
    let mut v___x_4600_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4601_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4602_: u8 = 0;
    let mut v_isSharedCheck_4603_: u8 = 0;
    let mut v_unused_4604_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
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
    let mut state = 0;
    loop {
        match state {
            0 => {
                crate::leanh::lean_inc(v_a_4391_);
                v___x_4410_ = l_Lean_MVarId_getType(
                    v_a_4391_,
                    v___y_4405_,
                    v___y_4406_,
                    v___y_4407_,
                    v___y_4408_,
                );
                if crate::leanh::lean_obj_tag(v___x_4410_) == 0 {
                    v_a_4411_ = crate::leanh::lean_ctor_get(v___x_4410_, 0);
                    crate::leanh::lean_inc_n(v_a_4411_, 2);
                    crate::leanh::lean_dec_ref_known(v___x_4410_, 1);
                    v___x_4412_ = lean_mk_syntax_ident(v_a_4392_);
                    v___x_4413_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_4413_, 0, v_a_4411_);
                    v___x_4414_ = l_Lean_Elab_Term_elabTerm(
                        v___x_4412_,
                        v___x_4413_,
                        v___x_4393_,
                        v___x_4393_,
                        v___y_4403_,
                        v___y_4404_,
                        v___y_4405_,
                        v___y_4406_,
                        v___y_4407_,
                        v___y_4408_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_4414_) == 0 {
                        v_a_4415_ = crate::leanh::lean_ctor_get(v___x_4414_, 0);
                        crate::leanh::lean_inc(v_a_4415_);
                        crate::leanh::lean_dec_ref_known(v___x_4414_, 1);
                        v___x_4449_ = l_Lean_Elab_Term_synthesizeSyntheticMVarsNoPostponing(
                            v___x_4394_,
                            v___y_4403_,
                            v___y_4404_,
                            v___y_4405_,
                            v___y_4406_,
                            v___y_4407_,
                            v___y_4408_,
                        );
                        if crate::leanh::lean_obj_tag(v___x_4449_) == 0 {
                            v_isSharedCheck_4603_ =
                                (!crate::leanh::lean_is_exclusive(v___x_4449_)) as u8;
                            if v_isSharedCheck_4603_ == 0 {
                                v_unused_4604_ = crate::leanh::lean_ctor_get(v___x_4449_, 0);
                                crate::leanh::lean_dec(v_unused_4604_);
                                v___x_4451_ = v___x_4449_;
                                v_isShared_4452_ = v_isSharedCheck_4603_;
                                state = 6;
                                continue;
                            } else {
                                crate::leanh::lean_dec(v___x_4449_);
                                v___x_4451_ = crate::leanh::lean_box(0);
                                v_isShared_4452_ = v_isSharedCheck_4603_;
                                state = 6;
                                continue;
                            }
                        } else {
                            crate::leanh::lean_dec(v_a_4415_);
                            crate::leanh::lean_dec(v_a_4411_);
                            crate::leanh::lean_dec(v___y_4408_);
                            crate::leanh::lean_dec_ref(v___y_4407_);
                            crate::leanh::lean_dec(v___y_4406_);
                            crate::leanh::lean_dec_ref(v___y_4405_);
                            crate::leanh::lean_dec(v___x_4398_);
                            crate::leanh::lean_dec_ref(v___x_4397_);
                            crate::leanh::lean_dec_ref(v_a_4395_);
                            crate::leanh::lean_dec(v_a_4391_);
                            return v___x_4449_;
                        }
                    } else {
                        crate::leanh::lean_dec(v_a_4411_);
                        crate::leanh::lean_dec(v___y_4408_);
                        crate::leanh::lean_dec_ref(v___y_4407_);
                        crate::leanh::lean_dec(v___y_4406_);
                        crate::leanh::lean_dec_ref(v___y_4405_);
                        crate::leanh::lean_dec(v___x_4398_);
                        crate::leanh::lean_dec_ref(v___x_4397_);
                        crate::leanh::lean_dec_ref(v_a_4395_);
                        crate::leanh::lean_dec(v_a_4391_);
                        v_a_4605_ = crate::leanh::lean_ctor_get(v___x_4414_, 0);
                        v_isSharedCheck_4612_ =
                            (!crate::leanh::lean_is_exclusive(v___x_4414_)) as u8;
                        if v_isSharedCheck_4612_ == 0 {
                            v___x_4607_ = v___x_4414_;
                            v_isShared_4608_ = v_isSharedCheck_4612_;
                            state = 20;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_4605_);
                            crate::leanh::lean_dec(v___x_4414_);
                            v___x_4607_ = crate::leanh::lean_box(0);
                            v_isShared_4608_ = v_isSharedCheck_4612_;
                            state = 20;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec(v___y_4408_);
                    crate::leanh::lean_dec_ref(v___y_4407_);
                    crate::leanh::lean_dec(v___y_4406_);
                    crate::leanh::lean_dec_ref(v___y_4405_);
                    crate::leanh::lean_dec(v___x_4398_);
                    crate::leanh::lean_dec_ref(v___x_4397_);
                    crate::leanh::lean_dec_ref(v_a_4395_);
                    crate::leanh::lean_dec(v_a_4392_);
                    crate::leanh::lean_dec(v_a_4391_);
                    v_a_4613_ = crate::leanh::lean_ctor_get(v___x_4410_, 0);
                    v_isSharedCheck_4620_ = (!crate::leanh::lean_is_exclusive(v___x_4410_)) as u8;
                    if v_isSharedCheck_4620_ == 0 {
                        v___x_4615_ = v___x_4410_;
                        v_isShared_4616_ = v_isSharedCheck_4620_;
                        state = 22;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4613_);
                        crate::leanh::lean_dec(v___x_4410_);
                        v___x_4615_ = crate::leanh::lean_box(0);
                        v_isShared_4616_ = v_isSharedCheck_4620_;
                        state = 22;
                        continue;
                    }
                }
            }
            1 => {
                v___x_4425_ = l_Lean_Meta_getMVars(
                    v_a_4395_,
                    v___y_4421_,
                    v___y_4422_,
                    v___y_4423_,
                    v___y_4424_,
                );
                if crate::leanh::lean_obj_tag(v___x_4425_) == 0 {
                    v_a_4426_ = crate::leanh::lean_ctor_get(v___x_4425_, 0);
                    crate::leanh::lean_inc(v_a_4426_);
                    crate::leanh::lean_dec_ref_known(v___x_4425_, 1);
                    v___x_4427_ = l_Lean_Elab_Tactic_filterOldMVars___redArg(
                        v_a_4426_,
                        v_mvarCounter_4396_,
                        v___y_4422_,
                    );
                    crate::leanh::lean_dec(v_a_4426_);
                    if crate::leanh::lean_obj_tag(v___x_4427_) == 0 {
                        v_a_4428_ = crate::leanh::lean_ctor_get(v___x_4427_, 0);
                        crate::leanh::lean_inc(v_a_4428_);
                        crate::leanh::lean_dec_ref_known(v___x_4427_, 1);
                        v___x_4429_ = l_Lean_Elab_Tactic_logUnassignedAndAbort(
                            v_a_4428_,
                            v___y_4417_,
                            v___y_4418_,
                            v___y_4419_,
                            v___y_4420_,
                            v___y_4421_,
                            v___y_4422_,
                            v___y_4423_,
                            v___y_4424_,
                        );
                        crate::leanh::lean_dec(v_a_4428_);
                        if crate::leanh::lean_obj_tag(v___x_4429_) == 0 {
                            crate::leanh::lean_dec_ref_known(v___x_4429_, 1);
                            v___x_4430_ =
                                l_Lean_Elab_Tactic_pushGoal___redArg(v_a_4391_, v___y_4418_);
                            if crate::leanh::lean_obj_tag(v___x_4430_) == 0 {
                                crate::leanh::lean_dec_ref_known(v___x_4430_, 1);
                                v___x_4431_ = l_Lean_Name_mkStr1(v___x_4397_);
                                v___x_4432_ = l_Lean_Elab_Tactic_closeMainGoal___redArg(
                                    v___x_4431_,
                                    v_a_4415_,
                                    v___x_4394_,
                                    v___y_4418_,
                                    v___y_4419_,
                                    v___y_4420_,
                                    v___y_4421_,
                                    v___y_4422_,
                                    v___y_4423_,
                                    v___y_4424_,
                                );
                                crate::leanh::lean_dec(v___y_4424_);
                                crate::leanh::lean_dec_ref(v___y_4423_);
                                crate::leanh::lean_dec(v___y_4422_);
                                crate::leanh::lean_dec_ref(v___y_4421_);
                                return v___x_4432_;
                            } else {
                                crate::leanh::lean_dec(v___y_4424_);
                                crate::leanh::lean_dec_ref(v___y_4423_);
                                crate::leanh::lean_dec(v___y_4422_);
                                crate::leanh::lean_dec_ref(v___y_4421_);
                                crate::leanh::lean_dec(v_a_4415_);
                                crate::leanh::lean_dec_ref(v___x_4397_);
                                return v___x_4430_;
                            }
                        } else {
                            crate::leanh::lean_dec(v___y_4424_);
                            crate::leanh::lean_dec_ref(v___y_4423_);
                            crate::leanh::lean_dec(v___y_4422_);
                            crate::leanh::lean_dec_ref(v___y_4421_);
                            crate::leanh::lean_dec(v_a_4415_);
                            crate::leanh::lean_dec_ref(v___x_4397_);
                            crate::leanh::lean_dec(v_a_4391_);
                            return v___x_4429_;
                        }
                    } else {
                        crate::leanh::lean_dec(v___y_4424_);
                        crate::leanh::lean_dec_ref(v___y_4423_);
                        crate::leanh::lean_dec(v___y_4422_);
                        crate::leanh::lean_dec_ref(v___y_4421_);
                        crate::leanh::lean_dec(v_a_4415_);
                        crate::leanh::lean_dec_ref(v___x_4397_);
                        crate::leanh::lean_dec(v_a_4391_);
                        v_a_4433_ = crate::leanh::lean_ctor_get(v___x_4427_, 0);
                        v_isSharedCheck_4440_ =
                            (!crate::leanh::lean_is_exclusive(v___x_4427_)) as u8;
                        if v_isSharedCheck_4440_ == 0 {
                            v___x_4435_ = v___x_4427_;
                            v_isShared_4436_ = v_isSharedCheck_4440_;
                            state = 2;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_4433_);
                            crate::leanh::lean_dec(v___x_4427_);
                            v___x_4435_ = crate::leanh::lean_box(0);
                            v_isShared_4436_ = v_isSharedCheck_4440_;
                            state = 2;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec(v___y_4424_);
                    crate::leanh::lean_dec_ref(v___y_4423_);
                    crate::leanh::lean_dec(v___y_4422_);
                    crate::leanh::lean_dec_ref(v___y_4421_);
                    crate::leanh::lean_dec(v_a_4415_);
                    crate::leanh::lean_dec_ref(v___x_4397_);
                    crate::leanh::lean_dec(v_a_4391_);
                    v_a_4441_ = crate::leanh::lean_ctor_get(v___x_4425_, 0);
                    v_isSharedCheck_4448_ = (!crate::leanh::lean_is_exclusive(v___x_4425_)) as u8;
                    if v_isSharedCheck_4448_ == 0 {
                        v___x_4443_ = v___x_4425_;
                        v_isShared_4444_ = v_isSharedCheck_4448_;
                        state = 4;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4441_);
                        crate::leanh::lean_dec(v___x_4425_);
                        v___x_4443_ = crate::leanh::lean_box(0);
                        v_isShared_4444_ = v_isSharedCheck_4448_;
                        state = 4;
                        continue;
                    }
                }
            }
            2 => {
                if v_isShared_4436_ == 0 {
                    v___x_4438_ = v___x_4435_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_4439_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4439_, 0, v_a_4433_);
                    v___x_4438_ = v_reuseFailAlloc_4439_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_4438_;
            }
            4 => {
                if v_isShared_4444_ == 0 {
                    v___x_4446_ = v___x_4443_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_4447_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4447_, 0, v_a_4441_);
                    v___x_4446_ = v_reuseFailAlloc_4447_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_4446_;
            }
            6 => {
                crate::leanh::lean_inc(v___y_4408_);
                crate::leanh::lean_inc_ref(v___y_4407_);
                crate::leanh::lean_inc(v___y_4406_);
                crate::leanh::lean_inc_ref(v___y_4405_);
                crate::leanh::lean_inc(v_a_4415_);
                v___x_4453_ = lean_infer_type(
                    v_a_4415_,
                    v___y_4405_,
                    v___y_4406_,
                    v___y_4407_,
                    v___y_4408_,
                );
                if crate::leanh::lean_obj_tag(v___x_4453_) == 0 {
                    v_a_4454_ = crate::leanh::lean_ctor_get(v___x_4453_, 0);
                    crate::leanh::lean_inc(v_a_4454_);
                    crate::leanh::lean_dec_ref_known(v___x_4453_, 1);
                    if v_useReducible_4399_ == 0 {
                        v___x_4478_ = l_Lean_Meta_Context_config(v___y_4405_);
                        v_foApprox_4479_ = crate::leanh::lean_ctor_get_uint8(v___x_4478_, 0 as u32);
                        v_ctxApprox_4480_ =
                            crate::leanh::lean_ctor_get_uint8(v___x_4478_, 1 as u32);
                        v_quasiPatternApprox_4481_ =
                            crate::leanh::lean_ctor_get_uint8(v___x_4478_, 2 as u32);
                        v_constApprox_4482_ =
                            crate::leanh::lean_ctor_get_uint8(v___x_4478_, 3 as u32);
                        v_isDefEqStuckEx_4483_ =
                            crate::leanh::lean_ctor_get_uint8(v___x_4478_, 4 as u32);
                        v_unificationHints_4484_ =
                            crate::leanh::lean_ctor_get_uint8(v___x_4478_, 5 as u32);
                        v_proofIrrelevance_4485_ =
                            crate::leanh::lean_ctor_get_uint8(v___x_4478_, 6 as u32);
                        v_offsetCnstrs_4486_ =
                            crate::leanh::lean_ctor_get_uint8(v___x_4478_, 8 as u32);
                        v_transparency_4487_ =
                            crate::leanh::lean_ctor_get_uint8(v___x_4478_, 9 as u32);
                        v_etaStruct_4488_ =
                            crate::leanh::lean_ctor_get_uint8(v___x_4478_, 10 as u32);
                        v_univApprox_4489_ =
                            crate::leanh::lean_ctor_get_uint8(v___x_4478_, 11 as u32);
                        v_iota_4490_ = crate::leanh::lean_ctor_get_uint8(v___x_4478_, 12 as u32);
                        v_beta_4491_ = crate::leanh::lean_ctor_get_uint8(v___x_4478_, 13 as u32);
                        v_proj_4492_ = crate::leanh::lean_ctor_get_uint8(v___x_4478_, 14 as u32);
                        v_zeta_4493_ = crate::leanh::lean_ctor_get_uint8(v___x_4478_, 15 as u32);
                        v_zetaDelta_4494_ =
                            crate::leanh::lean_ctor_get_uint8(v___x_4478_, 16 as u32);
                        v_zetaUnused_4495_ =
                            crate::leanh::lean_ctor_get_uint8(v___x_4478_, 17 as u32);
                        v_zetaHave_4496_ =
                            crate::leanh::lean_ctor_get_uint8(v___x_4478_, 18 as u32);
                        v_isSharedCheck_4517_ =
                            (!crate::leanh::lean_is_exclusive(v___x_4478_)) as u8;
                        if v_isSharedCheck_4517_ == 0 {
                            v___x_4498_ = v___x_4478_;
                            v_isShared_4499_ = v_isSharedCheck_4517_;
                            state = 12;
                            continue;
                        } else {
                            crate::leanh::lean_dec(v___x_4478_);
                            v___x_4498_ = crate::leanh::lean_box(0);
                            v_isShared_4499_ = v_isSharedCheck_4517_;
                            state = 12;
                            continue;
                        }
                    } else {
                        v___x_4518_ = l_Lean_Meta_Context_config(v___y_4405_);
                        v_foApprox_4519_ = crate::leanh::lean_ctor_get_uint8(v___x_4518_, 0 as u32);
                        v_ctxApprox_4520_ =
                            crate::leanh::lean_ctor_get_uint8(v___x_4518_, 1 as u32);
                        v_quasiPatternApprox_4521_ =
                            crate::leanh::lean_ctor_get_uint8(v___x_4518_, 2 as u32);
                        v_constApprox_4522_ =
                            crate::leanh::lean_ctor_get_uint8(v___x_4518_, 3 as u32);
                        v_isDefEqStuckEx_4523_ =
                            crate::leanh::lean_ctor_get_uint8(v___x_4518_, 4 as u32);
                        v_unificationHints_4524_ =
                            crate::leanh::lean_ctor_get_uint8(v___x_4518_, 5 as u32);
                        v_proofIrrelevance_4525_ =
                            crate::leanh::lean_ctor_get_uint8(v___x_4518_, 6 as u32);
                        v_assignSyntheticOpaque_4526_ =
                            crate::leanh::lean_ctor_get_uint8(v___x_4518_, 7 as u32);
                        v_offsetCnstrs_4527_ =
                            crate::leanh::lean_ctor_get_uint8(v___x_4518_, 8 as u32);
                        v_etaStruct_4528_ =
                            crate::leanh::lean_ctor_get_uint8(v___x_4518_, 10 as u32);
                        v_univApprox_4529_ =
                            crate::leanh::lean_ctor_get_uint8(v___x_4518_, 11 as u32);
                        v_iota_4530_ = crate::leanh::lean_ctor_get_uint8(v___x_4518_, 12 as u32);
                        v_beta_4531_ = crate::leanh::lean_ctor_get_uint8(v___x_4518_, 13 as u32);
                        v_proj_4532_ = crate::leanh::lean_ctor_get_uint8(v___x_4518_, 14 as u32);
                        v_zeta_4533_ = crate::leanh::lean_ctor_get_uint8(v___x_4518_, 15 as u32);
                        v_zetaDelta_4534_ =
                            crate::leanh::lean_ctor_get_uint8(v___x_4518_, 16 as u32);
                        v_zetaUnused_4535_ =
                            crate::leanh::lean_ctor_get_uint8(v___x_4518_, 17 as u32);
                        v_zetaHave_4536_ =
                            crate::leanh::lean_ctor_get_uint8(v___x_4518_, 18 as u32);
                        v_isSharedCheck_4594_ =
                            (!crate::leanh::lean_is_exclusive(v___x_4518_)) as u8;
                        if v_isSharedCheck_4594_ == 0 {
                            v___x_4538_ = v___x_4518_;
                            v_isShared_4539_ = v_isSharedCheck_4594_;
                            state = 14;
                            continue;
                        } else {
                            crate::leanh::lean_dec(v___x_4518_);
                            v___x_4538_ = crate::leanh::lean_box(0);
                            v_isShared_4539_ = v_isSharedCheck_4594_;
                            state = 14;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_4451_);
                    crate::leanh::lean_dec(v_a_4415_);
                    crate::leanh::lean_dec(v_a_4411_);
                    crate::leanh::lean_dec(v___y_4408_);
                    crate::leanh::lean_dec_ref(v___y_4407_);
                    crate::leanh::lean_dec(v___y_4406_);
                    crate::leanh::lean_dec_ref(v___y_4405_);
                    crate::leanh::lean_dec(v___x_4398_);
                    crate::leanh::lean_dec_ref(v___x_4397_);
                    crate::leanh::lean_dec_ref(v_a_4395_);
                    crate::leanh::lean_dec(v_a_4391_);
                    v_a_4595_ = crate::leanh::lean_ctor_get(v___x_4453_, 0);
                    v_isSharedCheck_4602_ = (!crate::leanh::lean_is_exclusive(v___x_4453_)) as u8;
                    if v_isSharedCheck_4602_ == 0 {
                        v___x_4597_ = v___x_4453_;
                        v_isShared_4598_ = v_isSharedCheck_4602_;
                        state = 18;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4595_);
                        crate::leanh::lean_dec(v___x_4453_);
                        v___x_4597_ = crate::leanh::lean_box(0);
                        v_isShared_4598_ = v_isSharedCheck_4602_;
                        state = 18;
                        continue;
                    }
                }
            }
            7 => {
                if v_a_4456_ == 0 {
                    v___x_4457_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__2___closed__1), core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__2___closed__1_once), _init_l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__2___closed__1);
                    crate::leanh::lean_inc_ref(v_a_4395_);
                    v___x_4458_ = l_Lean_indentExpr(v_a_4395_);
                    v___x_4459_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_4459_, 0, v___x_4457_);
                    crate::leanh::lean_ctor_set(v___x_4459_, 1, v___x_4458_);
                    v___x_4460_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__2___closed__3), core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__2___closed__3_once), _init_l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__2___closed__3);
                    v___x_4461_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_4461_, 0, v___x_4459_);
                    crate::leanh::lean_ctor_set(v___x_4461_, 1, v___x_4460_);
                    if v_isShared_4452_ == 0 {
                        crate::leanh::lean_ctor_set_tag(v___x_4451_, 1);
                        crate::leanh::lean_ctor_set(v___x_4451_, 0, v___x_4461_);
                        v___x_4463_ = v___x_4451_;
                        state = 8;
                        continue;
                    } else {
                        v_reuseFailAlloc_4465_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4465_, 0, v___x_4461_);
                        v___x_4463_ = v_reuseFailAlloc_4465_;
                        state = 8;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_a_4454_);
                    crate::leanh::lean_del_object(v___x_4451_);
                    crate::leanh::lean_dec(v_a_4411_);
                    crate::leanh::lean_dec(v___x_4398_);
                    v___y_4417_ = v___y_4401_;
                    v___y_4418_ = v___y_4402_;
                    v___y_4419_ = v___y_4403_;
                    v___y_4420_ = v___y_4404_;
                    v___y_4421_ = v___y_4405_;
                    v___y_4422_ = v___y_4406_;
                    v___y_4423_ = v___y_4407_;
                    v___y_4424_ = v___y_4408_;
                    state = 1;
                    continue;
                }
            }
            8 => {
                crate::leanh::lean_inc(v_a_4415_);
                v___x_4464_ = l_Lean_Elab_Term_throwTypeMismatchError___redArg(
                    v___x_4463_,
                    v_a_4411_,
                    v_a_4454_,
                    v_a_4415_,
                    v___x_4398_,
                    v___y_4405_,
                    v___y_4406_,
                    v___y_4407_,
                    v___y_4408_,
                );
                crate::leanh::lean_dec_ref(v___x_4463_);
                if crate::leanh::lean_obj_tag(v___x_4464_) == 0 {
                    crate::leanh::lean_dec_ref_known(v___x_4464_, 1);
                    v___y_4417_ = v___y_4401_;
                    v___y_4418_ = v___y_4402_;
                    v___y_4419_ = v___y_4403_;
                    v___y_4420_ = v___y_4404_;
                    v___y_4421_ = v___y_4405_;
                    v___y_4422_ = v___y_4406_;
                    v___y_4423_ = v___y_4407_;
                    v___y_4424_ = v___y_4408_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_dec(v_a_4415_);
                    crate::leanh::lean_dec(v___y_4408_);
                    crate::leanh::lean_dec_ref(v___y_4407_);
                    crate::leanh::lean_dec(v___y_4406_);
                    crate::leanh::lean_dec_ref(v___y_4405_);
                    crate::leanh::lean_dec_ref(v___x_4397_);
                    crate::leanh::lean_dec_ref(v_a_4395_);
                    crate::leanh::lean_dec(v_a_4391_);
                    return v___x_4464_;
                }
            }
            9 => {
                if crate::leanh::lean_obj_tag(v___y_4467_) == 0 {
                    v_a_4468_ = crate::leanh::lean_ctor_get(v___y_4467_, 0);
                    crate::leanh::lean_inc(v_a_4468_);
                    crate::leanh::lean_dec_ref_known(v___y_4467_, 1);
                    v___x_4469_ = (crate::leanh::lean_unbox(v_a_4468_) as u8);
                    crate::leanh::lean_dec(v_a_4468_);
                    v_a_4456_ = v___x_4469_;
                    state = 7;
                    continue;
                } else {
                    crate::leanh::lean_dec(v_a_4454_);
                    crate::leanh::lean_del_object(v___x_4451_);
                    crate::leanh::lean_dec(v_a_4415_);
                    crate::leanh::lean_dec(v_a_4411_);
                    crate::leanh::lean_dec(v___y_4408_);
                    crate::leanh::lean_dec_ref(v___y_4407_);
                    crate::leanh::lean_dec(v___y_4406_);
                    crate::leanh::lean_dec_ref(v___y_4405_);
                    crate::leanh::lean_dec(v___x_4398_);
                    crate::leanh::lean_dec_ref(v___x_4397_);
                    crate::leanh::lean_dec_ref(v_a_4395_);
                    crate::leanh::lean_dec(v_a_4391_);
                    v_a_4470_ = crate::leanh::lean_ctor_get(v___y_4467_, 0);
                    v_isSharedCheck_4477_ = (!crate::leanh::lean_is_exclusive(v___y_4467_)) as u8;
                    if v_isSharedCheck_4477_ == 0 {
                        v___x_4472_ = v___y_4467_;
                        v_isShared_4473_ = v_isSharedCheck_4477_;
                        state = 10;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4470_);
                        crate::leanh::lean_dec(v___y_4467_);
                        v___x_4472_ = crate::leanh::lean_box(0);
                        v_isShared_4473_ = v_isSharedCheck_4477_;
                        state = 10;
                        continue;
                    }
                }
            }
            10 => {
                if v_isShared_4473_ == 0 {
                    v___x_4475_ = v___x_4472_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_4476_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4476_, 0, v_a_4470_);
                    v___x_4475_ = v_reuseFailAlloc_4476_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                return v___x_4475_;
            }
            12 => {
                v_trackZetaDelta_4500_ = crate::leanh::lean_ctor_get_uint8(
                    v___y_4405_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 7) as u32,
                );
                v_zetaDeltaSet_4501_ = crate::leanh::lean_ctor_get(v___y_4405_, 1);
                v_lctx_4502_ = crate::leanh::lean_ctor_get(v___y_4405_, 2);
                v_localInstances_4503_ = crate::leanh::lean_ctor_get(v___y_4405_, 3);
                v_defEqCtx_x3f_4504_ = crate::leanh::lean_ctor_get(v___y_4405_, 4);
                v_synthPendingDepth_4505_ = crate::leanh::lean_ctor_get(v___y_4405_, 5);
                v_canUnfold_x3f_4506_ = crate::leanh::lean_ctor_get(v___y_4405_, 6);
                v_univApprox_4507_ = crate::leanh::lean_ctor_get_uint8(
                    v___y_4405_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 7 + 1) as u32,
                );
                v_inTypeClassResolution_4508_ = crate::leanh::lean_ctor_get_uint8(
                    v___y_4405_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 7 + 2) as u32,
                );
                v_cacheInferType_4509_ = crate::leanh::lean_ctor_get_uint8(
                    v___y_4405_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 7 + 3) as u32,
                );
                if v_isShared_4499_ == 0 {
                    v___x_4511_ = v___x_4498_;
                    state = 13;
                    continue;
                } else {
                    v_reuseFailAlloc_4516_ = crate::leanh::lean_alloc_ctor(0, 0, (19) as u32);
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_4516_,
                        0 as u32,
                        v_foApprox_4479_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_4516_,
                        1 as u32,
                        v_ctxApprox_4480_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_4516_,
                        2 as u32,
                        v_quasiPatternApprox_4481_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_4516_,
                        3 as u32,
                        v_constApprox_4482_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_4516_,
                        4 as u32,
                        v_isDefEqStuckEx_4483_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_4516_,
                        5 as u32,
                        v_unificationHints_4484_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_4516_,
                        6 as u32,
                        v_proofIrrelevance_4485_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_4516_,
                        8 as u32,
                        v_offsetCnstrs_4486_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_4516_,
                        9 as u32,
                        v_transparency_4487_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_4516_,
                        10 as u32,
                        v_etaStruct_4488_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_4516_,
                        11 as u32,
                        v_univApprox_4489_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_4516_,
                        12 as u32,
                        v_iota_4490_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_4516_,
                        13 as u32,
                        v_beta_4491_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_4516_,
                        14 as u32,
                        v_proj_4492_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_4516_,
                        15 as u32,
                        v_zeta_4493_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_4516_,
                        16 as u32,
                        v_zetaDelta_4494_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_4516_,
                        17 as u32,
                        v_zetaUnused_4495_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_4516_,
                        18 as u32,
                        v_zetaHave_4496_,
                    );
                    v___x_4511_ = v_reuseFailAlloc_4516_;
                    state = 13;
                    continue;
                }
            }
            13 => {
                crate::leanh::lean_ctor_set_uint8(v___x_4511_, 7 as u32, v___x_4400_);
                v___x_4512_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_4511_);
                v___x_4513_ = crate::leanh::lean_alloc_ctor(0, 1, (8) as u32);
                crate::leanh::lean_ctor_set(v___x_4513_, 0, v___x_4511_);
                crate::leanh::lean_ctor_set_uint64(
                    v___x_4513_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    v___x_4512_,
                );
                crate::leanh::lean_inc(v_canUnfold_x3f_4506_);
                crate::leanh::lean_inc(v_synthPendingDepth_4505_);
                crate::leanh::lean_inc(v_defEqCtx_x3f_4504_);
                crate::leanh::lean_inc_ref(v_localInstances_4503_);
                crate::leanh::lean_inc_ref(v_lctx_4502_);
                crate::leanh::lean_inc(v_zetaDeltaSet_4501_);
                v___x_4514_ = crate::leanh::lean_alloc_ctor(0, 7, (4) as u32);
                crate::leanh::lean_ctor_set(v___x_4514_, 0, v___x_4513_);
                crate::leanh::lean_ctor_set(v___x_4514_, 1, v_zetaDeltaSet_4501_);
                crate::leanh::lean_ctor_set(v___x_4514_, 2, v_lctx_4502_);
                crate::leanh::lean_ctor_set(v___x_4514_, 3, v_localInstances_4503_);
                crate::leanh::lean_ctor_set(v___x_4514_, 4, v_defEqCtx_x3f_4504_);
                crate::leanh::lean_ctor_set(v___x_4514_, 5, v_synthPendingDepth_4505_);
                crate::leanh::lean_ctor_set(v___x_4514_, 6, v_canUnfold_x3f_4506_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_4514_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 7) as u32,
                    v_trackZetaDelta_4500_,
                );
                crate::leanh::lean_ctor_set_uint8(
                    v___x_4514_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 7 + 1) as u32,
                    v_univApprox_4507_,
                );
                crate::leanh::lean_ctor_set_uint8(
                    v___x_4514_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 7 + 2) as u32,
                    v_inTypeClassResolution_4508_,
                );
                crate::leanh::lean_ctor_set_uint8(
                    v___x_4514_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 7 + 3) as u32,
                    v_cacheInferType_4509_,
                );
                crate::leanh::lean_inc(v_a_4454_);
                crate::leanh::lean_inc(v_a_4411_);
                v___x_4515_ = l_Lean_Meta_isExprDefEq(
                    v_a_4411_,
                    v_a_4454_,
                    v___x_4514_,
                    v___y_4406_,
                    v___y_4407_,
                    v___y_4408_,
                );
                crate::leanh::lean_dec_ref_known(v___x_4514_, 7);
                v___y_4467_ = v___x_4515_;
                state = 9;
                continue;
            }
            14 => {
                v_trackZetaDelta_4540_ = crate::leanh::lean_ctor_get_uint8(
                    v___y_4405_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 7) as u32,
                );
                v_zetaDeltaSet_4541_ = crate::leanh::lean_ctor_get(v___y_4405_, 1);
                v_lctx_4542_ = crate::leanh::lean_ctor_get(v___y_4405_, 2);
                v_localInstances_4543_ = crate::leanh::lean_ctor_get(v___y_4405_, 3);
                v_defEqCtx_x3f_4544_ = crate::leanh::lean_ctor_get(v___y_4405_, 4);
                v_synthPendingDepth_4545_ = crate::leanh::lean_ctor_get(v___y_4405_, 5);
                v_canUnfold_x3f_4546_ = crate::leanh::lean_ctor_get(v___y_4405_, 6);
                v_univApprox_4547_ = crate::leanh::lean_ctor_get_uint8(
                    v___y_4405_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 7 + 1) as u32,
                );
                v_inTypeClassResolution_4548_ = crate::leanh::lean_ctor_get_uint8(
                    v___y_4405_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 7 + 2) as u32,
                );
                v_cacheInferType_4549_ = crate::leanh::lean_ctor_get_uint8(
                    v___y_4405_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 7 + 3) as u32,
                );
                v___x_4550_ = 2;
                if v_isShared_4539_ == 0 {
                    v_config_4552_ = v___x_4538_;
                    state = 15;
                    continue;
                } else {
                    v_reuseFailAlloc_4593_ = crate::leanh::lean_alloc_ctor(0, 0, (19) as u32);
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_4593_,
                        0 as u32,
                        v_foApprox_4519_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_4593_,
                        1 as u32,
                        v_ctxApprox_4520_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_4593_,
                        2 as u32,
                        v_quasiPatternApprox_4521_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_4593_,
                        3 as u32,
                        v_constApprox_4522_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_4593_,
                        4 as u32,
                        v_isDefEqStuckEx_4523_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_4593_,
                        5 as u32,
                        v_unificationHints_4524_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_4593_,
                        6 as u32,
                        v_proofIrrelevance_4525_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_4593_,
                        7 as u32,
                        v_assignSyntheticOpaque_4526_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_4593_,
                        8 as u32,
                        v_offsetCnstrs_4527_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_4593_,
                        10 as u32,
                        v_etaStruct_4528_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_4593_,
                        11 as u32,
                        v_univApprox_4529_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_4593_,
                        12 as u32,
                        v_iota_4530_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_4593_,
                        13 as u32,
                        v_beta_4531_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_4593_,
                        14 as u32,
                        v_proj_4532_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_4593_,
                        15 as u32,
                        v_zeta_4533_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_4593_,
                        16 as u32,
                        v_zetaDelta_4534_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_4593_,
                        17 as u32,
                        v_zetaUnused_4535_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_4593_,
                        18 as u32,
                        v_zetaHave_4536_,
                    );
                    v_config_4552_ = v_reuseFailAlloc_4593_;
                    state = 15;
                    continue;
                }
            }
            15 => {
                crate::leanh::lean_ctor_set_uint8(v_config_4552_, 9 as u32, v___x_4550_);
                v___x_4553_ = l_Lean_Meta_Context_configKey(v___y_4405_);
                v___x_4554_ = 3u64;
                v___x_4555_ = lean_uint64_shift_right(v___x_4553_, v___x_4554_);
                v___x_4556_ = lean_uint64_shift_left(v___x_4555_, v___x_4554_);
                v___x_4557_ = crate::leanh::lean_uint64_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__2___closed__4), core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__2___closed__4_once), _init_l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__2___closed__4);
                v_key_4558_ = lean_uint64_lor(v___x_4556_, v___x_4557_);
                v___x_4559_ = crate::leanh::lean_alloc_ctor(0, 1, (8) as u32);
                crate::leanh::lean_ctor_set(v___x_4559_, 0, v_config_4552_);
                crate::leanh::lean_ctor_set_uint64(
                    v___x_4559_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    v_key_4558_,
                );
                crate::leanh::lean_inc(v_canUnfold_x3f_4546_);
                crate::leanh::lean_inc(v_synthPendingDepth_4545_);
                crate::leanh::lean_inc(v_defEqCtx_x3f_4544_);
                crate::leanh::lean_inc_ref(v_localInstances_4543_);
                crate::leanh::lean_inc_ref(v_lctx_4542_);
                crate::leanh::lean_inc(v_zetaDeltaSet_4541_);
                v___x_4560_ = crate::leanh::lean_alloc_ctor(0, 7, (4) as u32);
                crate::leanh::lean_ctor_set(v___x_4560_, 0, v___x_4559_);
                crate::leanh::lean_ctor_set(v___x_4560_, 1, v_zetaDeltaSet_4541_);
                crate::leanh::lean_ctor_set(v___x_4560_, 2, v_lctx_4542_);
                crate::leanh::lean_ctor_set(v___x_4560_, 3, v_localInstances_4543_);
                crate::leanh::lean_ctor_set(v___x_4560_, 4, v_defEqCtx_x3f_4544_);
                crate::leanh::lean_ctor_set(v___x_4560_, 5, v_synthPendingDepth_4545_);
                crate::leanh::lean_ctor_set(v___x_4560_, 6, v_canUnfold_x3f_4546_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_4560_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 7) as u32,
                    v_trackZetaDelta_4540_,
                );
                crate::leanh::lean_ctor_set_uint8(
                    v___x_4560_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 7 + 1) as u32,
                    v_univApprox_4547_,
                );
                crate::leanh::lean_ctor_set_uint8(
                    v___x_4560_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 7 + 2) as u32,
                    v_inTypeClassResolution_4548_,
                );
                crate::leanh::lean_ctor_set_uint8(
                    v___x_4560_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 7 + 3) as u32,
                    v_cacheInferType_4549_,
                );
                v___x_4561_ = l_Lean_Meta_Context_config(v___x_4560_);
                crate::leanh::lean_dec_ref_known(v___x_4560_, 7);
                v_foApprox_4562_ = crate::leanh::lean_ctor_get_uint8(v___x_4561_, 0 as u32);
                v_ctxApprox_4563_ = crate::leanh::lean_ctor_get_uint8(v___x_4561_, 1 as u32);
                v_quasiPatternApprox_4564_ =
                    crate::leanh::lean_ctor_get_uint8(v___x_4561_, 2 as u32);
                v_constApprox_4565_ = crate::leanh::lean_ctor_get_uint8(v___x_4561_, 3 as u32);
                v_isDefEqStuckEx_4566_ = crate::leanh::lean_ctor_get_uint8(v___x_4561_, 4 as u32);
                v_unificationHints_4567_ = crate::leanh::lean_ctor_get_uint8(v___x_4561_, 5 as u32);
                v_proofIrrelevance_4568_ = crate::leanh::lean_ctor_get_uint8(v___x_4561_, 6 as u32);
                v_offsetCnstrs_4569_ = crate::leanh::lean_ctor_get_uint8(v___x_4561_, 8 as u32);
                v_transparency_4570_ = crate::leanh::lean_ctor_get_uint8(v___x_4561_, 9 as u32);
                v_etaStruct_4571_ = crate::leanh::lean_ctor_get_uint8(v___x_4561_, 10 as u32);
                v_univApprox_4572_ = crate::leanh::lean_ctor_get_uint8(v___x_4561_, 11 as u32);
                v_iota_4573_ = crate::leanh::lean_ctor_get_uint8(v___x_4561_, 12 as u32);
                v_beta_4574_ = crate::leanh::lean_ctor_get_uint8(v___x_4561_, 13 as u32);
                v_proj_4575_ = crate::leanh::lean_ctor_get_uint8(v___x_4561_, 14 as u32);
                v_zeta_4576_ = crate::leanh::lean_ctor_get_uint8(v___x_4561_, 15 as u32);
                v_zetaDelta_4577_ = crate::leanh::lean_ctor_get_uint8(v___x_4561_, 16 as u32);
                v_zetaUnused_4578_ = crate::leanh::lean_ctor_get_uint8(v___x_4561_, 17 as u32);
                v_zetaHave_4579_ = crate::leanh::lean_ctor_get_uint8(v___x_4561_, 18 as u32);
                v_isSharedCheck_4592_ = (!crate::leanh::lean_is_exclusive(v___x_4561_)) as u8;
                if v_isSharedCheck_4592_ == 0 {
                    v___x_4581_ = v___x_4561_;
                    v_isShared_4582_ = v_isSharedCheck_4592_;
                    state = 16;
                    continue;
                } else {
                    crate::leanh::lean_dec(v___x_4561_);
                    v___x_4581_ = crate::leanh::lean_box(0);
                    v_isShared_4582_ = v_isSharedCheck_4592_;
                    state = 16;
                    continue;
                }
            }
            16 => {
                if v_isShared_4582_ == 0 {
                    v___x_4584_ = v___x_4581_;
                    state = 17;
                    continue;
                } else {
                    v_reuseFailAlloc_4591_ = crate::leanh::lean_alloc_ctor(0, 0, (19) as u32);
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_4591_,
                        0 as u32,
                        v_foApprox_4562_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_4591_,
                        1 as u32,
                        v_ctxApprox_4563_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_4591_,
                        2 as u32,
                        v_quasiPatternApprox_4564_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_4591_,
                        3 as u32,
                        v_constApprox_4565_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_4591_,
                        4 as u32,
                        v_isDefEqStuckEx_4566_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_4591_,
                        5 as u32,
                        v_unificationHints_4567_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_4591_,
                        6 as u32,
                        v_proofIrrelevance_4568_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_4591_,
                        8 as u32,
                        v_offsetCnstrs_4569_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_4591_,
                        9 as u32,
                        v_transparency_4570_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_4591_,
                        10 as u32,
                        v_etaStruct_4571_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_4591_,
                        11 as u32,
                        v_univApprox_4572_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_4591_,
                        12 as u32,
                        v_iota_4573_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_4591_,
                        13 as u32,
                        v_beta_4574_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_4591_,
                        14 as u32,
                        v_proj_4575_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_4591_,
                        15 as u32,
                        v_zeta_4576_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_4591_,
                        16 as u32,
                        v_zetaDelta_4577_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_4591_,
                        17 as u32,
                        v_zetaUnused_4578_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_4591_,
                        18 as u32,
                        v_zetaHave_4579_,
                    );
                    v___x_4584_ = v_reuseFailAlloc_4591_;
                    state = 17;
                    continue;
                }
            }
            17 => {
                crate::leanh::lean_ctor_set_uint8(v___x_4584_, 7 as u32, v___x_4400_);
                v___x_4585_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_4584_);
                v___x_4586_ = crate::leanh::lean_alloc_ctor(0, 1, (8) as u32);
                crate::leanh::lean_ctor_set(v___x_4586_, 0, v___x_4584_);
                crate::leanh::lean_ctor_set_uint64(
                    v___x_4586_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    v___x_4585_,
                );
                crate::leanh::lean_inc(v_canUnfold_x3f_4546_);
                crate::leanh::lean_inc(v_synthPendingDepth_4545_);
                crate::leanh::lean_inc(v_defEqCtx_x3f_4544_);
                crate::leanh::lean_inc_ref(v_localInstances_4543_);
                crate::leanh::lean_inc_ref(v_lctx_4542_);
                crate::leanh::lean_inc(v_zetaDeltaSet_4541_);
                v___x_4587_ = crate::leanh::lean_alloc_ctor(0, 7, (4) as u32);
                crate::leanh::lean_ctor_set(v___x_4587_, 0, v___x_4586_);
                crate::leanh::lean_ctor_set(v___x_4587_, 1, v_zetaDeltaSet_4541_);
                crate::leanh::lean_ctor_set(v___x_4587_, 2, v_lctx_4542_);
                crate::leanh::lean_ctor_set(v___x_4587_, 3, v_localInstances_4543_);
                crate::leanh::lean_ctor_set(v___x_4587_, 4, v_defEqCtx_x3f_4544_);
                crate::leanh::lean_ctor_set(v___x_4587_, 5, v_synthPendingDepth_4545_);
                crate::leanh::lean_ctor_set(v___x_4587_, 6, v_canUnfold_x3f_4546_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_4587_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 7) as u32,
                    v_trackZetaDelta_4540_,
                );
                crate::leanh::lean_ctor_set_uint8(
                    v___x_4587_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 7 + 1) as u32,
                    v_univApprox_4547_,
                );
                crate::leanh::lean_ctor_set_uint8(
                    v___x_4587_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 7 + 2) as u32,
                    v_inTypeClassResolution_4548_,
                );
                crate::leanh::lean_ctor_set_uint8(
                    v___x_4587_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 7 + 3) as u32,
                    v_cacheInferType_4549_,
                );
                crate::leanh::lean_inc(v_a_4454_);
                crate::leanh::lean_inc(v_a_4411_);
                v___x_4588_ = l_Lean_Meta_isExprDefEq(
                    v_a_4411_,
                    v_a_4454_,
                    v___x_4587_,
                    v___y_4406_,
                    v___y_4407_,
                    v___y_4408_,
                );
                crate::leanh::lean_dec_ref_known(v___x_4587_, 7);
                if crate::leanh::lean_obj_tag(v___x_4588_) == 0 {
                    v_a_4589_ = crate::leanh::lean_ctor_get(v___x_4588_, 0);
                    crate::leanh::lean_inc(v_a_4589_);
                    crate::leanh::lean_dec_ref_known(v___x_4588_, 1);
                    v___x_4590_ = (crate::leanh::lean_unbox(v_a_4589_) as u8);
                    crate::leanh::lean_dec(v_a_4589_);
                    v_a_4456_ = v___x_4590_;
                    state = 7;
                    continue;
                } else {
                    v___y_4467_ = v___x_4588_;
                    state = 9;
                    continue;
                }
            }
            18 => {
                if v_isShared_4598_ == 0 {
                    v___x_4600_ = v___x_4597_;
                    state = 19;
                    continue;
                } else {
                    v_reuseFailAlloc_4601_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4601_, 0, v_a_4595_);
                    v___x_4600_ = v_reuseFailAlloc_4601_;
                    state = 19;
                    continue;
                }
            }
            19 => {
                return v___x_4600_;
            }
            20 => {
                if v_isShared_4608_ == 0 {
                    v___x_4610_ = v___x_4607_;
                    state = 21;
                    continue;
                } else {
                    v_reuseFailAlloc_4611_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4611_, 0, v_a_4605_);
                    v___x_4610_ = v_reuseFailAlloc_4611_;
                    state = 21;
                    continue;
                }
            }
            21 => {
                return v___x_4610_;
            }
            22 => {
                if v_isShared_4616_ == 0 {
                    v___x_4618_ = v___x_4615_;
                    state = 23;
                    continue;
                } else {
                    v_reuseFailAlloc_4619_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4619_, 0, v_a_4613_);
                    v___x_4618_ = v_reuseFailAlloc_4619_;
                    state = 23;
                    continue;
                }
            }
            23 => {
                return v___x_4618_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__2___boxed(
    _args: *mut *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_4621_: *mut crate::leanh::LeanObject = *_args.add(0);
    let mut v_a_4622_: *mut crate::leanh::LeanObject = *_args.add(1);
    let mut v___x_4623_: *mut crate::leanh::LeanObject = *_args.add(2);
    let mut v___x_4624_: *mut crate::leanh::LeanObject = *_args.add(3);
    let mut v_a_4625_: *mut crate::leanh::LeanObject = *_args.add(4);
    let mut v_mvarCounter_4626_: *mut crate::leanh::LeanObject = *_args.add(5);
    let mut v___x_4627_: *mut crate::leanh::LeanObject = *_args.add(6);
    let mut v___x_4628_: *mut crate::leanh::LeanObject = *_args.add(7);
    let mut v_useReducible_4629_: *mut crate::leanh::LeanObject = *_args.add(8);
    let mut v___x_4630_: *mut crate::leanh::LeanObject = *_args.add(9);
    let mut v___y_4631_: *mut crate::leanh::LeanObject = *_args.add(10);
    let mut v___y_4632_: *mut crate::leanh::LeanObject = *_args.add(11);
    let mut v___y_4633_: *mut crate::leanh::LeanObject = *_args.add(12);
    let mut v___y_4634_: *mut crate::leanh::LeanObject = *_args.add(13);
    let mut v___y_4635_: *mut crate::leanh::LeanObject = *_args.add(14);
    let mut v___y_4636_: *mut crate::leanh::LeanObject = *_args.add(15);
    let mut v___y_4637_: *mut crate::leanh::LeanObject = *_args.add(16);
    let mut v___y_4638_: *mut crate::leanh::LeanObject = *_args.add(17);
    let mut v___y_4639_: *mut crate::leanh::LeanObject = *_args.add(18);
    let mut v___x_93519__boxed_4640_: u8 = 0;
    let mut v___x_93520__boxed_4641_: u8 = 0;
    let mut v_useReducible_boxed_4642_: u8 = 0;
    let mut v___x_93524__boxed_4643_: u8 = 0;
    let mut v_res_4644_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_93519__boxed_4640_ = (crate::leanh::lean_unbox(v___x_4623_) as u8);
    v___x_93520__boxed_4641_ = (crate::leanh::lean_unbox(v___x_4624_) as u8);
    v_useReducible_boxed_4642_ = (crate::leanh::lean_unbox(v_useReducible_4629_) as u8);
    v___x_93524__boxed_4643_ = (crate::leanh::lean_unbox(v___x_4630_) as u8);
    v_res_4644_ =
        l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__2(
            v_a_4621_,
            v_a_4622_,
            v___x_93519__boxed_4640_,
            v___x_93520__boxed_4641_,
            v_a_4625_,
            v_mvarCounter_4626_,
            v___x_4627_,
            v___x_4628_,
            v_useReducible_boxed_4642_,
            v___x_93524__boxed_4643_,
            v___y_4631_,
            v___y_4632_,
            v___y_4633_,
            v___y_4634_,
            v___y_4635_,
            v___y_4636_,
            v___y_4637_,
            v___y_4638_,
        );
    crate::leanh::lean_dec(v___y_4634_);
    crate::leanh::lean_dec_ref(v___y_4633_);
    crate::leanh::lean_dec(v___y_4632_);
    crate::leanh::lean_dec_ref(v___y_4631_);
    crate::leanh::lean_dec(v_mvarCounter_4626_);
    return v_res_4644_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__3(
    mut v_a_4645_: *mut crate::leanh::LeanObject,
    mut v___y_4646_: *mut crate::leanh::LeanObject,
    mut v___y_4647_: *mut crate::leanh::LeanObject,
    mut v___y_4648_: *mut crate::leanh::LeanObject,
    mut v___y_4649_: *mut crate::leanh::LeanObject,
    mut v___y_4650_: *mut crate::leanh::LeanObject,
    mut v___y_4651_: *mut crate::leanh::LeanObject,
    mut v___y_4652_: *mut crate::leanh::LeanObject,
    mut v___y_4653_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4655_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_infoState_4656_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_4657_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_4658_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ngen_4659_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_4660_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_traceState_4661_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_cache_4662_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_messages_4663_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_4664_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4666_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4667_: u8 = 0;
    let mut v_enabled_4668_: u8 = 0;
    let mut v_assignment_4669_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_lazyAssignment_4670_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4672_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4673_: u8 = 0;
    let mut v___x_4675_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4677_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4678_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4679_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4680_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4681_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4682_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4683_: u8 = 0;
    let mut v_unused_4684_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4685_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4655_ = lean_st_ref_take(v___y_4653_);
                v_infoState_4656_ = crate::leanh::lean_ctor_get(v___x_4655_, 7);
                v_env_4657_ = crate::leanh::lean_ctor_get(v___x_4655_, 0);
                v_nextMacroScope_4658_ = crate::leanh::lean_ctor_get(v___x_4655_, 1);
                v_ngen_4659_ = crate::leanh::lean_ctor_get(v___x_4655_, 2);
                v_auxDeclNGen_4660_ = crate::leanh::lean_ctor_get(v___x_4655_, 3);
                v_traceState_4661_ = crate::leanh::lean_ctor_get(v___x_4655_, 4);
                v_cache_4662_ = crate::leanh::lean_ctor_get(v___x_4655_, 5);
                v_messages_4663_ = crate::leanh::lean_ctor_get(v___x_4655_, 6);
                v_snapshotTasks_4664_ = crate::leanh::lean_ctor_get(v___x_4655_, 8);
                v_isSharedCheck_4685_ = (!crate::leanh::lean_is_exclusive(v___x_4655_)) as u8;
                if v_isSharedCheck_4685_ == 0 {
                    v___x_4666_ = v___x_4655_;
                    v_isShared_4667_ = v_isSharedCheck_4685_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snapshotTasks_4664_);
                    crate::leanh::lean_inc(v_infoState_4656_);
                    crate::leanh::lean_inc(v_messages_4663_);
                    crate::leanh::lean_inc(v_cache_4662_);
                    crate::leanh::lean_inc(v_traceState_4661_);
                    crate::leanh::lean_inc(v_auxDeclNGen_4660_);
                    crate::leanh::lean_inc(v_ngen_4659_);
                    crate::leanh::lean_inc(v_nextMacroScope_4658_);
                    crate::leanh::lean_inc(v_env_4657_);
                    crate::leanh::lean_dec(v___x_4655_);
                    v___x_4666_ = crate::leanh::lean_box(0);
                    v_isShared_4667_ = v_isSharedCheck_4685_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_enabled_4668_ = crate::leanh::lean_ctor_get_uint8(
                    v_infoState_4656_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u32,
                );
                v_assignment_4669_ = crate::leanh::lean_ctor_get(v_infoState_4656_, 0);
                v_lazyAssignment_4670_ = crate::leanh::lean_ctor_get(v_infoState_4656_, 1);
                v_isSharedCheck_4683_ = (!crate::leanh::lean_is_exclusive(v_infoState_4656_)) as u8;
                if v_isSharedCheck_4683_ == 0 {
                    v_unused_4684_ = crate::leanh::lean_ctor_get(v_infoState_4656_, 2);
                    crate::leanh::lean_dec(v_unused_4684_);
                    v___x_4672_ = v_infoState_4656_;
                    v_isShared_4673_ = v_isSharedCheck_4683_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_lazyAssignment_4670_);
                    crate::leanh::lean_inc(v_assignment_4669_);
                    crate::leanh::lean_dec(v_infoState_4656_);
                    v___x_4672_ = crate::leanh::lean_box(0);
                    v_isShared_4673_ = v_isSharedCheck_4683_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                if v_isShared_4673_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4672_, 2, v_a_4645_);
                    v___x_4675_ = v___x_4672_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_4682_ = crate::leanh::lean_alloc_ctor(0, 3, (1) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4682_, 0, v_assignment_4669_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4682_, 1, v_lazyAssignment_4670_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4682_, 2, v_a_4645_);
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_4682_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u32,
                        v_enabled_4668_,
                    );
                    v___x_4675_ = v_reuseFailAlloc_4682_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_4667_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4666_, 7, v___x_4675_);
                    v___x_4677_ = v___x_4666_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4681_ = crate::leanh::lean_alloc_ctor(0, 9, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4681_, 0, v_env_4657_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4681_, 1, v_nextMacroScope_4658_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4681_, 2, v_ngen_4659_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4681_, 3, v_auxDeclNGen_4660_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4681_, 4, v_traceState_4661_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4681_, 5, v_cache_4662_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4681_, 6, v_messages_4663_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4681_, 7, v___x_4675_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4681_, 8, v_snapshotTasks_4664_);
                    v___x_4677_ = v_reuseFailAlloc_4681_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_4678_ = lean_st_ref_set(v___y_4653_, v___x_4677_);
                v___x_4679_ = crate::leanh::lean_box(0);
                v___x_4680_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4680_, 0, v___x_4679_);
                return v___x_4680_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__3___boxed(
    mut v_a_4686_: *mut crate::leanh::LeanObject,
    mut v___y_4687_: *mut crate::leanh::LeanObject,
    mut v___y_4688_: *mut crate::leanh::LeanObject,
    mut v___y_4689_: *mut crate::leanh::LeanObject,
    mut v___y_4690_: *mut crate::leanh::LeanObject,
    mut v___y_4691_: *mut crate::leanh::LeanObject,
    mut v___y_4692_: *mut crate::leanh::LeanObject,
    mut v___y_4693_: *mut crate::leanh::LeanObject,
    mut v___y_4694_: *mut crate::leanh::LeanObject,
    mut v___y_4695_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4696_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4696_ =
        l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__3(
            v_a_4686_,
            v___y_4687_,
            v___y_4688_,
            v___y_4689_,
            v___y_4690_,
            v___y_4691_,
            v___y_4692_,
            v___y_4693_,
            v___y_4694_,
        );
    crate::leanh::lean_dec(v___y_4694_);
    crate::leanh::lean_dec_ref(v___y_4693_);
    crate::leanh::lean_dec(v___y_4692_);
    crate::leanh::lean_dec_ref(v___y_4691_);
    crate::leanh::lean_dec(v___y_4690_);
    crate::leanh::lean_dec_ref(v___y_4689_);
    crate::leanh::lean_dec(v___y_4688_);
    crate::leanh::lean_dec_ref(v___y_4687_);
    return v_res_4696_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__7_spec__16_spec__19_spec__25___redArg(
    mut v_x_4697_: *mut crate::leanh::LeanObject,
    mut v_x_4698_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_key_4699_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_4700_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_4701_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4703_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4704_: u8 = 0;
    let mut v___x_4705_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4706_: u64 = 0;
    let mut v___x_4707_: u64 = 0;
    let mut v___x_4708_: u64 = 0;
    let mut v_fold_4709_: u64 = 0;
    let mut v___x_4710_: u64 = 0;
    let mut v___x_4711_: u64 = 0;
    let mut v___x_4712_: u64 = 0;
    let mut v___x_4713_: usize = 0;
    let mut v___x_4714_: usize = 0;
    let mut v___x_4715_: usize = 0;
    let mut v___x_4716_: usize = 0;
    let mut v___x_4717_: usize = 0;
    let mut v___x_4718_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4720_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4721_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4723_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4724_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_4698_) == 0 {
                    return v_x_4697_;
                } else {
                    v_key_4699_ = crate::leanh::lean_ctor_get(v_x_4698_, 0);
                    v_value_4700_ = crate::leanh::lean_ctor_get(v_x_4698_, 1);
                    v_tail_4701_ = crate::leanh::lean_ctor_get(v_x_4698_, 2);
                    v_isSharedCheck_4724_ = (!crate::leanh::lean_is_exclusive(v_x_4698_)) as u8;
                    if v_isSharedCheck_4724_ == 0 {
                        v___x_4703_ = v_x_4698_;
                        v_isShared_4704_ = v_isSharedCheck_4724_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_tail_4701_);
                        crate::leanh::lean_inc(v_value_4700_);
                        crate::leanh::lean_inc(v_key_4699_);
                        crate::leanh::lean_dec(v_x_4698_);
                        v___x_4703_ = crate::leanh::lean_box(0);
                        v_isShared_4704_ = v_isSharedCheck_4724_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_4705_ = lean_array_get_size(v_x_4697_);
                v___x_4706_ = l_Lean_Expr_hash(v_key_4699_);
                v___x_4707_ = 32u64;
                v___x_4708_ = lean_uint64_shift_right(v___x_4706_, v___x_4707_);
                v_fold_4709_ = lean_uint64_xor(v___x_4706_, v___x_4708_);
                v___x_4710_ = 16u64;
                v___x_4711_ = lean_uint64_shift_right(v_fold_4709_, v___x_4710_);
                v___x_4712_ = lean_uint64_xor(v_fold_4709_, v___x_4711_);
                v___x_4713_ = lean_uint64_to_usize(v___x_4712_);
                v___x_4714_ = lean_usize_of_nat(v___x_4705_);
                v___x_4715_ = 1usize;
                v___x_4716_ = lean_usize_sub(v___x_4714_, v___x_4715_);
                v___x_4717_ = lean_usize_land(v___x_4713_, v___x_4716_);
                v___x_4718_ = lean_array_uget_borrowed(v_x_4697_, v___x_4717_);
                crate::leanh::lean_inc(v___x_4718_);
                if v_isShared_4704_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4703_, 2, v___x_4718_);
                    v___x_4720_ = v___x_4703_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4723_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4723_, 0, v_key_4699_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4723_, 1, v_value_4700_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4723_, 2, v___x_4718_);
                    v___x_4720_ = v_reuseFailAlloc_4723_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_4721_ = lean_array_uset(v_x_4697_, v___x_4717_, v___x_4720_);
                v_x_4697_ = v___x_4721_;
                v_x_4698_ = v_tail_4701_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__7_spec__16_spec__19___redArg(
    mut v_i_4725_: *mut crate::leanh::LeanObject,
    mut v_source_4726_: *mut crate::leanh::LeanObject,
    mut v_target_4727_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4728_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4729_: u8 = 0;
    let mut v_es_4730_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4731_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_source_4732_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_target_4733_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4734_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4735_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4728_ = lean_array_get_size(v_source_4726_);
                v___x_4729_ = lean_nat_dec_lt(v_i_4725_, v___x_4728_);
                if v___x_4729_ == 0 {
                    crate::leanh::lean_dec_ref(v_source_4726_);
                    crate::leanh::lean_dec(v_i_4725_);
                    return v_target_4727_;
                } else {
                    v_es_4730_ = lean_array_fget(v_source_4726_, v_i_4725_);
                    v___x_4731_ = crate::leanh::lean_box(0);
                    v_source_4732_ = lean_array_fset(v_source_4726_, v_i_4725_, v___x_4731_);
                    v_target_4733_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__7_spec__16_spec__19_spec__25___redArg(v_target_4727_, v_es_4730_);
                    v___x_4734_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_4735_ = lean_nat_add(v_i_4725_, v___x_4734_);
                    crate::leanh::lean_dec(v_i_4725_);
                    v_i_4725_ = v___x_4735_;
                    v_source_4726_ = v_source_4732_;
                    v_target_4727_ = v_target_4733_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__7_spec__16___redArg(
    mut v_data_4737_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4738_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4739_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nbuckets_4740_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4741_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4742_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4743_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4744_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4738_ = lean_array_get_size(v_data_4737_);
    v___x_4739_ = crate::leanh::lean_unsigned_to_nat(2);
    v_nbuckets_4740_ = lean_nat_mul(v___x_4738_, v___x_4739_);
    v___x_4741_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_4742_ = crate::leanh::lean_box(0);
    v___x_4743_ = lean_mk_array(v_nbuckets_4740_, v___x_4742_);
    v___x_4744_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__7_spec__16_spec__19___redArg(v___x_4741_, v_data_4737_, v___x_4743_);
    return v___x_4744_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__6_spec__14___redArg(
    mut v_a_4745_: *mut crate::leanh::LeanObject,
    mut v_x_4746_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_4747_: u8 = 0;
    let mut v_key_4748_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_4749_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4750_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_4746_) == 0 {
                    v___x_4747_ = 0;
                    return v___x_4747_;
                } else {
                    v_key_4748_ = crate::leanh::lean_ctor_get(v_x_4746_, 0);
                    v_tail_4749_ = crate::leanh::lean_ctor_get(v_x_4746_, 2);
                    v___x_4750_ = lean_expr_eqv(v_key_4748_, v_a_4745_);
                    if v___x_4750_ == 0 {
                        v_x_4746_ = v_tail_4749_;
                        state = 0;
                        continue;
                    } else {
                        return v___x_4750_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__6_spec__14___redArg___boxed(
    mut v_a_4752_: *mut crate::leanh::LeanObject,
    mut v_x_4753_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4754_: u8 = 0;
    let mut v_r_4755_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4754_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__6_spec__14___redArg(v_a_4752_, v_x_4753_);
    crate::leanh::lean_dec(v_x_4753_);
    crate::leanh::lean_dec_ref(v_a_4752_);
    v_r_4755_ = crate::leanh::lean_box((v_res_4754_) as usize);
    return v_r_4755_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__7___redArg(
    mut v_m_4756_: *mut crate::leanh::LeanObject,
    mut v_a_4757_: *mut crate::leanh::LeanObject,
    mut v_b_4758_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_size_4759_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_4760_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4761_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4762_: u64 = 0;
    let mut v___x_4763_: u64 = 0;
    let mut v___x_4764_: u64 = 0;
    let mut v_fold_4765_: u64 = 0;
    let mut v___x_4766_: u64 = 0;
    let mut v___x_4767_: u64 = 0;
    let mut v___x_4768_: u64 = 0;
    let mut v___x_4769_: usize = 0;
    let mut v___x_4770_: usize = 0;
    let mut v___x_4771_: usize = 0;
    let mut v___x_4772_: usize = 0;
    let mut v___x_4773_: usize = 0;
    let mut v_bkt_4774_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4775_: u8 = 0;
    let mut v___x_4777_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4778_: u8 = 0;
    let mut v___x_4779_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_x27_4780_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4781_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_x27_4782_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4783_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4784_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4785_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4786_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4787_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4788_: u8 = 0;
    let mut v_val_4789_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4791_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4792_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4794_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4795_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4796_: u8 = 0;
    let mut v_unused_4797_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_4798_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_size_4759_ = crate::leanh::lean_ctor_get(v_m_4756_, 0);
                v_buckets_4760_ = crate::leanh::lean_ctor_get(v_m_4756_, 1);
                v___x_4761_ = lean_array_get_size(v_buckets_4760_);
                v___x_4762_ = l_Lean_Expr_hash(v_a_4757_);
                v___x_4763_ = 32u64;
                v___x_4764_ = lean_uint64_shift_right(v___x_4762_, v___x_4763_);
                v_fold_4765_ = lean_uint64_xor(v___x_4762_, v___x_4764_);
                v___x_4766_ = 16u64;
                v___x_4767_ = lean_uint64_shift_right(v_fold_4765_, v___x_4766_);
                v___x_4768_ = lean_uint64_xor(v_fold_4765_, v___x_4767_);
                v___x_4769_ = lean_uint64_to_usize(v___x_4768_);
                v___x_4770_ = lean_usize_of_nat(v___x_4761_);
                v___x_4771_ = 1usize;
                v___x_4772_ = lean_usize_sub(v___x_4770_, v___x_4771_);
                v___x_4773_ = lean_usize_land(v___x_4769_, v___x_4772_);
                v_bkt_4774_ = lean_array_uget_borrowed(v_buckets_4760_, v___x_4773_);
                v___x_4775_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__6_spec__14___redArg(v_a_4757_, v_bkt_4774_);
                if v___x_4775_ == 0 {
                    crate::leanh::lean_inc_ref(v_buckets_4760_);
                    crate::leanh::lean_inc(v_size_4759_);
                    v_isSharedCheck_4796_ = (!crate::leanh::lean_is_exclusive(v_m_4756_)) as u8;
                    if v_isSharedCheck_4796_ == 0 {
                        v_unused_4797_ = crate::leanh::lean_ctor_get(v_m_4756_, 1);
                        crate::leanh::lean_dec(v_unused_4797_);
                        v_unused_4798_ = crate::leanh::lean_ctor_get(v_m_4756_, 0);
                        crate::leanh::lean_dec(v_unused_4798_);
                        v___x_4777_ = v_m_4756_;
                        v_isShared_4778_ = v_isSharedCheck_4796_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v_m_4756_);
                        v___x_4777_ = crate::leanh::lean_box(0);
                        v_isShared_4778_ = v_isSharedCheck_4796_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_b_4758_);
                    crate::leanh::lean_dec_ref(v_a_4757_);
                    return v_m_4756_;
                }
            }
            1 => {
                v___x_4779_ = crate::leanh::lean_unsigned_to_nat(1);
                v_size_x27_4780_ = lean_nat_add(v_size_4759_, v___x_4779_);
                crate::leanh::lean_dec(v_size_4759_);
                crate::leanh::lean_inc(v_bkt_4774_);
                v___x_4781_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4781_, 0, v_a_4757_);
                crate::leanh::lean_ctor_set(v___x_4781_, 1, v_b_4758_);
                crate::leanh::lean_ctor_set(v___x_4781_, 2, v_bkt_4774_);
                v_buckets_x27_4782_ = lean_array_uset(v_buckets_4760_, v___x_4773_, v___x_4781_);
                v___x_4783_ = crate::leanh::lean_unsigned_to_nat(4);
                v___x_4784_ = lean_nat_mul(v_size_x27_4780_, v___x_4783_);
                v___x_4785_ = crate::leanh::lean_unsigned_to_nat(3);
                v___x_4786_ = lean_nat_div(v___x_4784_, v___x_4785_);
                crate::leanh::lean_dec(v___x_4784_);
                v___x_4787_ = lean_array_get_size(v_buckets_x27_4782_);
                v___x_4788_ = lean_nat_dec_le(v___x_4786_, v___x_4787_);
                crate::leanh::lean_dec(v___x_4786_);
                if v___x_4788_ == 0 {
                    v_val_4789_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__7_spec__16___redArg(v_buckets_x27_4782_);
                    if v_isShared_4778_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_4777_, 1, v_val_4789_);
                        crate::leanh::lean_ctor_set(v___x_4777_, 0, v_size_x27_4780_);
                        v___x_4791_ = v___x_4777_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_4792_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4792_, 0, v_size_x27_4780_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4792_, 1, v_val_4789_);
                        v___x_4791_ = v_reuseFailAlloc_4792_;
                        state = 2;
                        continue;
                    }
                } else {
                    if v_isShared_4778_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_4777_, 1, v_buckets_x27_4782_);
                        crate::leanh::lean_ctor_set(v___x_4777_, 0, v_size_x27_4780_);
                        v___x_4794_ = v___x_4777_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_4795_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4795_, 0, v_size_x27_4780_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4795_, 1, v_buckets_x27_4782_);
                        v___x_4794_ = v_reuseFailAlloc_4795_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_4791_;
            }
            3 => {
                return v___x_4794_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_getExprMVarAssignment_x3f___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__8_spec__18___redArg(
    mut v_mvarId_4799_: *mut crate::leanh::LeanObject,
    mut v___y_4800_: *mut crate::leanh::LeanObject,
    mut v___y_4801_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4803_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_4804_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4805_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4806_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4807_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4808_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4803_ = lean_st_ref_get(v___y_4801_);
    v_mctx_4804_ = crate::leanh::lean_ctor_get(v___x_4803_, 0);
    crate::leanh::lean_inc_ref(v_mctx_4804_);
    crate::leanh::lean_dec(v___x_4803_);
    v___x_4805_ = l_Lean_MetavarContext_getExprAssignmentCore_x3f(v_mctx_4804_, v_mvarId_4799_);
    crate::leanh::lean_dec_ref(v_mctx_4804_);
    v___x_4806_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_4806_, 0, v___x_4805_);
    v___x_4807_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_4807_, 0, v___x_4806_);
    crate::leanh::lean_ctor_set(v___x_4807_, 1, v___y_4800_);
    v___x_4808_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_4808_, 0, v___x_4807_);
    return v___x_4808_;
}
pub unsafe fn l_Lean_getExprMVarAssignment_x3f___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__8_spec__18___redArg___boxed(
    mut v_mvarId_4809_: *mut crate::leanh::LeanObject,
    mut v___y_4810_: *mut crate::leanh::LeanObject,
    mut v___y_4811_: *mut crate::leanh::LeanObject,
    mut v___y_4812_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4813_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4813_ = l_Lean_getExprMVarAssignment_x3f___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__8_spec__18___redArg(v_mvarId_4809_, v___y_4810_, v___y_4811_);
    crate::leanh::lean_dec(v___y_4811_);
    crate::leanh::lean_dec(v_mvarId_4809_);
    return v_res_4813_;
}
pub unsafe fn l_Lean_getDelayedMVarAssignment_x3f___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__8_spec__19___redArg(
    mut v_mvarId_4814_: *mut crate::leanh::LeanObject,
    mut v___y_4815_: *mut crate::leanh::LeanObject,
    mut v___y_4816_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4818_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_4819_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4820_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4821_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4822_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4823_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4818_ = lean_st_ref_get(v___y_4816_);
    v_mctx_4819_ = crate::leanh::lean_ctor_get(v___x_4818_, 0);
    crate::leanh::lean_inc_ref(v_mctx_4819_);
    crate::leanh::lean_dec(v___x_4818_);
    v___x_4820_ =
        l_Lean_MetavarContext_getDelayedMVarAssignmentCore_x3f(v_mctx_4819_, v_mvarId_4814_);
    crate::leanh::lean_dec_ref(v_mctx_4819_);
    v___x_4821_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_4821_, 0, v___x_4820_);
    v___x_4822_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_4822_, 0, v___x_4821_);
    crate::leanh::lean_ctor_set(v___x_4822_, 1, v___y_4815_);
    v___x_4823_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_4823_, 0, v___x_4822_);
    return v___x_4823_;
}
pub unsafe fn l_Lean_getDelayedMVarAssignment_x3f___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__8_spec__19___redArg___boxed(
    mut v_mvarId_4824_: *mut crate::leanh::LeanObject,
    mut v___y_4825_: *mut crate::leanh::LeanObject,
    mut v___y_4826_: *mut crate::leanh::LeanObject,
    mut v___y_4827_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4828_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4828_ = l_Lean_getDelayedMVarAssignment_x3f___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__8_spec__19___redArg(v_mvarId_4824_, v___y_4825_, v___y_4826_);
    crate::leanh::lean_dec(v___y_4826_);
    crate::leanh::lean_dec(v_mvarId_4824_);
    return v_res_4828_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__6___redArg(
    mut v_m_4829_: *mut crate::leanh::LeanObject,
    mut v_a_4830_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v_buckets_4831_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4832_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4833_: u64 = 0;
    let mut v___x_4834_: u64 = 0;
    let mut v___x_4835_: u64 = 0;
    let mut v_fold_4836_: u64 = 0;
    let mut v___x_4837_: u64 = 0;
    let mut v___x_4838_: u64 = 0;
    let mut v___x_4839_: u64 = 0;
    let mut v___x_4840_: usize = 0;
    let mut v___x_4841_: usize = 0;
    let mut v___x_4842_: usize = 0;
    let mut v___x_4843_: usize = 0;
    let mut v___x_4844_: usize = 0;
    let mut v___x_4845_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4846_: u8 = 0;
    v_buckets_4831_ = crate::leanh::lean_ctor_get(v_m_4829_, 1);
    v___x_4832_ = lean_array_get_size(v_buckets_4831_);
    v___x_4833_ = l_Lean_Expr_hash(v_a_4830_);
    v___x_4834_ = 32u64;
    v___x_4835_ = lean_uint64_shift_right(v___x_4833_, v___x_4834_);
    v_fold_4836_ = lean_uint64_xor(v___x_4833_, v___x_4835_);
    v___x_4837_ = 16u64;
    v___x_4838_ = lean_uint64_shift_right(v_fold_4836_, v___x_4837_);
    v___x_4839_ = lean_uint64_xor(v_fold_4836_, v___x_4838_);
    v___x_4840_ = lean_uint64_to_usize(v___x_4839_);
    v___x_4841_ = lean_usize_of_nat(v___x_4832_);
    v___x_4842_ = 1usize;
    v___x_4843_ = lean_usize_sub(v___x_4841_, v___x_4842_);
    v___x_4844_ = lean_usize_land(v___x_4840_, v___x_4843_);
    v___x_4845_ = lean_array_uget_borrowed(v_buckets_4831_, v___x_4844_);
    v___x_4846_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__6_spec__14___redArg(v_a_4830_, v___x_4845_);
    return v___x_4846_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__6___redArg___boxed(
    mut v_m_4847_: *mut crate::leanh::LeanObject,
    mut v_a_4848_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4849_: u8 = 0;
    let mut v_r_4850_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4849_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__6___redArg(v_m_4847_, v_a_4848_);
    crate::leanh::lean_dec_ref(v_a_4848_);
    crate::leanh::lean_dec_ref(v_m_4847_);
    v_r_4850_ = crate::leanh::lean_box((v_res_4849_) as usize);
    return v_r_4850_;
}
pub unsafe fn l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1(
    mut v_mvarId_4855_: *mut crate::leanh::LeanObject,
    mut v_e_4856_: *mut crate::leanh::LeanObject,
    mut v_a_4857_: *mut crate::leanh::LeanObject,
    mut v___y_4858_: *mut crate::leanh::LeanObject,
    mut v___y_4859_: *mut crate::leanh::LeanObject,
    mut v___y_4860_: *mut crate::leanh::LeanObject,
    mut v___y_4861_: *mut crate::leanh::LeanObject,
    mut v___y_4862_: *mut crate::leanh::LeanObject,
    mut v___y_4863_: *mut crate::leanh::LeanObject,
    mut v___y_4864_: *mut crate::leanh::LeanObject,
    mut v___y_4865_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_d_4868_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_b_4869_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4870_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4871_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4872_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_4873_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_4874_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4876_: u8 = 0;
    let mut v___x_4877_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4878_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4879_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4880_: u8 = 0;
    let mut v___x_4881_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4882_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_struct_4883_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_binderType_4885_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_body_4886_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_binderType_4887_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_body_4888_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_type_4889_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_4890_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_body_4891_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4892_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4893_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_4894_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_4895_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4896_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4897_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_4898_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_4899_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_expr_4901_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fn_4903_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_arg_4904_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4905_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4906_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_4907_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_4908_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mvarId_4910_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4911_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4912_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4913_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4914_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4915_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4916_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4917_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4876_ = l_Lean_Expr_hasExprMVar(v_e_4856_);
                if v___x_4876_ == 0 {
                    crate::leanh::lean_dec_ref(v_e_4856_);
                    v___x_4877_ = l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__8___closed__0;
                    v___x_4878_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_4878_, 0, v___x_4877_);
                    crate::leanh::lean_ctor_set(v___x_4878_, 1, v_a_4857_);
                    v___x_4879_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_4879_, 0, v___x_4878_);
                    return v___x_4879_;
                } else {
                    v___x_4880_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__6___redArg(v_a_4857_, v_e_4856_);
                    if v___x_4880_ == 0 {
                        v___x_4881_ = crate::leanh::lean_box(0);
                        crate::leanh::lean_inc_ref(v_e_4856_);
                        v___x_4882_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__7___redArg(v_a_4857_, v_e_4856_, v___x_4881_);
                        match crate::leanh::lean_obj_tag(v_e_4856_) {
                            11 => {
                                v_struct_4883_ = crate::leanh::lean_ctor_get(v_e_4856_, 2);
                                crate::leanh::lean_inc_ref(v_struct_4883_);
                                crate::leanh::lean_dec_ref_known(v_e_4856_, 3);
                                v_e_4856_ = v_struct_4883_;
                                v_a_4857_ = v___x_4882_;
                                state = 0;
                                continue;
                            }
                            7 => {
                                v_binderType_4885_ = crate::leanh::lean_ctor_get(v_e_4856_, 1);
                                crate::leanh::lean_inc_ref(v_binderType_4885_);
                                v_body_4886_ = crate::leanh::lean_ctor_get(v_e_4856_, 2);
                                crate::leanh::lean_inc_ref(v_body_4886_);
                                crate::leanh::lean_dec_ref_known(v_e_4856_, 3);
                                v_d_4868_ = v_binderType_4885_;
                                v_b_4869_ = v_body_4886_;
                                v___y_4870_ = v___x_4882_;
                                state = 1;
                                continue;
                            }
                            6 => {
                                v_binderType_4887_ = crate::leanh::lean_ctor_get(v_e_4856_, 1);
                                crate::leanh::lean_inc_ref(v_binderType_4887_);
                                v_body_4888_ = crate::leanh::lean_ctor_get(v_e_4856_, 2);
                                crate::leanh::lean_inc_ref(v_body_4888_);
                                crate::leanh::lean_dec_ref_known(v_e_4856_, 3);
                                v_d_4868_ = v_binderType_4887_;
                                v_b_4869_ = v_body_4888_;
                                v___y_4870_ = v___x_4882_;
                                state = 1;
                                continue;
                            }
                            8 => {
                                v_type_4889_ = crate::leanh::lean_ctor_get(v_e_4856_, 1);
                                crate::leanh::lean_inc_ref(v_type_4889_);
                                v_value_4890_ = crate::leanh::lean_ctor_get(v_e_4856_, 2);
                                crate::leanh::lean_inc_ref(v_value_4890_);
                                v_body_4891_ = crate::leanh::lean_ctor_get(v_e_4856_, 3);
                                crate::leanh::lean_inc_ref(v_body_4891_);
                                crate::leanh::lean_dec_ref_known(v_e_4856_, 4);
                                v___x_4892_ = l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1(v_mvarId_4855_, v_type_4889_, v___x_4882_, v___y_4858_, v___y_4859_, v___y_4860_, v___y_4861_, v___y_4862_, v___y_4863_, v___y_4864_, v___y_4865_);
                                if crate::leanh::lean_obj_tag(v___x_4892_) == 0 {
                                    v_a_4893_ = crate::leanh::lean_ctor_get(v___x_4892_, 0);
                                    crate::leanh::lean_inc(v_a_4893_);
                                    v_fst_4894_ = crate::leanh::lean_ctor_get(v_a_4893_, 0);
                                    if crate::leanh::lean_obj_tag(v_fst_4894_) == 0 {
                                        crate::leanh::lean_dec(v_a_4893_);
                                        crate::leanh::lean_dec_ref(v_body_4891_);
                                        crate::leanh::lean_dec_ref(v_value_4890_);
                                        return v___x_4892_;
                                    } else {
                                        crate::leanh::lean_dec_ref_known(v___x_4892_, 1);
                                        v_snd_4895_ = crate::leanh::lean_ctor_get(v_a_4893_, 1);
                                        crate::leanh::lean_inc(v_snd_4895_);
                                        crate::leanh::lean_dec(v_a_4893_);
                                        v___x_4896_ = l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1(v_mvarId_4855_, v_value_4890_, v_snd_4895_, v___y_4858_, v___y_4859_, v___y_4860_, v___y_4861_, v___y_4862_, v___y_4863_, v___y_4864_, v___y_4865_);
                                        if crate::leanh::lean_obj_tag(v___x_4896_) == 0 {
                                            v_a_4897_ = crate::leanh::lean_ctor_get(v___x_4896_, 0);
                                            crate::leanh::lean_inc(v_a_4897_);
                                            v_fst_4898_ = crate::leanh::lean_ctor_get(v_a_4897_, 0);
                                            if crate::leanh::lean_obj_tag(v_fst_4898_) == 0 {
                                                crate::leanh::lean_dec(v_a_4897_);
                                                crate::leanh::lean_dec_ref(v_body_4891_);
                                                return v___x_4896_;
                                            } else {
                                                crate::leanh::lean_dec_ref_known(v___x_4896_, 1);
                                                v_snd_4899_ =
                                                    crate::leanh::lean_ctor_get(v_a_4897_, 1);
                                                crate::leanh::lean_inc(v_snd_4899_);
                                                crate::leanh::lean_dec(v_a_4897_);
                                                v_e_4856_ = v_body_4891_;
                                                v_a_4857_ = v_snd_4899_;
                                                state = 0;
                                                continue;
                                            }
                                        } else {
                                            crate::leanh::lean_dec_ref(v_body_4891_);
                                            return v___x_4896_;
                                        }
                                    }
                                } else {
                                    crate::leanh::lean_dec_ref(v_body_4891_);
                                    crate::leanh::lean_dec_ref(v_value_4890_);
                                    return v___x_4892_;
                                }
                            }
                            10 => {
                                v_expr_4901_ = crate::leanh::lean_ctor_get(v_e_4856_, 1);
                                crate::leanh::lean_inc_ref(v_expr_4901_);
                                crate::leanh::lean_dec_ref_known(v_e_4856_, 2);
                                v_e_4856_ = v_expr_4901_;
                                v_a_4857_ = v___x_4882_;
                                state = 0;
                                continue;
                            }
                            5 => {
                                v_fn_4903_ = crate::leanh::lean_ctor_get(v_e_4856_, 0);
                                crate::leanh::lean_inc_ref(v_fn_4903_);
                                v_arg_4904_ = crate::leanh::lean_ctor_get(v_e_4856_, 1);
                                crate::leanh::lean_inc_ref(v_arg_4904_);
                                crate::leanh::lean_dec_ref_known(v_e_4856_, 2);
                                v___x_4905_ = l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1(v_mvarId_4855_, v_fn_4903_, v___x_4882_, v___y_4858_, v___y_4859_, v___y_4860_, v___y_4861_, v___y_4862_, v___y_4863_, v___y_4864_, v___y_4865_);
                                if crate::leanh::lean_obj_tag(v___x_4905_) == 0 {
                                    v_a_4906_ = crate::leanh::lean_ctor_get(v___x_4905_, 0);
                                    crate::leanh::lean_inc(v_a_4906_);
                                    v_fst_4907_ = crate::leanh::lean_ctor_get(v_a_4906_, 0);
                                    if crate::leanh::lean_obj_tag(v_fst_4907_) == 0 {
                                        crate::leanh::lean_dec(v_a_4906_);
                                        crate::leanh::lean_dec_ref(v_arg_4904_);
                                        return v___x_4905_;
                                    } else {
                                        crate::leanh::lean_dec_ref_known(v___x_4905_, 1);
                                        v_snd_4908_ = crate::leanh::lean_ctor_get(v_a_4906_, 1);
                                        crate::leanh::lean_inc(v_snd_4908_);
                                        crate::leanh::lean_dec(v_a_4906_);
                                        v_e_4856_ = v_arg_4904_;
                                        v_a_4857_ = v_snd_4908_;
                                        state = 0;
                                        continue;
                                    }
                                } else {
                                    crate::leanh::lean_dec_ref(v_arg_4904_);
                                    return v___x_4905_;
                                }
                            }
                            2 => {
                                v_mvarId_4910_ = crate::leanh::lean_ctor_get(v_e_4856_, 0);
                                crate::leanh::lean_inc(v_mvarId_4910_);
                                crate::leanh::lean_dec_ref_known(v_e_4856_, 1);
                                v___x_4911_ = l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__8(v_mvarId_4855_, v_mvarId_4910_, v___x_4882_, v___y_4858_, v___y_4859_, v___y_4860_, v___y_4861_, v___y_4862_, v___y_4863_, v___y_4864_, v___y_4865_);
                                return v___x_4911_;
                            }
                            _ => {
                                crate::leanh::lean_dec_ref(v_e_4856_);
                                v___x_4912_ = l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__8___closed__0;
                                v___x_4913_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                                crate::leanh::lean_ctor_set(v___x_4913_, 0, v___x_4912_);
                                crate::leanh::lean_ctor_set(v___x_4913_, 1, v___x_4882_);
                                v___x_4914_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                                crate::leanh::lean_ctor_set(v___x_4914_, 0, v___x_4913_);
                                return v___x_4914_;
                            }
                        }
                    } else {
                        crate::leanh::lean_dec_ref(v_e_4856_);
                        v___x_4915_ = l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__8___closed__0;
                        v___x_4916_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_4916_, 0, v___x_4915_);
                        crate::leanh::lean_ctor_set(v___x_4916_, 1, v_a_4857_);
                        v___x_4917_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_4917_, 0, v___x_4916_);
                        return v___x_4917_;
                    }
                }
            }
            1 => {
                v___x_4871_ = l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1(v_mvarId_4855_, v_d_4868_, v___y_4870_, v___y_4858_, v___y_4859_, v___y_4860_, v___y_4861_, v___y_4862_, v___y_4863_, v___y_4864_, v___y_4865_);
                if crate::leanh::lean_obj_tag(v___x_4871_) == 0 {
                    v_a_4872_ = crate::leanh::lean_ctor_get(v___x_4871_, 0);
                    crate::leanh::lean_inc(v_a_4872_);
                    v_fst_4873_ = crate::leanh::lean_ctor_get(v_a_4872_, 0);
                    if crate::leanh::lean_obj_tag(v_fst_4873_) == 0 {
                        crate::leanh::lean_dec(v_a_4872_);
                        crate::leanh::lean_dec_ref(v_b_4869_);
                        return v___x_4871_;
                    } else {
                        crate::leanh::lean_dec_ref_known(v___x_4871_, 1);
                        v_snd_4874_ = crate::leanh::lean_ctor_get(v_a_4872_, 1);
                        crate::leanh::lean_inc(v_snd_4874_);
                        crate::leanh::lean_dec(v_a_4872_);
                        v_e_4856_ = v_b_4869_;
                        v_a_4857_ = v_snd_4874_;
                        state = 0;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_b_4869_);
                    return v___x_4871_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__8(
    mut v_mvarId_4918_: *mut crate::leanh::LeanObject,
    mut v_mvarId_x27_4919_: *mut crate::leanh::LeanObject,
    mut v_a_4920_: *mut crate::leanh::LeanObject,
    mut v___y_4921_: *mut crate::leanh::LeanObject,
    mut v___y_4922_: *mut crate::leanh::LeanObject,
    mut v___y_4923_: *mut crate::leanh::LeanObject,
    mut v___y_4924_: *mut crate::leanh::LeanObject,
    mut v___y_4925_: *mut crate::leanh::LeanObject,
    mut v___y_4926_: *mut crate::leanh::LeanObject,
    mut v___y_4927_: *mut crate::leanh::LeanObject,
    mut v___y_4928_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4930_: u8 = 0;
    let mut v___x_4931_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4932_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4934_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4935_: u8 = 0;
    let mut v_fst_4936_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_4937_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4939_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4940_: u8 = 0;
    let mut v_a_4941_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4943_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4944_: u8 = 0;
    let mut v___x_4946_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4948_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4950_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4951_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4952_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4953_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4954_: u8 = 0;
    let mut v_isSharedCheck_4955_: u8 = 0;
    let mut v_unused_4956_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4957_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_4958_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4959_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4960_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4962_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4963_: u8 = 0;
    let mut v_fst_4964_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_4965_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4967_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4968_: u8 = 0;
    let mut v_a_4969_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4971_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4972_: u8 = 0;
    let mut v___x_4974_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4976_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4978_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4979_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4980_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4981_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4982_: u8 = 0;
    let mut v_isSharedCheck_4983_: u8 = 0;
    let mut v_unused_4984_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4985_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_4986_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4988_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4989_: u8 = 0;
    let mut v___x_4990_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4992_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4994_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4995_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4996_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4997_: u8 = 0;
    let mut v_unused_4998_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_4999_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_5000_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mvarIdPending_5001_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5003_: u8 = 0;
    let mut v_a_5004_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5006_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5007_: u8 = 0;
    let mut v___x_5009_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5010_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5011_: u8 = 0;
    let mut v_snd_5012_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_5013_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5014_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5015_: u8 = 0;
    let mut v_a_5016_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5018_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5019_: u8 = 0;
    let mut v___x_5021_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5022_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5023_: u8 = 0;
    let mut v___x_5024_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5025_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5026_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4930_ = l_Lean_instBEqMVarId_beq(v_mvarId_4918_, v_mvarId_x27_4919_);
                if v___x_4930_ == 0 {
                    v___x_4931_ = l_Lean_getExprMVarAssignment_x3f___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__8_spec__18___redArg(v_mvarId_x27_4919_, v_a_4920_, v___y_4926_);
                    if crate::leanh::lean_obj_tag(v___x_4931_) == 0 {
                        v_a_4932_ = crate::leanh::lean_ctor_get(v___x_4931_, 0);
                        v_isSharedCheck_5015_ =
                            (!crate::leanh::lean_is_exclusive(v___x_4931_)) as u8;
                        if v_isSharedCheck_5015_ == 0 {
                            v___x_4934_ = v___x_4931_;
                            v_isShared_4935_ = v_isSharedCheck_5015_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_4932_);
                            crate::leanh::lean_dec(v___x_4931_);
                            v___x_4934_ = crate::leanh::lean_box(0);
                            v_isShared_4935_ = v_isSharedCheck_5015_;
                            state = 1;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec(v_mvarId_x27_4919_);
                        v_a_5016_ = crate::leanh::lean_ctor_get(v___x_4931_, 0);
                        v_isSharedCheck_5023_ =
                            (!crate::leanh::lean_is_exclusive(v___x_4931_)) as u8;
                        if v_isSharedCheck_5023_ == 0 {
                            v___x_5018_ = v___x_4931_;
                            v_isShared_5019_ = v_isSharedCheck_5023_;
                            state = 18;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_5016_);
                            crate::leanh::lean_dec(v___x_4931_);
                            v___x_5018_ = crate::leanh::lean_box(0);
                            v_isShared_5019_ = v_isSharedCheck_5023_;
                            state = 18;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec(v_mvarId_x27_4919_);
                    v___x_5024_ = l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__8___closed__1;
                    v___x_5025_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_5025_, 0, v___x_5024_);
                    crate::leanh::lean_ctor_set(v___x_5025_, 1, v_a_4920_);
                    v___x_5026_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_5026_, 0, v___x_5025_);
                    return v___x_5026_;
                }
            }
            1 => {
                v_fst_4936_ = crate::leanh::lean_ctor_get(v_a_4932_, 0);
                crate::leanh::lean_inc(v_fst_4936_);
                if crate::leanh::lean_obj_tag(v_fst_4936_) == 0 {
                    crate::leanh::lean_dec(v_mvarId_x27_4919_);
                    v_snd_4937_ = crate::leanh::lean_ctor_get(v_a_4932_, 1);
                    v_isSharedCheck_4955_ = (!crate::leanh::lean_is_exclusive(v_a_4932_)) as u8;
                    if v_isSharedCheck_4955_ == 0 {
                        v_unused_4956_ = crate::leanh::lean_ctor_get(v_a_4932_, 0);
                        crate::leanh::lean_dec(v_unused_4956_);
                        v___x_4939_ = v_a_4932_;
                        v_isShared_4940_ = v_isSharedCheck_4955_;
                        state = 2;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_snd_4937_);
                        crate::leanh::lean_dec(v_a_4932_);
                        v___x_4939_ = crate::leanh::lean_box(0);
                        v_isShared_4940_ = v_isSharedCheck_4955_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_4934_);
                    v_a_4957_ = crate::leanh::lean_ctor_get(v_fst_4936_, 0);
                    crate::leanh::lean_inc(v_a_4957_);
                    crate::leanh::lean_dec_ref_known(v_fst_4936_, 1);
                    if crate::leanh::lean_obj_tag(v_a_4957_) == 0 {
                        v_snd_4958_ = crate::leanh::lean_ctor_get(v_a_4932_, 1);
                        crate::leanh::lean_inc(v_snd_4958_);
                        crate::leanh::lean_dec(v_a_4932_);
                        v___x_4959_ = l_Lean_getDelayedMVarAssignment_x3f___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__8_spec__19___redArg(v_mvarId_x27_4919_, v_snd_4958_, v___y_4926_);
                        crate::leanh::lean_dec(v_mvarId_x27_4919_);
                        if crate::leanh::lean_obj_tag(v___x_4959_) == 0 {
                            v_a_4960_ = crate::leanh::lean_ctor_get(v___x_4959_, 0);
                            v_isSharedCheck_5003_ =
                                (!crate::leanh::lean_is_exclusive(v___x_4959_)) as u8;
                            if v_isSharedCheck_5003_ == 0 {
                                v___x_4962_ = v___x_4959_;
                                v_isShared_4963_ = v_isSharedCheck_5003_;
                                state = 7;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_4960_);
                                crate::leanh::lean_dec(v___x_4959_);
                                v___x_4962_ = crate::leanh::lean_box(0);
                                v_isShared_4963_ = v_isSharedCheck_5003_;
                                state = 7;
                                continue;
                            }
                        } else {
                            v_a_5004_ = crate::leanh::lean_ctor_get(v___x_4959_, 0);
                            v_isSharedCheck_5011_ =
                                (!crate::leanh::lean_is_exclusive(v___x_4959_)) as u8;
                            if v_isSharedCheck_5011_ == 0 {
                                v___x_5006_ = v___x_4959_;
                                v_isShared_5007_ = v_isSharedCheck_5011_;
                                state = 16;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_5004_);
                                crate::leanh::lean_dec(v___x_4959_);
                                v___x_5006_ = crate::leanh::lean_box(0);
                                v_isShared_5007_ = v_isSharedCheck_5011_;
                                state = 16;
                                continue;
                            }
                        }
                    } else {
                        crate::leanh::lean_dec(v_mvarId_x27_4919_);
                        v_snd_5012_ = crate::leanh::lean_ctor_get(v_a_4932_, 1);
                        crate::leanh::lean_inc(v_snd_5012_);
                        crate::leanh::lean_dec(v_a_4932_);
                        v_val_5013_ = crate::leanh::lean_ctor_get(v_a_4957_, 0);
                        crate::leanh::lean_inc(v_val_5013_);
                        crate::leanh::lean_dec_ref_known(v_a_4957_, 1);
                        v___x_5014_ = l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1(v_mvarId_4918_, v_val_5013_, v_snd_5012_, v___y_4921_, v___y_4922_, v___y_4923_, v___y_4924_, v___y_4925_, v___y_4926_, v___y_4927_, v___y_4928_);
                        return v___x_5014_;
                    }
                }
            }
            2 => {
                v_a_4941_ = crate::leanh::lean_ctor_get(v_fst_4936_, 0);
                v_isSharedCheck_4954_ = (!crate::leanh::lean_is_exclusive(v_fst_4936_)) as u8;
                if v_isSharedCheck_4954_ == 0 {
                    v___x_4943_ = v_fst_4936_;
                    v_isShared_4944_ = v_isSharedCheck_4954_;
                    state = 3;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_a_4941_);
                    crate::leanh::lean_dec(v_fst_4936_);
                    v___x_4943_ = crate::leanh::lean_box(0);
                    v_isShared_4944_ = v_isSharedCheck_4954_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_4944_ == 0 {
                    v___x_4946_ = v___x_4943_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4953_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4953_, 0, v_a_4941_);
                    v___x_4946_ = v_reuseFailAlloc_4953_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                if v_isShared_4940_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4939_, 0, v___x_4946_);
                    v___x_4948_ = v___x_4939_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_4952_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4952_, 0, v___x_4946_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4952_, 1, v_snd_4937_);
                    v___x_4948_ = v_reuseFailAlloc_4952_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                if v_isShared_4935_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4934_, 0, v___x_4948_);
                    v___x_4950_ = v___x_4934_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_4951_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4951_, 0, v___x_4948_);
                    v___x_4950_ = v_reuseFailAlloc_4951_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_4950_;
            }
            7 => {
                v_fst_4964_ = crate::leanh::lean_ctor_get(v_a_4960_, 0);
                crate::leanh::lean_inc(v_fst_4964_);
                if crate::leanh::lean_obj_tag(v_fst_4964_) == 0 {
                    v_snd_4965_ = crate::leanh::lean_ctor_get(v_a_4960_, 1);
                    v_isSharedCheck_4983_ = (!crate::leanh::lean_is_exclusive(v_a_4960_)) as u8;
                    if v_isSharedCheck_4983_ == 0 {
                        v_unused_4984_ = crate::leanh::lean_ctor_get(v_a_4960_, 0);
                        crate::leanh::lean_dec(v_unused_4984_);
                        v___x_4967_ = v_a_4960_;
                        v_isShared_4968_ = v_isSharedCheck_4983_;
                        state = 8;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_snd_4965_);
                        crate::leanh::lean_dec(v_a_4960_);
                        v___x_4967_ = crate::leanh::lean_box(0);
                        v_isShared_4968_ = v_isSharedCheck_4983_;
                        state = 8;
                        continue;
                    }
                } else {
                    v_a_4985_ = crate::leanh::lean_ctor_get(v_fst_4964_, 0);
                    crate::leanh::lean_inc(v_a_4985_);
                    crate::leanh::lean_dec_ref_known(v_fst_4964_, 1);
                    if crate::leanh::lean_obj_tag(v_a_4985_) == 0 {
                        v_snd_4986_ = crate::leanh::lean_ctor_get(v_a_4960_, 1);
                        v_isSharedCheck_4997_ = (!crate::leanh::lean_is_exclusive(v_a_4960_)) as u8;
                        if v_isSharedCheck_4997_ == 0 {
                            v_unused_4998_ = crate::leanh::lean_ctor_get(v_a_4960_, 0);
                            crate::leanh::lean_dec(v_unused_4998_);
                            v___x_4988_ = v_a_4960_;
                            v_isShared_4989_ = v_isSharedCheck_4997_;
                            state = 13;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_snd_4986_);
                            crate::leanh::lean_dec(v_a_4960_);
                            v___x_4988_ = crate::leanh::lean_box(0);
                            v_isShared_4989_ = v_isSharedCheck_4997_;
                            state = 13;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_del_object(v___x_4962_);
                        v_val_4999_ = crate::leanh::lean_ctor_get(v_a_4985_, 0);
                        crate::leanh::lean_inc(v_val_4999_);
                        crate::leanh::lean_dec_ref_known(v_a_4985_, 1);
                        v_snd_5000_ = crate::leanh::lean_ctor_get(v_a_4960_, 1);
                        crate::leanh::lean_inc(v_snd_5000_);
                        crate::leanh::lean_dec(v_a_4960_);
                        v_mvarIdPending_5001_ = crate::leanh::lean_ctor_get(v_val_4999_, 1);
                        crate::leanh::lean_inc(v_mvarIdPending_5001_);
                        crate::leanh::lean_dec(v_val_4999_);
                        v_mvarId_x27_4919_ = v_mvarIdPending_5001_;
                        v_a_4920_ = v_snd_5000_;
                        state = 0;
                        continue;
                    }
                }
            }
            8 => {
                v_a_4969_ = crate::leanh::lean_ctor_get(v_fst_4964_, 0);
                v_isSharedCheck_4982_ = (!crate::leanh::lean_is_exclusive(v_fst_4964_)) as u8;
                if v_isSharedCheck_4982_ == 0 {
                    v___x_4971_ = v_fst_4964_;
                    v_isShared_4972_ = v_isSharedCheck_4982_;
                    state = 9;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_a_4969_);
                    crate::leanh::lean_dec(v_fst_4964_);
                    v___x_4971_ = crate::leanh::lean_box(0);
                    v_isShared_4972_ = v_isSharedCheck_4982_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                if v_isShared_4972_ == 0 {
                    v___x_4974_ = v___x_4971_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_4981_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4981_, 0, v_a_4969_);
                    v___x_4974_ = v_reuseFailAlloc_4981_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                if v_isShared_4968_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4967_, 0, v___x_4974_);
                    v___x_4976_ = v___x_4967_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_4980_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4980_, 0, v___x_4974_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4980_, 1, v_snd_4965_);
                    v___x_4976_ = v_reuseFailAlloc_4980_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                if v_isShared_4963_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4962_, 0, v___x_4976_);
                    v___x_4978_ = v___x_4962_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_4979_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4979_, 0, v___x_4976_);
                    v___x_4978_ = v_reuseFailAlloc_4979_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                return v___x_4978_;
            }
            13 => {
                v___x_4990_ = l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__8___closed__0;
                if v_isShared_4989_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4988_, 0, v___x_4990_);
                    v___x_4992_ = v___x_4988_;
                    state = 14;
                    continue;
                } else {
                    v_reuseFailAlloc_4996_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4996_, 0, v___x_4990_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4996_, 1, v_snd_4986_);
                    v___x_4992_ = v_reuseFailAlloc_4996_;
                    state = 14;
                    continue;
                }
            }
            14 => {
                if v_isShared_4963_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4962_, 0, v___x_4992_);
                    v___x_4994_ = v___x_4962_;
                    state = 15;
                    continue;
                } else {
                    v_reuseFailAlloc_4995_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4995_, 0, v___x_4992_);
                    v___x_4994_ = v_reuseFailAlloc_4995_;
                    state = 15;
                    continue;
                }
            }
            15 => {
                return v___x_4994_;
            }
            16 => {
                if v_isShared_5007_ == 0 {
                    v___x_5009_ = v___x_5006_;
                    state = 17;
                    continue;
                } else {
                    v_reuseFailAlloc_5010_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5010_, 0, v_a_5004_);
                    v___x_5009_ = v_reuseFailAlloc_5010_;
                    state = 17;
                    continue;
                }
            }
            17 => {
                return v___x_5009_;
            }
            18 => {
                if v_isShared_5019_ == 0 {
                    v___x_5021_ = v___x_5018_;
                    state = 19;
                    continue;
                } else {
                    v_reuseFailAlloc_5022_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5022_, 0, v_a_5016_);
                    v___x_5021_ = v_reuseFailAlloc_5022_;
                    state = 19;
                    continue;
                }
            }
            19 => {
                return v___x_5021_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__8___boxed(
    mut v_mvarId_5027_: *mut crate::leanh::LeanObject,
    mut v_mvarId_x27_5028_: *mut crate::leanh::LeanObject,
    mut v_a_5029_: *mut crate::leanh::LeanObject,
    mut v___y_5030_: *mut crate::leanh::LeanObject,
    mut v___y_5031_: *mut crate::leanh::LeanObject,
    mut v___y_5032_: *mut crate::leanh::LeanObject,
    mut v___y_5033_: *mut crate::leanh::LeanObject,
    mut v___y_5034_: *mut crate::leanh::LeanObject,
    mut v___y_5035_: *mut crate::leanh::LeanObject,
    mut v___y_5036_: *mut crate::leanh::LeanObject,
    mut v___y_5037_: *mut crate::leanh::LeanObject,
    mut v___y_5038_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5039_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5039_ = l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__8(v_mvarId_5027_, v_mvarId_x27_5028_, v_a_5029_, v___y_5030_, v___y_5031_, v___y_5032_, v___y_5033_, v___y_5034_, v___y_5035_, v___y_5036_, v___y_5037_);
    crate::leanh::lean_dec(v___y_5037_);
    crate::leanh::lean_dec_ref(v___y_5036_);
    crate::leanh::lean_dec(v___y_5035_);
    crate::leanh::lean_dec_ref(v___y_5034_);
    crate::leanh::lean_dec(v___y_5033_);
    crate::leanh::lean_dec_ref(v___y_5032_);
    crate::leanh::lean_dec(v___y_5031_);
    crate::leanh::lean_dec_ref(v___y_5030_);
    crate::leanh::lean_dec(v_mvarId_5027_);
    return v_res_5039_;
}
pub unsafe fn l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1___boxed(
    mut v_mvarId_5040_: *mut crate::leanh::LeanObject,
    mut v_e_5041_: *mut crate::leanh::LeanObject,
    mut v_a_5042_: *mut crate::leanh::LeanObject,
    mut v___y_5043_: *mut crate::leanh::LeanObject,
    mut v___y_5044_: *mut crate::leanh::LeanObject,
    mut v___y_5045_: *mut crate::leanh::LeanObject,
    mut v___y_5046_: *mut crate::leanh::LeanObject,
    mut v___y_5047_: *mut crate::leanh::LeanObject,
    mut v___y_5048_: *mut crate::leanh::LeanObject,
    mut v___y_5049_: *mut crate::leanh::LeanObject,
    mut v___y_5050_: *mut crate::leanh::LeanObject,
    mut v___y_5051_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5052_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5052_ = l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1(v_mvarId_5040_, v_e_5041_, v_a_5042_, v___y_5043_, v___y_5044_, v___y_5045_, v___y_5046_, v___y_5047_, v___y_5048_, v___y_5049_, v___y_5050_);
    crate::leanh::lean_dec(v___y_5050_);
    crate::leanh::lean_dec_ref(v___y_5049_);
    crate::leanh::lean_dec(v___y_5048_);
    crate::leanh::lean_dec_ref(v___y_5047_);
    crate::leanh::lean_dec(v___y_5046_);
    crate::leanh::lean_dec_ref(v___y_5045_);
    crate::leanh::lean_dec(v___y_5044_);
    crate::leanh::lean_dec_ref(v___y_5043_);
    crate::leanh::lean_dec(v_mvarId_5040_);
    return v_res_5052_;
}
pub unsafe fn _init_l_Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_5053_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5054_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5055_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5053_ = crate::leanh::lean_box(0);
    v___x_5054_ = crate::leanh::lean_unsigned_to_nat(16);
    v___x_5055_ = lean_mk_array(v___x_5054_, v___x_5053_);
    return v___x_5055_;
}
pub unsafe fn _init_l_Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_5056_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5057_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5058_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5056_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1___closed__0), core::ptr::addr_of_mut!(l_Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1___closed__0_once), _init_l_Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1___closed__0);
    v___x_5057_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_5058_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_5058_, 0, v___x_5057_);
    crate::leanh::lean_ctor_set(v___x_5058_, 1, v___x_5056_);
    return v___x_5058_;
}
pub unsafe fn l_Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1(
    mut v_mvarId_5059_: *mut crate::leanh::LeanObject,
    mut v_e_5060_: *mut crate::leanh::LeanObject,
    mut v___y_5061_: *mut crate::leanh::LeanObject,
    mut v___y_5062_: *mut crate::leanh::LeanObject,
    mut v___y_5063_: *mut crate::leanh::LeanObject,
    mut v___y_5064_: *mut crate::leanh::LeanObject,
    mut v___y_5065_: *mut crate::leanh::LeanObject,
    mut v___y_5066_: *mut crate::leanh::LeanObject,
    mut v___y_5067_: *mut crate::leanh::LeanObject,
    mut v___y_5068_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5070_: u8 = 0;
    let mut v___x_5071_: u8 = 0;
    let mut v___x_5072_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5073_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5074_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5075_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5076_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5078_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5079_: u8 = 0;
    let mut v_fst_5080_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5081_: u8 = 0;
    let mut v___x_5082_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5084_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5085_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5086_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5088_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5089_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5090_: u8 = 0;
    let mut v_a_5091_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5093_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5094_: u8 = 0;
    let mut v___x_5096_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5097_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5098_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5070_ = l_Lean_Expr_hasExprMVar(v_e_5060_);
                if v___x_5070_ == 0 {
                    crate::leanh::lean_dec_ref(v_e_5060_);
                    v___x_5071_ = 1;
                    v___x_5072_ = crate::leanh::lean_box((v___x_5071_) as usize);
                    v___x_5073_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_5073_, 0, v___x_5072_);
                    return v___x_5073_;
                } else {
                    v___x_5074_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1___closed__1), core::ptr::addr_of_mut!(l_Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1___closed__1_once), _init_l_Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1___closed__1);
                    v___x_5075_ = l___private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1(v_mvarId_5059_, v_e_5060_, v___x_5074_, v___y_5061_, v___y_5062_, v___y_5063_, v___y_5064_, v___y_5065_, v___y_5066_, v___y_5067_, v___y_5068_);
                    if crate::leanh::lean_obj_tag(v___x_5075_) == 0 {
                        v_a_5076_ = crate::leanh::lean_ctor_get(v___x_5075_, 0);
                        v_isSharedCheck_5090_ =
                            (!crate::leanh::lean_is_exclusive(v___x_5075_)) as u8;
                        if v_isSharedCheck_5090_ == 0 {
                            v___x_5078_ = v___x_5075_;
                            v_isShared_5079_ = v_isSharedCheck_5090_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_5076_);
                            crate::leanh::lean_dec(v___x_5075_);
                            v___x_5078_ = crate::leanh::lean_box(0);
                            v_isShared_5079_ = v_isSharedCheck_5090_;
                            state = 1;
                            continue;
                        }
                    } else {
                        v_a_5091_ = crate::leanh::lean_ctor_get(v___x_5075_, 0);
                        v_isSharedCheck_5098_ =
                            (!crate::leanh::lean_is_exclusive(v___x_5075_)) as u8;
                        if v_isSharedCheck_5098_ == 0 {
                            v___x_5093_ = v___x_5075_;
                            v_isShared_5094_ = v_isSharedCheck_5098_;
                            state = 4;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_5091_);
                            crate::leanh::lean_dec(v___x_5075_);
                            v___x_5093_ = crate::leanh::lean_box(0);
                            v_isShared_5094_ = v_isSharedCheck_5098_;
                            state = 4;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v_fst_5080_ = crate::leanh::lean_ctor_get(v_a_5076_, 0);
                crate::leanh::lean_inc(v_fst_5080_);
                crate::leanh::lean_dec(v_a_5076_);
                if crate::leanh::lean_obj_tag(v_fst_5080_) == 0 {
                    crate::leanh::lean_dec_ref_known(v_fst_5080_, 1);
                    v___x_5081_ = 0;
                    v___x_5082_ = crate::leanh::lean_box((v___x_5081_) as usize);
                    if v_isShared_5079_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_5078_, 0, v___x_5082_);
                        v___x_5084_ = v___x_5078_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_5085_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_5085_, 0, v___x_5082_);
                        v___x_5084_ = v_reuseFailAlloc_5085_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref_known(v_fst_5080_, 1);
                    v___x_5086_ = crate::leanh::lean_box((v___x_5070_) as usize);
                    if v_isShared_5079_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_5078_, 0, v___x_5086_);
                        v___x_5088_ = v___x_5078_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_5089_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_5089_, 0, v___x_5086_);
                        v___x_5088_ = v_reuseFailAlloc_5089_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_5084_;
            }
            3 => {
                return v___x_5088_;
            }
            4 => {
                if v_isShared_5094_ == 0 {
                    v___x_5096_ = v___x_5093_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_5097_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5097_, 0, v_a_5091_);
                    v___x_5096_ = v_reuseFailAlloc_5097_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_5096_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1___boxed(
    mut v_mvarId_5099_: *mut crate::leanh::LeanObject,
    mut v_e_5100_: *mut crate::leanh::LeanObject,
    mut v___y_5101_: *mut crate::leanh::LeanObject,
    mut v___y_5102_: *mut crate::leanh::LeanObject,
    mut v___y_5103_: *mut crate::leanh::LeanObject,
    mut v___y_5104_: *mut crate::leanh::LeanObject,
    mut v___y_5105_: *mut crate::leanh::LeanObject,
    mut v___y_5106_: *mut crate::leanh::LeanObject,
    mut v___y_5107_: *mut crate::leanh::LeanObject,
    mut v___y_5108_: *mut crate::leanh::LeanObject,
    mut v___y_5109_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5110_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5110_ = l_Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1(v_mvarId_5099_, v_e_5100_, v___y_5101_, v___y_5102_, v___y_5103_, v___y_5104_, v___y_5105_, v___y_5106_, v___y_5107_, v___y_5108_);
    crate::leanh::lean_dec(v___y_5108_);
    crate::leanh::lean_dec_ref(v___y_5107_);
    crate::leanh::lean_dec(v___y_5106_);
    crate::leanh::lean_dec_ref(v___y_5105_);
    crate::leanh::lean_dec(v___y_5104_);
    crate::leanh::lean_dec_ref(v___y_5103_);
    crate::leanh::lean_dec(v___y_5102_);
    crate::leanh::lean_dec_ref(v___y_5101_);
    crate::leanh::lean_dec(v_mvarId_5099_);
    return v_res_5110_;
}
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__6_spec__10(
    mut v_msgData_5111_: *mut crate::leanh::LeanObject,
    mut v___y_5112_: *mut crate::leanh::LeanObject,
    mut v___y_5113_: *mut crate::leanh::LeanObject,
    mut v___y_5114_: *mut crate::leanh::LeanObject,
    mut v___y_5115_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5117_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_5118_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5119_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_5120_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_lctx_5121_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_5122_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5123_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5124_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5125_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5117_ = lean_st_ref_get(v___y_5115_);
    v_env_5118_ = crate::leanh::lean_ctor_get(v___x_5117_, 0);
    crate::leanh::lean_inc_ref(v_env_5118_);
    crate::leanh::lean_dec(v___x_5117_);
    v___x_5119_ = lean_st_ref_get(v___y_5113_);
    v_mctx_5120_ = crate::leanh::lean_ctor_get(v___x_5119_, 0);
    crate::leanh::lean_inc_ref(v_mctx_5120_);
    crate::leanh::lean_dec(v___x_5119_);
    v_lctx_5121_ = crate::leanh::lean_ctor_get(v___y_5112_, 2);
    v_options_5122_ = crate::leanh::lean_ctor_get(v___y_5114_, 2);
    crate::leanh::lean_inc_ref(v_options_5122_);
    crate::leanh::lean_inc_ref(v_lctx_5121_);
    v___x_5123_ = crate::leanh::lean_alloc_ctor(0, 4, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_5123_, 0, v_env_5118_);
    crate::leanh::lean_ctor_set(v___x_5123_, 1, v_mctx_5120_);
    crate::leanh::lean_ctor_set(v___x_5123_, 2, v_lctx_5121_);
    crate::leanh::lean_ctor_set(v___x_5123_, 3, v_options_5122_);
    v___x_5124_ = crate::leanh::lean_alloc_ctor(3, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_5124_, 0, v___x_5123_);
    crate::leanh::lean_ctor_set(v___x_5124_, 1, v_msgData_5111_);
    v___x_5125_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_5125_, 0, v___x_5124_);
    return v___x_5125_;
}
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__6_spec__10___boxed(
    mut v_msgData_5126_: *mut crate::leanh::LeanObject,
    mut v___y_5127_: *mut crate::leanh::LeanObject,
    mut v___y_5128_: *mut crate::leanh::LeanObject,
    mut v___y_5129_: *mut crate::leanh::LeanObject,
    mut v___y_5130_: *mut crate::leanh::LeanObject,
    mut v___y_5131_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5132_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5132_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__6_spec__10(v_msgData_5126_, v___y_5127_, v___y_5128_, v___y_5129_, v___y_5130_);
    crate::leanh::lean_dec(v___y_5130_);
    crate::leanh::lean_dec_ref(v___y_5129_);
    crate::leanh::lean_dec(v___y_5128_);
    crate::leanh::lean_dec_ref(v___y_5127_);
    return v_res_5132_;
}
pub unsafe fn l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__6___redArg(
    mut v_msg_5133_: *mut crate::leanh::LeanObject,
    mut v___y_5134_: *mut crate::leanh::LeanObject,
    mut v___y_5135_: *mut crate::leanh::LeanObject,
    mut v___y_5136_: *mut crate::leanh::LeanObject,
    mut v___y_5137_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_ref_5139_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5140_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5141_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5143_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5144_: u8 = 0;
    let mut v___x_5145_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5147_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5148_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5149_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ref_5139_ = crate::leanh::lean_ctor_get(v___y_5136_, 5);
                v___x_5140_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__6_spec__10(v_msg_5133_, v___y_5134_, v___y_5135_, v___y_5136_, v___y_5137_);
                v_a_5141_ = crate::leanh::lean_ctor_get(v___x_5140_, 0);
                v_isSharedCheck_5149_ = (!crate::leanh::lean_is_exclusive(v___x_5140_)) as u8;
                if v_isSharedCheck_5149_ == 0 {
                    v___x_5143_ = v___x_5140_;
                    v_isShared_5144_ = v_isSharedCheck_5149_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_a_5141_);
                    crate::leanh::lean_dec(v___x_5140_);
                    v___x_5143_ = crate::leanh::lean_box(0);
                    v_isShared_5144_ = v_isSharedCheck_5149_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                crate::leanh::lean_inc(v_ref_5139_);
                v___x_5145_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_5145_, 0, v_ref_5139_);
                crate::leanh::lean_ctor_set(v___x_5145_, 1, v_a_5141_);
                if v_isShared_5144_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_5143_, 1);
                    crate::leanh::lean_ctor_set(v___x_5143_, 0, v___x_5145_);
                    v___x_5147_ = v___x_5143_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5148_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5148_, 0, v___x_5145_);
                    v___x_5147_ = v_reuseFailAlloc_5148_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_5147_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__6___redArg___boxed(
    mut v_msg_5150_: *mut crate::leanh::LeanObject,
    mut v___y_5151_: *mut crate::leanh::LeanObject,
    mut v___y_5152_: *mut crate::leanh::LeanObject,
    mut v___y_5153_: *mut crate::leanh::LeanObject,
    mut v___y_5154_: *mut crate::leanh::LeanObject,
    mut v___y_5155_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5156_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5156_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__6___redArg(v_msg_5150_, v___y_5151_, v___y_5152_, v___y_5153_, v___y_5154_);
    crate::leanh::lean_dec(v___y_5154_);
    crate::leanh::lean_dec_ref(v___y_5153_);
    crate::leanh::lean_dec(v___y_5152_);
    crate::leanh::lean_dec_ref(v___y_5151_);
    return v_res_5156_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__2_spec__3_spec__11_spec__22_spec__25___redArg(
    mut v_x_5157_: *mut crate::leanh::LeanObject,
    mut v_x_5158_: *mut crate::leanh::LeanObject,
    mut v_x_5159_: *mut crate::leanh::LeanObject,
    mut v_x_5160_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_ks_5161_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_vs_5162_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5164_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5165_: u8 = 0;
    let mut v___x_5166_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5167_: u8 = 0;
    let mut v___x_5168_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5169_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5171_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5172_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_x27_5173_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5174_: u8 = 0;
    let mut v___x_5176_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5177_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5178_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5180_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5181_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5182_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5184_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5185_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5186_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ks_5161_ = crate::leanh::lean_ctor_get(v_x_5157_, 0);
                v_vs_5162_ = crate::leanh::lean_ctor_get(v_x_5157_, 1);
                v_isSharedCheck_5186_ = (!crate::leanh::lean_is_exclusive(v_x_5157_)) as u8;
                if v_isSharedCheck_5186_ == 0 {
                    v___x_5164_ = v_x_5157_;
                    v_isShared_5165_ = v_isSharedCheck_5186_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_vs_5162_);
                    crate::leanh::lean_inc(v_ks_5161_);
                    crate::leanh::lean_dec(v_x_5157_);
                    v___x_5164_ = crate::leanh::lean_box(0);
                    v_isShared_5165_ = v_isSharedCheck_5186_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_5166_ = lean_array_get_size(v_ks_5161_);
                v___x_5167_ = lean_nat_dec_lt(v_x_5158_, v___x_5166_);
                if v___x_5167_ == 0 {
                    crate::leanh::lean_dec(v_x_5158_);
                    v___x_5168_ = lean_array_push(v_ks_5161_, v_x_5159_);
                    v___x_5169_ = lean_array_push(v_vs_5162_, v_x_5160_);
                    if v_isShared_5165_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_5164_, 1, v___x_5169_);
                        crate::leanh::lean_ctor_set(v___x_5164_, 0, v___x_5168_);
                        v___x_5171_ = v___x_5164_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_5172_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_5172_, 0, v___x_5168_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_5172_, 1, v___x_5169_);
                        v___x_5171_ = v_reuseFailAlloc_5172_;
                        state = 2;
                        continue;
                    }
                } else {
                    v_k_x27_5173_ = lean_array_fget_borrowed(v_ks_5161_, v_x_5158_);
                    v___x_5174_ = l_Lean_instBEqMVarId_beq(v_x_5159_, v_k_x27_5173_);
                    if v___x_5174_ == 0 {
                        if v_isShared_5165_ == 0 {
                            v___x_5176_ = v___x_5164_;
                            state = 3;
                            continue;
                        } else {
                            v_reuseFailAlloc_5180_ =
                                crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_5180_, 0, v_ks_5161_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_5180_, 1, v_vs_5162_);
                            v___x_5176_ = v_reuseFailAlloc_5180_;
                            state = 3;
                            continue;
                        }
                    } else {
                        v___x_5181_ = lean_array_fset(v_ks_5161_, v_x_5158_, v_x_5159_);
                        v___x_5182_ = lean_array_fset(v_vs_5162_, v_x_5158_, v_x_5160_);
                        crate::leanh::lean_dec(v_x_5158_);
                        if v_isShared_5165_ == 0 {
                            crate::leanh::lean_ctor_set(v___x_5164_, 1, v___x_5182_);
                            crate::leanh::lean_ctor_set(v___x_5164_, 0, v___x_5181_);
                            v___x_5184_ = v___x_5164_;
                            state = 4;
                            continue;
                        } else {
                            v_reuseFailAlloc_5185_ =
                                crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_5185_, 0, v___x_5181_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_5185_, 1, v___x_5182_);
                            v___x_5184_ = v_reuseFailAlloc_5185_;
                            state = 4;
                            continue;
                        }
                    }
                }
            }
            2 => {
                return v___x_5171_;
            }
            3 => {
                v___x_5177_ = crate::leanh::lean_unsigned_to_nat(1);
                v___x_5178_ = lean_nat_add(v_x_5158_, v___x_5177_);
                crate::leanh::lean_dec(v_x_5158_);
                v_x_5157_ = v___x_5176_;
                v_x_5158_ = v___x_5178_;
                state = 0;
                continue;
            }
            4 => {
                return v___x_5184_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__2_spec__3_spec__11_spec__22___redArg(
    mut v_n_5187_: *mut crate::leanh::LeanObject,
    mut v_k_5188_: *mut crate::leanh::LeanObject,
    mut v_v_5189_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5190_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5191_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5190_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_5191_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__2_spec__3_spec__11_spec__22_spec__25___redArg(v_n_5187_, v___x_5190_, v_k_5188_, v_v_5189_);
    return v___x_5191_;
}
pub unsafe fn _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__2_spec__3_spec__11___redArg___closed__0()
-> usize {
    let mut v___x_5192_: usize = 0;
    let mut v___x_5193_: usize = 0;
    let mut v___x_5194_: usize = 0;
    v___x_5192_ = 5usize;
    v___x_5193_ = 1usize;
    v___x_5194_ = lean_usize_shift_left(v___x_5193_, v___x_5192_);
    return v___x_5194_;
}
pub unsafe fn _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__2_spec__3_spec__11___redArg___closed__1()
-> usize {
    let mut v___x_5195_: usize = 0;
    let mut v___x_5196_: usize = 0;
    let mut v___x_5197_: usize = 0;
    v___x_5195_ = 1usize;
    v___x_5196_ = crate::leanh::lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__2_spec__3_spec__11___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__2_spec__3_spec__11___redArg___closed__0_once), _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__2_spec__3_spec__11___redArg___closed__0);
    v___x_5197_ = lean_usize_sub(v___x_5196_, v___x_5195_);
    return v___x_5197_;
}
pub unsafe fn _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__2_spec__3_spec__11___redArg___closed__2()
-> *mut crate::leanh::LeanObject {
    let mut v___x_5198_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5198_ = l_Lean_PersistentHashMap_mkEmptyEntries(
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
    );
    return v___x_5198_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__2_spec__3_spec__11___redArg(
    mut v_x_5199_: *mut crate::leanh::LeanObject,
    mut v_x_5200_: usize,
    mut v_x_5201_: usize,
    mut v_x_5202_: *mut crate::leanh::LeanObject,
    mut v_x_5203_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_es_5204_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5205_: usize = 0;
    let mut v___x_5206_: usize = 0;
    let mut v___x_5207_: usize = 0;
    let mut v___x_5208_: usize = 0;
    let mut v_j_5209_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5210_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5211_: u8 = 0;
    let mut v___x_5213_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5214_: u8 = 0;
    let mut v_v_5215_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5216_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_xs_x27_5217_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5219_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5220_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5222_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5223_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_key_5224_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_5225_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5227_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5228_: u8 = 0;
    let mut v___x_5229_: u8 = 0;
    let mut v___x_5230_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5231_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5233_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5234_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5235_: u8 = 0;
    let mut v_node_5236_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5238_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5239_: u8 = 0;
    let mut v___x_5240_: usize = 0;
    let mut v___x_5241_: usize = 0;
    let mut v___x_5242_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5244_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5245_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5246_: u8 = 0;
    let mut v___x_5247_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5248_: u8 = 0;
    let mut v_unused_5249_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ks_5250_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_vs_5251_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5253_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5254_: u8 = 0;
    let mut v___x_5256_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_newNode_5257_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5259_: u8 = 0;
    let mut v_ks_5260_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_vs_5261_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5262_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5263_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5264_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5265_: usize = 0;
    let mut v___x_5266_: u8 = 0;
    let mut v___x_5267_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5268_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5269_: u8 = 0;
    let mut v_reuseFailAlloc_5270_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5271_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_5199_) == 0 {
                    v_es_5204_ = crate::leanh::lean_ctor_get(v_x_5199_, 0);
                    v___x_5205_ = 5usize;
                    v___x_5206_ = 1usize;
                    v___x_5207_ = crate::leanh::lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__2_spec__3_spec__11___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__2_spec__3_spec__11___redArg___closed__1_once), _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__2_spec__3_spec__11___redArg___closed__1);
                    v___x_5208_ = lean_usize_land(v_x_5200_, v___x_5207_);
                    v_j_5209_ = lean_usize_to_nat(v___x_5208_);
                    v___x_5210_ = lean_array_get_size(v_es_5204_);
                    v___x_5211_ = lean_nat_dec_lt(v_j_5209_, v___x_5210_);
                    if v___x_5211_ == 0 {
                        crate::leanh::lean_dec(v_j_5209_);
                        crate::leanh::lean_dec(v_x_5203_);
                        crate::leanh::lean_dec(v_x_5202_);
                        return v_x_5199_;
                    } else {
                        crate::leanh::lean_inc_ref(v_es_5204_);
                        v_isSharedCheck_5248_ = (!crate::leanh::lean_is_exclusive(v_x_5199_)) as u8;
                        if v_isSharedCheck_5248_ == 0 {
                            v_unused_5249_ = crate::leanh::lean_ctor_get(v_x_5199_, 0);
                            crate::leanh::lean_dec(v_unused_5249_);
                            v___x_5213_ = v_x_5199_;
                            v_isShared_5214_ = v_isSharedCheck_5248_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_dec(v_x_5199_);
                            v___x_5213_ = crate::leanh::lean_box(0);
                            v_isShared_5214_ = v_isSharedCheck_5248_;
                            state = 1;
                            continue;
                        }
                    }
                } else {
                    v_ks_5250_ = crate::leanh::lean_ctor_get(v_x_5199_, 0);
                    v_vs_5251_ = crate::leanh::lean_ctor_get(v_x_5199_, 1);
                    v_isSharedCheck_5271_ = (!crate::leanh::lean_is_exclusive(v_x_5199_)) as u8;
                    if v_isSharedCheck_5271_ == 0 {
                        v___x_5253_ = v_x_5199_;
                        v_isShared_5254_ = v_isSharedCheck_5271_;
                        state = 8;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_vs_5251_);
                        crate::leanh::lean_inc(v_ks_5250_);
                        crate::leanh::lean_dec(v_x_5199_);
                        v___x_5253_ = crate::leanh::lean_box(0);
                        v_isShared_5254_ = v_isSharedCheck_5271_;
                        state = 8;
                        continue;
                    }
                }
            }
            1 => {
                v_v_5215_ = lean_array_fget(v_es_5204_, v_j_5209_);
                v___x_5216_ = crate::leanh::lean_box(0);
                v_xs_x27_5217_ = lean_array_fset(v_es_5204_, v_j_5209_, v___x_5216_);
                match crate::leanh::lean_obj_tag(v_v_5215_) {
                    0 => {
                        v_key_5224_ = crate::leanh::lean_ctor_get(v_v_5215_, 0);
                        v_val_5225_ = crate::leanh::lean_ctor_get(v_v_5215_, 1);
                        v_isSharedCheck_5235_ = (!crate::leanh::lean_is_exclusive(v_v_5215_)) as u8;
                        if v_isSharedCheck_5235_ == 0 {
                            v___x_5227_ = v_v_5215_;
                            v_isShared_5228_ = v_isSharedCheck_5235_;
                            state = 4;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_val_5225_);
                            crate::leanh::lean_inc(v_key_5224_);
                            crate::leanh::lean_dec(v_v_5215_);
                            v___x_5227_ = crate::leanh::lean_box(0);
                            v_isShared_5228_ = v_isSharedCheck_5235_;
                            state = 4;
                            continue;
                        }
                    }
                    1 => {
                        v_node_5236_ = crate::leanh::lean_ctor_get(v_v_5215_, 0);
                        v_isSharedCheck_5246_ = (!crate::leanh::lean_is_exclusive(v_v_5215_)) as u8;
                        if v_isSharedCheck_5246_ == 0 {
                            v___x_5238_ = v_v_5215_;
                            v_isShared_5239_ = v_isSharedCheck_5246_;
                            state = 6;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_node_5236_);
                            crate::leanh::lean_dec(v_v_5215_);
                            v___x_5238_ = crate::leanh::lean_box(0);
                            v_isShared_5239_ = v_isSharedCheck_5246_;
                            state = 6;
                            continue;
                        }
                    }
                    _ => {
                        v___x_5247_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_5247_, 0, v_x_5202_);
                        crate::leanh::lean_ctor_set(v___x_5247_, 1, v_x_5203_);
                        v___y_5219_ = v___x_5247_;
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                v___x_5220_ = lean_array_fset(v_xs_x27_5217_, v_j_5209_, v___y_5219_);
                crate::leanh::lean_dec(v_j_5209_);
                if v_isShared_5214_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5213_, 0, v___x_5220_);
                    v___x_5222_ = v___x_5213_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_5223_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5223_, 0, v___x_5220_);
                    v___x_5222_ = v_reuseFailAlloc_5223_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_5222_;
            }
            4 => {
                v___x_5229_ = l_Lean_instBEqMVarId_beq(v_x_5202_, v_key_5224_);
                if v___x_5229_ == 0 {
                    crate::leanh::lean_del_object(v___x_5227_);
                    v___x_5230_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(
                        v_key_5224_,
                        v_val_5225_,
                        v_x_5202_,
                        v_x_5203_,
                    );
                    v___x_5231_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_5231_, 0, v___x_5230_);
                    v___y_5219_ = v___x_5231_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_dec(v_val_5225_);
                    crate::leanh::lean_dec(v_key_5224_);
                    if v_isShared_5228_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_5227_, 1, v_x_5203_);
                        crate::leanh::lean_ctor_set(v___x_5227_, 0, v_x_5202_);
                        v___x_5233_ = v___x_5227_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_5234_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_5234_, 0, v_x_5202_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_5234_, 1, v_x_5203_);
                        v___x_5233_ = v_reuseFailAlloc_5234_;
                        state = 5;
                        continue;
                    }
                }
            }
            5 => {
                v___y_5219_ = v___x_5233_;
                state = 2;
                continue;
            }
            6 => {
                v___x_5240_ = lean_usize_shift_right(v_x_5200_, v___x_5205_);
                v___x_5241_ = lean_usize_add(v_x_5201_, v___x_5206_);
                v___x_5242_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__2_spec__3_spec__11___redArg(v_node_5236_, v___x_5240_, v___x_5241_, v_x_5202_, v_x_5203_);
                if v_isShared_5239_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5238_, 0, v___x_5242_);
                    v___x_5244_ = v___x_5238_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_5245_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5245_, 0, v___x_5242_);
                    v___x_5244_ = v_reuseFailAlloc_5245_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                v___y_5219_ = v___x_5244_;
                state = 2;
                continue;
            }
            8 => {
                if v_isShared_5254_ == 0 {
                    v___x_5256_ = v___x_5253_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_5270_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5270_, 0, v_ks_5250_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5270_, 1, v_vs_5251_);
                    v___x_5256_ = v_reuseFailAlloc_5270_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                v_newNode_5257_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__2_spec__3_spec__11_spec__22___redArg(v___x_5256_, v_x_5202_, v_x_5203_);
                v___x_5265_ = 7usize;
                v___x_5266_ = lean_usize_dec_le(v___x_5265_, v_x_5201_);
                if v___x_5266_ == 0 {
                    v___x_5267_ =
                        l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_5257_);
                    v___x_5268_ = crate::leanh::lean_unsigned_to_nat(4);
                    v___x_5269_ = lean_nat_dec_lt(v___x_5267_, v___x_5268_);
                    crate::leanh::lean_dec(v___x_5267_);
                    v___y_5259_ = v___x_5269_;
                    state = 10;
                    continue;
                } else {
                    v___y_5259_ = v___x_5266_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                if v___y_5259_ == 0 {
                    v_ks_5260_ = crate::leanh::lean_ctor_get(v_newNode_5257_, 0);
                    crate::leanh::lean_inc_ref(v_ks_5260_);
                    v_vs_5261_ = crate::leanh::lean_ctor_get(v_newNode_5257_, 1);
                    crate::leanh::lean_inc_ref(v_vs_5261_);
                    crate::leanh::lean_dec_ref(v_newNode_5257_);
                    v___x_5262_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___x_5263_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__2_spec__3_spec__11___redArg___closed__2), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__2_spec__3_spec__11___redArg___closed__2_once), _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__2_spec__3_spec__11___redArg___closed__2);
                    v___x_5264_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__2_spec__3_spec__11_spec__23___redArg(v_x_5201_, v_ks_5260_, v_vs_5261_, v___x_5262_, v___x_5263_);
                    crate::leanh::lean_dec_ref(v_vs_5261_);
                    crate::leanh::lean_dec_ref(v_ks_5260_);
                    return v___x_5264_;
                } else {
                    return v_newNode_5257_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__2_spec__3_spec__11_spec__23___redArg(
    mut v_depth_5272_: usize,
    mut v_keys_5273_: *mut crate::leanh::LeanObject,
    mut v_vals_5274_: *mut crate::leanh::LeanObject,
    mut v_i_5275_: *mut crate::leanh::LeanObject,
    mut v_entries_5276_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5277_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5278_: u8 = 0;
    let mut v_k_5279_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_5280_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5281_: u64 = 0;
    let mut v_h_5282_: usize = 0;
    let mut v___x_5283_: usize = 0;
    let mut v___x_5284_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5285_: usize = 0;
    let mut v___x_5286_: usize = 0;
    let mut v___x_5287_: usize = 0;
    let mut v_h_5288_: usize = 0;
    let mut v___x_5289_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5290_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5277_ = lean_array_get_size(v_keys_5273_);
                v___x_5278_ = lean_nat_dec_lt(v_i_5275_, v___x_5277_);
                if v___x_5278_ == 0 {
                    crate::leanh::lean_dec(v_i_5275_);
                    return v_entries_5276_;
                } else {
                    v_k_5279_ = lean_array_fget_borrowed(v_keys_5273_, v_i_5275_);
                    v_v_5280_ = lean_array_fget_borrowed(v_vals_5274_, v_i_5275_);
                    v___x_5281_ = l_Lean_instHashableMVarId_hash(v_k_5279_);
                    v_h_5282_ = lean_uint64_to_usize(v___x_5281_);
                    v___x_5283_ = 5usize;
                    v___x_5284_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_5285_ = 1usize;
                    v___x_5286_ = lean_usize_sub(v_depth_5272_, v___x_5285_);
                    v___x_5287_ = lean_usize_mul(v___x_5283_, v___x_5286_);
                    v_h_5288_ = lean_usize_shift_right(v_h_5282_, v___x_5287_);
                    v___x_5289_ = lean_nat_add(v_i_5275_, v___x_5284_);
                    crate::leanh::lean_dec(v_i_5275_);
                    crate::leanh::lean_inc(v_v_5280_);
                    crate::leanh::lean_inc(v_k_5279_);
                    v___x_5290_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__2_spec__3_spec__11___redArg(v_entries_5276_, v_h_5288_, v_depth_5272_, v_k_5279_, v_v_5280_);
                    v_i_5275_ = v___x_5289_;
                    v_entries_5276_ = v___x_5290_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__2_spec__3_spec__11_spec__23___redArg___boxed(
    mut v_depth_5292_: *mut crate::leanh::LeanObject,
    mut v_keys_5293_: *mut crate::leanh::LeanObject,
    mut v_vals_5294_: *mut crate::leanh::LeanObject,
    mut v_i_5295_: *mut crate::leanh::LeanObject,
    mut v_entries_5296_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_depth_boxed_5297_: usize = 0;
    let mut v_res_5298_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_depth_boxed_5297_ = crate::leanh::lean_unbox_usize(v_depth_5292_);
    crate::leanh::lean_dec(v_depth_5292_);
    v_res_5298_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__2_spec__3_spec__11_spec__23___redArg(v_depth_boxed_5297_, v_keys_5293_, v_vals_5294_, v_i_5295_, v_entries_5296_);
    crate::leanh::lean_dec_ref(v_vals_5294_);
    crate::leanh::lean_dec_ref(v_keys_5293_);
    return v_res_5298_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__2_spec__3_spec__11___redArg___boxed(
    mut v_x_5299_: *mut crate::leanh::LeanObject,
    mut v_x_5300_: *mut crate::leanh::LeanObject,
    mut v_x_5301_: *mut crate::leanh::LeanObject,
    mut v_x_5302_: *mut crate::leanh::LeanObject,
    mut v_x_5303_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_94802__boxed_5304_: usize = 0;
    let mut v_x_94803__boxed_5305_: usize = 0;
    let mut v_res_5306_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_94802__boxed_5304_ = crate::leanh::lean_unbox_usize(v_x_5300_);
    crate::leanh::lean_dec(v_x_5300_);
    v_x_94803__boxed_5305_ = crate::leanh::lean_unbox_usize(v_x_5301_);
    crate::leanh::lean_dec(v_x_5301_);
    v_res_5306_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__2_spec__3_spec__11___redArg(v_x_5299_, v_x_94802__boxed_5304_, v_x_94803__boxed_5305_, v_x_5302_, v_x_5303_);
    return v_res_5306_;
}
pub unsafe fn l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__2_spec__3___redArg(
    mut v_x_5307_: *mut crate::leanh::LeanObject,
    mut v_x_5308_: *mut crate::leanh::LeanObject,
    mut v_x_5309_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5310_: u64 = 0;
    let mut v___x_5311_: usize = 0;
    let mut v___x_5312_: usize = 0;
    let mut v___x_5313_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5310_ = l_Lean_instHashableMVarId_hash(v_x_5308_);
    v___x_5311_ = lean_uint64_to_usize(v___x_5310_);
    v___x_5312_ = 1usize;
    v___x_5313_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__2_spec__3_spec__11___redArg(v_x_5307_, v___x_5311_, v___x_5312_, v_x_5308_, v_x_5309_);
    return v___x_5313_;
}
pub unsafe fn l_Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__2___redArg(
    mut v_mvarId_5314_: *mut crate::leanh::LeanObject,
    mut v_val_5315_: *mut crate::leanh::LeanObject,
    mut v___y_5316_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5318_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_5319_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_cache_5320_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_zetaDeltaFVarIds_5321_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_postponed_5322_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_diag_5323_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5325_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5326_: u8 = 0;
    let mut v_depth_5327_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_levelAssignDepth_5328_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_lmvarCounter_5329_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mvarCounter_5330_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_lDecls_5331_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_decls_5332_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_userNames_5333_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_lAssignment_5334_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_eAssignment_5335_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_dAssignment_5336_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5338_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5339_: u8 = 0;
    let mut v___x_5340_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5342_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5344_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5345_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5346_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5347_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5348_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5349_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5350_: u8 = 0;
    let mut v_isSharedCheck_5351_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5318_ = lean_st_ref_take(v___y_5316_);
                v_mctx_5319_ = crate::leanh::lean_ctor_get(v___x_5318_, 0);
                v_cache_5320_ = crate::leanh::lean_ctor_get(v___x_5318_, 1);
                v_zetaDeltaFVarIds_5321_ = crate::leanh::lean_ctor_get(v___x_5318_, 2);
                v_postponed_5322_ = crate::leanh::lean_ctor_get(v___x_5318_, 3);
                v_diag_5323_ = crate::leanh::lean_ctor_get(v___x_5318_, 4);
                v_isSharedCheck_5351_ = (!crate::leanh::lean_is_exclusive(v___x_5318_)) as u8;
                if v_isSharedCheck_5351_ == 0 {
                    v___x_5325_ = v___x_5318_;
                    v_isShared_5326_ = v_isSharedCheck_5351_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_diag_5323_);
                    crate::leanh::lean_inc(v_postponed_5322_);
                    crate::leanh::lean_inc(v_zetaDeltaFVarIds_5321_);
                    crate::leanh::lean_inc(v_cache_5320_);
                    crate::leanh::lean_inc(v_mctx_5319_);
                    crate::leanh::lean_dec(v___x_5318_);
                    v___x_5325_ = crate::leanh::lean_box(0);
                    v_isShared_5326_ = v_isSharedCheck_5351_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_depth_5327_ = crate::leanh::lean_ctor_get(v_mctx_5319_, 0);
                v_levelAssignDepth_5328_ = crate::leanh::lean_ctor_get(v_mctx_5319_, 1);
                v_lmvarCounter_5329_ = crate::leanh::lean_ctor_get(v_mctx_5319_, 2);
                v_mvarCounter_5330_ = crate::leanh::lean_ctor_get(v_mctx_5319_, 3);
                v_lDecls_5331_ = crate::leanh::lean_ctor_get(v_mctx_5319_, 4);
                v_decls_5332_ = crate::leanh::lean_ctor_get(v_mctx_5319_, 5);
                v_userNames_5333_ = crate::leanh::lean_ctor_get(v_mctx_5319_, 6);
                v_lAssignment_5334_ = crate::leanh::lean_ctor_get(v_mctx_5319_, 7);
                v_eAssignment_5335_ = crate::leanh::lean_ctor_get(v_mctx_5319_, 8);
                v_dAssignment_5336_ = crate::leanh::lean_ctor_get(v_mctx_5319_, 9);
                v_isSharedCheck_5350_ = (!crate::leanh::lean_is_exclusive(v_mctx_5319_)) as u8;
                if v_isSharedCheck_5350_ == 0 {
                    v___x_5338_ = v_mctx_5319_;
                    v_isShared_5339_ = v_isSharedCheck_5350_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_dAssignment_5336_);
                    crate::leanh::lean_inc(v_eAssignment_5335_);
                    crate::leanh::lean_inc(v_lAssignment_5334_);
                    crate::leanh::lean_inc(v_userNames_5333_);
                    crate::leanh::lean_inc(v_decls_5332_);
                    crate::leanh::lean_inc(v_lDecls_5331_);
                    crate::leanh::lean_inc(v_mvarCounter_5330_);
                    crate::leanh::lean_inc(v_lmvarCounter_5329_);
                    crate::leanh::lean_inc(v_levelAssignDepth_5328_);
                    crate::leanh::lean_inc(v_depth_5327_);
                    crate::leanh::lean_dec(v_mctx_5319_);
                    v___x_5338_ = crate::leanh::lean_box(0);
                    v_isShared_5339_ = v_isSharedCheck_5350_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_5340_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__2_spec__3___redArg(v_eAssignment_5335_, v_mvarId_5314_, v_val_5315_);
                if v_isShared_5339_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5338_, 8, v___x_5340_);
                    v___x_5342_ = v___x_5338_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_5349_ = crate::leanh::lean_alloc_ctor(0, 10, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5349_, 0, v_depth_5327_);
                    crate::leanh::lean_ctor_set(
                        v_reuseFailAlloc_5349_,
                        1,
                        v_levelAssignDepth_5328_,
                    );
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5349_, 2, v_lmvarCounter_5329_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5349_, 3, v_mvarCounter_5330_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5349_, 4, v_lDecls_5331_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5349_, 5, v_decls_5332_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5349_, 6, v_userNames_5333_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5349_, 7, v_lAssignment_5334_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5349_, 8, v___x_5340_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5349_, 9, v_dAssignment_5336_);
                    v___x_5342_ = v_reuseFailAlloc_5349_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_5326_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5325_, 0, v___x_5342_);
                    v___x_5344_ = v___x_5325_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_5348_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5348_, 0, v___x_5342_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5348_, 1, v_cache_5320_);
                    crate::leanh::lean_ctor_set(
                        v_reuseFailAlloc_5348_,
                        2,
                        v_zetaDeltaFVarIds_5321_,
                    );
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5348_, 3, v_postponed_5322_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5348_, 4, v_diag_5323_);
                    v___x_5344_ = v_reuseFailAlloc_5348_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_5345_ = lean_st_ref_set(v___y_5316_, v___x_5344_);
                v___x_5346_ = crate::leanh::lean_box(0);
                v___x_5347_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_5347_, 0, v___x_5346_);
                return v___x_5347_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__2___redArg___boxed(
    mut v_mvarId_5352_: *mut crate::leanh::LeanObject,
    mut v_val_5353_: *mut crate::leanh::LeanObject,
    mut v___y_5354_: *mut crate::leanh::LeanObject,
    mut v___y_5355_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5356_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5356_ = l_Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__2___redArg(v_mvarId_5352_, v_val_5353_, v___y_5354_);
    crate::leanh::lean_dec(v___y_5354_);
    return v_res_5356_;
}
pub unsafe fn l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4_spec__7_spec__16___redArg___lam__0(
    mut v___y_5365_: u8,
    mut v_suppressElabErrors_5366_: u8,
    mut v_x_5367_: *mut crate::leanh::LeanObject,
) -> u8 {
    if crate::leanh::lean_obj_tag(v_x_5367_) == 1 {
        let mut v_pre_5368_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_pre_5368_ = crate::leanh::lean_ctor_get(v_x_5367_, 0);
        match crate::leanh::lean_obj_tag(v_pre_5368_) {
            1 => {
                let mut v_pre_5369_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                v_pre_5369_ = crate::leanh::lean_ctor_get(v_pre_5368_, 0);
                match crate::leanh::lean_obj_tag(v_pre_5369_) {
                    0 => {
                        let mut v_str_5370_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                        let mut v_str_5371_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                        let mut v___x_5372_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                        let mut v___x_5373_: u8 = 0;
                        v_str_5370_ = crate::leanh::lean_ctor_get(v_x_5367_, 1);
                        v_str_5371_ = crate::leanh::lean_ctor_get(v_pre_5368_, 1);
                        v___x_5372_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4_spec__7_spec__16___redArg___lam__0___closed__0;
                        v___x_5373_ = lean_string_dec_eq(v_str_5371_, v___x_5372_);
                        if v___x_5373_ == 0 {
                            let mut v___x_5374_: *mut crate::leanh::LeanObject =
                                core::ptr::null_mut();
                            let mut v___x_5375_: u8 = 0;
                            v___x_5374_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4_spec__7_spec__16___redArg___lam__0___closed__1;
                            v___x_5375_ = lean_string_dec_eq(v_str_5371_, v___x_5374_);
                            if v___x_5375_ == 0 {
                                return v___y_5365_;
                            } else {
                                let mut v___x_5376_: *mut crate::leanh::LeanObject =
                                    core::ptr::null_mut();
                                let mut v___x_5377_: u8 = 0;
                                v___x_5376_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4_spec__7_spec__16___redArg___lam__0___closed__2;
                                v___x_5377_ = lean_string_dec_eq(v_str_5370_, v___x_5376_);
                                if v___x_5377_ == 0 {
                                    return v___y_5365_;
                                } else {
                                    return v_suppressElabErrors_5366_;
                                }
                            }
                        } else {
                            let mut v___x_5378_: *mut crate::leanh::LeanObject =
                                core::ptr::null_mut();
                            let mut v___x_5379_: u8 = 0;
                            v___x_5378_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4_spec__7_spec__16___redArg___lam__0___closed__3;
                            v___x_5379_ = lean_string_dec_eq(v_str_5370_, v___x_5378_);
                            if v___x_5379_ == 0 {
                                return v___y_5365_;
                            } else {
                                return v_suppressElabErrors_5366_;
                            }
                        }
                    }
                    1 => {
                        let mut v_pre_5380_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                        v_pre_5380_ = crate::leanh::lean_ctor_get(v_pre_5369_, 0);
                        if crate::leanh::lean_obj_tag(v_pre_5380_) == 0 {
                            let mut v_str_5381_: *mut crate::leanh::LeanObject =
                                core::ptr::null_mut();
                            let mut v_str_5382_: *mut crate::leanh::LeanObject =
                                core::ptr::null_mut();
                            let mut v_str_5383_: *mut crate::leanh::LeanObject =
                                core::ptr::null_mut();
                            let mut v___x_5384_: *mut crate::leanh::LeanObject =
                                core::ptr::null_mut();
                            let mut v___x_5385_: u8 = 0;
                            v_str_5381_ = crate::leanh::lean_ctor_get(v_x_5367_, 1);
                            v_str_5382_ = crate::leanh::lean_ctor_get(v_pre_5368_, 1);
                            v_str_5383_ = crate::leanh::lean_ctor_get(v_pre_5369_, 1);
                            v___x_5384_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4_spec__7_spec__16___redArg___lam__0___closed__4;
                            v___x_5385_ = lean_string_dec_eq(v_str_5383_, v___x_5384_);
                            if v___x_5385_ == 0 {
                                return v___y_5365_;
                            } else {
                                let mut v___x_5386_: *mut crate::leanh::LeanObject =
                                    core::ptr::null_mut();
                                let mut v___x_5387_: u8 = 0;
                                v___x_5386_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4_spec__7_spec__16___redArg___lam__0___closed__5;
                                v___x_5387_ = lean_string_dec_eq(v_str_5382_, v___x_5386_);
                                if v___x_5387_ == 0 {
                                    return v___y_5365_;
                                } else {
                                    let mut v___x_5388_: *mut crate::leanh::LeanObject =
                                        core::ptr::null_mut();
                                    let mut v___x_5389_: u8 = 0;
                                    v___x_5388_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4_spec__7_spec__16___redArg___lam__0___closed__6;
                                    v___x_5389_ = lean_string_dec_eq(v_str_5381_, v___x_5388_);
                                    if v___x_5389_ == 0 {
                                        return v___y_5365_;
                                    } else {
                                        return v_suppressElabErrors_5366_;
                                    }
                                }
                            }
                        } else {
                            return v___y_5365_;
                        }
                    }
                    _ => {
                        return v___y_5365_;
                    }
                }
            }
            0 => {
                let mut v_str_5390_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_5391_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_5392_: u8 = 0;
                v_str_5390_ = crate::leanh::lean_ctor_get(v_x_5367_, 1);
                v___x_5391_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4_spec__7_spec__16___redArg___lam__0___closed__7;
                v___x_5392_ = lean_string_dec_eq(v_str_5390_, v___x_5391_);
                if v___x_5392_ == 0 {
                    return v___y_5365_;
                } else {
                    return v_suppressElabErrors_5366_;
                }
            }
            _ => {
                return v___y_5365_;
            }
        }
    } else {
        return v___y_5365_;
    }
}
pub unsafe fn l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4_spec__7_spec__16___redArg___lam__0___boxed(
    mut v___y_5393_: *mut crate::leanh::LeanObject,
    mut v_suppressElabErrors_5394_: *mut crate::leanh::LeanObject,
    mut v_x_5395_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_95037__boxed_5396_: u8 = 0;
    let mut v_suppressElabErrors_boxed_5397_: u8 = 0;
    let mut v_res_5398_: u8 = 0;
    let mut v_r_5399_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___y_95037__boxed_5396_ = (crate::leanh::lean_unbox(v___y_5393_) as u8);
    v_suppressElabErrors_boxed_5397_ = (crate::leanh::lean_unbox(v_suppressElabErrors_5394_) as u8);
    v_res_5398_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4_spec__7_spec__16___redArg___lam__0(v___y_95037__boxed_5396_, v_suppressElabErrors_boxed_5397_, v_x_5395_);
    crate::leanh::lean_dec(v_x_5395_);
    v_r_5399_ = crate::leanh::lean_box((v_res_5398_) as usize);
    return v_r_5399_;
}
pub unsafe fn l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4_spec__7_spec__16___redArg(
    mut v_ref_5401_: *mut crate::leanh::LeanObject,
    mut v_msgData_5402_: *mut crate::leanh::LeanObject,
    mut v_severity_5403_: u8,
    mut v_isSilent_5404_: u8,
    mut v___y_5405_: *mut crate::leanh::LeanObject,
    mut v___y_5406_: *mut crate::leanh::LeanObject,
    mut v___y_5407_: *mut crate::leanh::LeanObject,
    mut v___y_5408_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_5411_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5412_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5413_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5414_: u8 = 0;
    let mut v___y_5415_: u8 = 0;
    let mut v___y_5416_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5417_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5418_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5419_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5420_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_currNamespace_5421_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_openDecls_5422_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_5423_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_5424_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ngen_5425_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_5426_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_traceState_5427_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_cache_5428_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_messages_5429_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_infoState_5430_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_5431_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5433_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5434_: u8 = 0;
    let mut v___x_5435_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5436_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5437_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5438_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5440_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5441_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5442_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5443_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5444_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5445_: u8 = 0;
    let mut v___y_5447_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5448_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5449_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5450_: u8 = 0;
    let mut v___y_5451_: u8 = 0;
    let mut v___y_5452_: u8 = 0;
    let mut v___y_5453_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5454_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5455_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5456_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5457_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5459_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5460_: u8 = 0;
    let mut v___x_5461_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5462_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5463_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5464_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5465_: u8 = 0;
    let mut v___x_5466_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5468_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5469_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5470_: u8 = 0;
    let mut v___y_5472_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5473_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5474_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5475_: u8 = 0;
    let mut v___y_5476_: u8 = 0;
    let mut v___y_5477_: u8 = 0;
    let mut v___y_5478_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5479_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5480_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_5481_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5483_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5484_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5485_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5486_: u8 = 0;
    let mut v___y_5487_: u8 = 0;
    let mut v___y_5488_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5489_: u8 = 0;
    let mut v_ref_5490_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5491_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5492_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_5493_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5494_: u8 = 0;
    let mut v___y_5496_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5497_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5498_: u8 = 0;
    let mut v___y_5499_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5500_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5501_: u8 = 0;
    let mut v___y_5502_: u8 = 0;
    let mut v___y_5504_: u8 = 0;
    let mut v_fileName_5505_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fileMap_5506_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_5507_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_5508_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_suppressElabErrors_5509_: u8 = 0;
    let mut v___x_5510_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5511_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5512_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5513_: u8 = 0;
    let mut v___x_5514_: u8 = 0;
    let mut v___x_5515_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5516_: u8 = 0;
    let mut v___x_5517_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5518_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5519_: u8 = 0;
    let mut v___x_5520_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5494_ = 2;
                v___x_5519_ = l_Lean_instBEqMessageSeverity_beq(v_severity_5403_, v___x_5494_);
                if v___x_5519_ == 0 {
                    v___y_5504_ = v___x_5519_;
                    state = 10;
                    continue;
                } else {
                    crate::leanh::lean_inc_ref(v_msgData_5402_);
                    v___x_5520_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_5402_);
                    v___y_5504_ = v___x_5520_;
                    state = 10;
                    continue;
                }
            }
            1 => {
                v___x_5420_ = lean_st_ref_take(v___y_5419_);
                v_currNamespace_5421_ = crate::leanh::lean_ctor_get(v___y_5418_, 6);
                v_openDecls_5422_ = crate::leanh::lean_ctor_get(v___y_5418_, 7);
                v_env_5423_ = crate::leanh::lean_ctor_get(v___x_5420_, 0);
                v_nextMacroScope_5424_ = crate::leanh::lean_ctor_get(v___x_5420_, 1);
                v_ngen_5425_ = crate::leanh::lean_ctor_get(v___x_5420_, 2);
                v_auxDeclNGen_5426_ = crate::leanh::lean_ctor_get(v___x_5420_, 3);
                v_traceState_5427_ = crate::leanh::lean_ctor_get(v___x_5420_, 4);
                v_cache_5428_ = crate::leanh::lean_ctor_get(v___x_5420_, 5);
                v_messages_5429_ = crate::leanh::lean_ctor_get(v___x_5420_, 6);
                v_infoState_5430_ = crate::leanh::lean_ctor_get(v___x_5420_, 7);
                v_snapshotTasks_5431_ = crate::leanh::lean_ctor_get(v___x_5420_, 8);
                v_isSharedCheck_5445_ = (!crate::leanh::lean_is_exclusive(v___x_5420_)) as u8;
                if v_isSharedCheck_5445_ == 0 {
                    v___x_5433_ = v___x_5420_;
                    v_isShared_5434_ = v_isSharedCheck_5445_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snapshotTasks_5431_);
                    crate::leanh::lean_inc(v_infoState_5430_);
                    crate::leanh::lean_inc(v_messages_5429_);
                    crate::leanh::lean_inc(v_cache_5428_);
                    crate::leanh::lean_inc(v_traceState_5427_);
                    crate::leanh::lean_inc(v_auxDeclNGen_5426_);
                    crate::leanh::lean_inc(v_ngen_5425_);
                    crate::leanh::lean_inc(v_nextMacroScope_5424_);
                    crate::leanh::lean_inc(v_env_5423_);
                    crate::leanh::lean_dec(v___x_5420_);
                    v___x_5433_ = crate::leanh::lean_box(0);
                    v_isShared_5434_ = v_isSharedCheck_5445_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                crate::leanh::lean_inc(v_openDecls_5422_);
                crate::leanh::lean_inc(v_currNamespace_5421_);
                v___x_5435_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_5435_, 0, v_currNamespace_5421_);
                crate::leanh::lean_ctor_set(v___x_5435_, 1, v_openDecls_5422_);
                v___x_5436_ = crate::leanh::lean_alloc_ctor(4, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_5436_, 0, v___x_5435_);
                crate::leanh::lean_ctor_set(v___x_5436_, 1, v___y_5417_);
                crate::leanh::lean_inc_ref(v___y_5412_);
                crate::leanh::lean_inc_ref(v___y_5413_);
                v___x_5437_ = crate::leanh::lean_alloc_ctor(0, 5, (3) as u32);
                crate::leanh::lean_ctor_set(v___x_5437_, 0, v___y_5413_);
                crate::leanh::lean_ctor_set(v___x_5437_, 1, v___y_5411_);
                crate::leanh::lean_ctor_set(v___x_5437_, 2, v___y_5416_);
                crate::leanh::lean_ctor_set(v___x_5437_, 3, v___y_5412_);
                crate::leanh::lean_ctor_set(v___x_5437_, 4, v___x_5436_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_5437_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 5) as u32,
                    v___y_5415_,
                );
                crate::leanh::lean_ctor_set_uint8(
                    v___x_5437_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 5 + 1) as u32,
                    v___y_5414_,
                );
                crate::leanh::lean_ctor_set_uint8(
                    v___x_5437_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 5 + 2) as u32,
                    v_isSilent_5404_,
                );
                v___x_5438_ = l_Lean_MessageLog_add(v___x_5437_, v_messages_5429_);
                if v_isShared_5434_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5433_, 6, v___x_5438_);
                    v___x_5440_ = v___x_5433_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_5444_ = crate::leanh::lean_alloc_ctor(0, 9, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5444_, 0, v_env_5423_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5444_, 1, v_nextMacroScope_5424_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5444_, 2, v_ngen_5425_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5444_, 3, v_auxDeclNGen_5426_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5444_, 4, v_traceState_5427_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5444_, 5, v_cache_5428_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5444_, 6, v___x_5438_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5444_, 7, v_infoState_5430_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5444_, 8, v_snapshotTasks_5431_);
                    v___x_5440_ = v_reuseFailAlloc_5444_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_5441_ = lean_st_ref_set(v___y_5419_, v___x_5440_);
                v___x_5442_ = crate::leanh::lean_box(0);
                v___x_5443_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_5443_, 0, v___x_5442_);
                return v___x_5443_;
            }
            4 => {
                v___x_5455_ =
                    l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(
                        v_msgData_5402_,
                    );
                v___x_5456_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__6_spec__10(v___x_5455_, v___y_5405_, v___y_5406_, v___y_5407_, v___y_5408_);
                v_a_5457_ = crate::leanh::lean_ctor_get(v___x_5456_, 0);
                v_isSharedCheck_5470_ = (!crate::leanh::lean_is_exclusive(v___x_5456_)) as u8;
                if v_isSharedCheck_5470_ == 0 {
                    v___x_5459_ = v___x_5456_;
                    v_isShared_5460_ = v_isSharedCheck_5470_;
                    state = 5;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_a_5457_);
                    crate::leanh::lean_dec(v___x_5456_);
                    v___x_5459_ = crate::leanh::lean_box(0);
                    v_isShared_5460_ = v_isSharedCheck_5470_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                crate::leanh::lean_inc_ref_n(v___y_5453_, 2);
                v___x_5461_ = l_Lean_FileMap_toPosition(v___y_5453_, v___y_5448_);
                crate::leanh::lean_dec(v___y_5448_);
                v___x_5462_ = l_Lean_FileMap_toPosition(v___y_5453_, v___y_5454_);
                crate::leanh::lean_dec(v___y_5454_);
                v___x_5463_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_5463_, 0, v___x_5462_);
                v___x_5464_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4_spec__7_spec__16___redArg___closed__0;
                if v___y_5450_ == 0 {
                    crate::leanh::lean_del_object(v___x_5459_);
                    crate::leanh::lean_dec_ref(v___y_5447_);
                    v___y_5411_ = v___x_5461_;
                    v___y_5412_ = v___x_5464_;
                    v___y_5413_ = v___y_5449_;
                    v___y_5414_ = v___y_5452_;
                    v___y_5415_ = v___y_5451_;
                    v___y_5416_ = v___x_5463_;
                    v___y_5417_ = v_a_5457_;
                    v___y_5418_ = v___y_5407_;
                    v___y_5419_ = v___y_5408_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_a_5457_);
                    v___x_5465_ = l_Lean_MessageData_hasTag(v___y_5447_, v_a_5457_);
                    if v___x_5465_ == 0 {
                        crate::leanh::lean_dec_ref_known(v___x_5463_, 1);
                        crate::leanh::lean_dec_ref(v___x_5461_);
                        crate::leanh::lean_dec(v_a_5457_);
                        v___x_5466_ = crate::leanh::lean_box(0);
                        if v_isShared_5460_ == 0 {
                            crate::leanh::lean_ctor_set(v___x_5459_, 0, v___x_5466_);
                            v___x_5468_ = v___x_5459_;
                            state = 6;
                            continue;
                        } else {
                            v_reuseFailAlloc_5469_ =
                                crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_5469_, 0, v___x_5466_);
                            v___x_5468_ = v_reuseFailAlloc_5469_;
                            state = 6;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_del_object(v___x_5459_);
                        v___y_5411_ = v___x_5461_;
                        v___y_5412_ = v___x_5464_;
                        v___y_5413_ = v___y_5449_;
                        v___y_5414_ = v___y_5452_;
                        v___y_5415_ = v___y_5451_;
                        v___y_5416_ = v___x_5463_;
                        v___y_5417_ = v_a_5457_;
                        v___y_5418_ = v___y_5407_;
                        v___y_5419_ = v___y_5408_;
                        state = 1;
                        continue;
                    }
                }
            }
            6 => {
                return v___x_5468_;
            }
            7 => {
                v___x_5480_ = l_Lean_Syntax_getTailPos_x3f(v___y_5474_, v___y_5476_);
                crate::leanh::lean_dec(v___y_5474_);
                if crate::leanh::lean_obj_tag(v___x_5480_) == 0 {
                    crate::leanh::lean_inc(v___y_5479_);
                    v___y_5447_ = v___y_5472_;
                    v___y_5448_ = v___y_5479_;
                    v___y_5449_ = v___y_5473_;
                    v___y_5450_ = v___y_5477_;
                    v___y_5451_ = v___y_5476_;
                    v___y_5452_ = v___y_5475_;
                    v___y_5453_ = v___y_5478_;
                    v___y_5454_ = v___y_5479_;
                    state = 4;
                    continue;
                } else {
                    v_val_5481_ = crate::leanh::lean_ctor_get(v___x_5480_, 0);
                    crate::leanh::lean_inc(v_val_5481_);
                    crate::leanh::lean_dec_ref_known(v___x_5480_, 1);
                    v___y_5447_ = v___y_5472_;
                    v___y_5448_ = v___y_5479_;
                    v___y_5449_ = v___y_5473_;
                    v___y_5450_ = v___y_5477_;
                    v___y_5451_ = v___y_5476_;
                    v___y_5452_ = v___y_5475_;
                    v___y_5453_ = v___y_5478_;
                    v___y_5454_ = v_val_5481_;
                    state = 4;
                    continue;
                }
            }
            8 => {
                v_ref_5490_ = l_Lean_replaceRef(v_ref_5401_, v___y_5484_);
                v___x_5491_ = l_Lean_Syntax_getPos_x3f(v_ref_5490_, v___y_5487_);
                if crate::leanh::lean_obj_tag(v___x_5491_) == 0 {
                    v___x_5492_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___y_5472_ = v___y_5483_;
                    v___y_5473_ = v___y_5485_;
                    v___y_5474_ = v_ref_5490_;
                    v___y_5475_ = v___y_5489_;
                    v___y_5476_ = v___y_5487_;
                    v___y_5477_ = v___y_5486_;
                    v___y_5478_ = v___y_5488_;
                    v___y_5479_ = v___x_5492_;
                    state = 7;
                    continue;
                } else {
                    v_val_5493_ = crate::leanh::lean_ctor_get(v___x_5491_, 0);
                    crate::leanh::lean_inc(v_val_5493_);
                    crate::leanh::lean_dec_ref_known(v___x_5491_, 1);
                    v___y_5472_ = v___y_5483_;
                    v___y_5473_ = v___y_5485_;
                    v___y_5474_ = v_ref_5490_;
                    v___y_5475_ = v___y_5489_;
                    v___y_5476_ = v___y_5487_;
                    v___y_5477_ = v___y_5486_;
                    v___y_5478_ = v___y_5488_;
                    v___y_5479_ = v_val_5493_;
                    state = 7;
                    continue;
                }
            }
            9 => {
                if v___y_5502_ == 0 {
                    v___y_5483_ = v___y_5500_;
                    v___y_5484_ = v___y_5496_;
                    v___y_5485_ = v___y_5497_;
                    v___y_5486_ = v___y_5498_;
                    v___y_5487_ = v___y_5501_;
                    v___y_5488_ = v___y_5499_;
                    v___y_5489_ = v_severity_5403_;
                    state = 8;
                    continue;
                } else {
                    v___y_5483_ = v___y_5500_;
                    v___y_5484_ = v___y_5496_;
                    v___y_5485_ = v___y_5497_;
                    v___y_5486_ = v___y_5498_;
                    v___y_5487_ = v___y_5501_;
                    v___y_5488_ = v___y_5499_;
                    v___y_5489_ = v___x_5494_;
                    state = 8;
                    continue;
                }
            }
            10 => {
                if v___y_5504_ == 0 {
                    v_fileName_5505_ = crate::leanh::lean_ctor_get(v___y_5407_, 0);
                    v_fileMap_5506_ = crate::leanh::lean_ctor_get(v___y_5407_, 1);
                    v_options_5507_ = crate::leanh::lean_ctor_get(v___y_5407_, 2);
                    v_ref_5508_ = crate::leanh::lean_ctor_get(v___y_5407_, 5);
                    v_suppressElabErrors_5509_ = crate::leanh::lean_ctor_get_uint8(
                        v___y_5407_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 14 + 1) as u32,
                    );
                    v___x_5510_ = crate::leanh::lean_box((v___y_5504_) as usize);
                    v___x_5511_ = crate::leanh::lean_box((v_suppressElabErrors_5509_) as usize);
                    v___f_5512_ = crate::leanh::lean_alloc_closure(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4_spec__7_spec__16___redArg___lam__0___boxed as *mut core::ffi::c_void, 3, 2);
                    crate::leanh::lean_closure_set(v___f_5512_, 0, v___x_5510_);
                    crate::leanh::lean_closure_set(v___f_5512_, 1, v___x_5511_);
                    v___x_5513_ = 1;
                    v___x_5514_ = l_Lean_instBEqMessageSeverity_beq(v_severity_5403_, v___x_5513_);
                    if v___x_5514_ == 0 {
                        v___y_5496_ = v_ref_5508_;
                        v___y_5497_ = v_fileName_5505_;
                        v___y_5498_ = v_suppressElabErrors_5509_;
                        v___y_5499_ = v_fileMap_5506_;
                        v___y_5500_ = v___f_5512_;
                        v___y_5501_ = v___y_5504_;
                        v___y_5502_ = v___x_5514_;
                        state = 9;
                        continue;
                    } else {
                        v___x_5515_ = l_Lean_warningAsError;
                        v___x_5516_ = l_Lean_Option_get___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__10(v_options_5507_, v___x_5515_);
                        v___y_5496_ = v_ref_5508_;
                        v___y_5497_ = v_fileName_5505_;
                        v___y_5498_ = v_suppressElabErrors_5509_;
                        v___y_5499_ = v_fileMap_5506_;
                        v___y_5500_ = v___f_5512_;
                        v___y_5501_ = v___y_5504_;
                        v___y_5502_ = v___x_5516_;
                        state = 9;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_msgData_5402_);
                    v___x_5517_ = crate::leanh::lean_box(0);
                    v___x_5518_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_5518_, 0, v___x_5517_);
                    return v___x_5518_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4_spec__7_spec__16___redArg___boxed(
    mut v_ref_5521_: *mut crate::leanh::LeanObject,
    mut v_msgData_5522_: *mut crate::leanh::LeanObject,
    mut v_severity_5523_: *mut crate::leanh::LeanObject,
    mut v_isSilent_5524_: *mut crate::leanh::LeanObject,
    mut v___y_5525_: *mut crate::leanh::LeanObject,
    mut v___y_5526_: *mut crate::leanh::LeanObject,
    mut v___y_5527_: *mut crate::leanh::LeanObject,
    mut v___y_5528_: *mut crate::leanh::LeanObject,
    mut v___y_5529_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_severity_boxed_5530_: u8 = 0;
    let mut v_isSilent_boxed_5531_: u8 = 0;
    let mut v_res_5532_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_severity_boxed_5530_ = (crate::leanh::lean_unbox(v_severity_5523_) as u8);
    v_isSilent_boxed_5531_ = (crate::leanh::lean_unbox(v_isSilent_5524_) as u8);
    v_res_5532_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4_spec__7_spec__16___redArg(v_ref_5521_, v_msgData_5522_, v_severity_boxed_5530_, v_isSilent_boxed_5531_, v___y_5525_, v___y_5526_, v___y_5527_, v___y_5528_);
    crate::leanh::lean_dec(v___y_5528_);
    crate::leanh::lean_dec_ref(v___y_5527_);
    crate::leanh::lean_dec(v___y_5526_);
    crate::leanh::lean_dec_ref(v___y_5525_);
    crate::leanh::lean_dec(v_ref_5521_);
    return v_res_5532_;
}
pub unsafe fn l_Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4_spec__7(
    mut v_ref_5533_: *mut crate::leanh::LeanObject,
    mut v_msgData_5534_: *mut crate::leanh::LeanObject,
    mut v___y_5535_: *mut crate::leanh::LeanObject,
    mut v___y_5536_: *mut crate::leanh::LeanObject,
    mut v___y_5537_: *mut crate::leanh::LeanObject,
    mut v___y_5538_: *mut crate::leanh::LeanObject,
    mut v___y_5539_: *mut crate::leanh::LeanObject,
    mut v___y_5540_: *mut crate::leanh::LeanObject,
    mut v___y_5541_: *mut crate::leanh::LeanObject,
    mut v___y_5542_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5544_: u8 = 0;
    let mut v___x_5545_: u8 = 0;
    let mut v___x_5546_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5544_ = 1;
    v___x_5545_ = 0;
    v___x_5546_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4_spec__7_spec__16___redArg(v_ref_5533_, v_msgData_5534_, v___x_5544_, v___x_5545_, v___y_5539_, v___y_5540_, v___y_5541_, v___y_5542_);
    return v___x_5546_;
}
pub unsafe fn l_Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4_spec__7___boxed(
    mut v_ref_5547_: *mut crate::leanh::LeanObject,
    mut v_msgData_5548_: *mut crate::leanh::LeanObject,
    mut v___y_5549_: *mut crate::leanh::LeanObject,
    mut v___y_5550_: *mut crate::leanh::LeanObject,
    mut v___y_5551_: *mut crate::leanh::LeanObject,
    mut v___y_5552_: *mut crate::leanh::LeanObject,
    mut v___y_5553_: *mut crate::leanh::LeanObject,
    mut v___y_5554_: *mut crate::leanh::LeanObject,
    mut v___y_5555_: *mut crate::leanh::LeanObject,
    mut v___y_5556_: *mut crate::leanh::LeanObject,
    mut v___y_5557_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5558_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5558_ = l_Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4_spec__7(v_ref_5547_, v_msgData_5548_, v___y_5549_, v___y_5550_, v___y_5551_, v___y_5552_, v___y_5553_, v___y_5554_, v___y_5555_, v___y_5556_);
    crate::leanh::lean_dec(v___y_5556_);
    crate::leanh::lean_dec_ref(v___y_5555_);
    crate::leanh::lean_dec(v___y_5554_);
    crate::leanh::lean_dec_ref(v___y_5553_);
    crate::leanh::lean_dec(v___y_5552_);
    crate::leanh::lean_dec_ref(v___y_5551_);
    crate::leanh::lean_dec(v___y_5550_);
    crate::leanh::lean_dec_ref(v___y_5549_);
    crate::leanh::lean_dec(v_ref_5547_);
    return v_res_5558_;
}
pub unsafe fn _init_l_Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_5560_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5561_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5560_ = l_Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4___closed__0;
    v___x_5561_ = l_Lean_stringToMessageData(v___x_5560_);
    return v___x_5561_;
}
pub unsafe fn _init_l_Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4___closed__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_5563_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5564_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5563_ = l_Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4___closed__2;
    v___x_5564_ = l_Lean_stringToMessageData(v___x_5563_);
    return v___x_5564_;
}
pub unsafe fn l_Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4(
    mut v_linterOption_5565_: *mut crate::leanh::LeanObject,
    mut v_stx_5566_: *mut crate::leanh::LeanObject,
    mut v_msg_5567_: *mut crate::leanh::LeanObject,
    mut v___y_5568_: *mut crate::leanh::LeanObject,
    mut v___y_5569_: *mut crate::leanh::LeanObject,
    mut v___y_5570_: *mut crate::leanh::LeanObject,
    mut v___y_5571_: *mut crate::leanh::LeanObject,
    mut v___y_5572_: *mut crate::leanh::LeanObject,
    mut v___y_5573_: *mut crate::leanh::LeanObject,
    mut v___y_5574_: *mut crate::leanh::LeanObject,
    mut v___y_5575_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_name_5577_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5579_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5580_: u8 = 0;
    let mut v___x_5581_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5582_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5584_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5585_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5586_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_disable_5587_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5588_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5589_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5590_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5591_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5592_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5593_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5594_: u8 = 0;
    let mut v_unused_5595_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_name_5577_ = crate::leanh::lean_ctor_get(v_linterOption_5565_, 0);
                v_isSharedCheck_5594_ =
                    (!crate::leanh::lean_is_exclusive(v_linterOption_5565_)) as u8;
                if v_isSharedCheck_5594_ == 0 {
                    v_unused_5595_ = crate::leanh::lean_ctor_get(v_linterOption_5565_, 1);
                    crate::leanh::lean_dec(v_unused_5595_);
                    v___x_5579_ = v_linterOption_5565_;
                    v_isShared_5580_ = v_isSharedCheck_5594_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_name_5577_);
                    crate::leanh::lean_dec(v_linterOption_5565_);
                    v___x_5579_ = crate::leanh::lean_box(0);
                    v_isShared_5580_ = v_isSharedCheck_5594_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_5581_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4___closed__1), core::ptr::addr_of_mut!(l_Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4___closed__1_once), _init_l_Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4___closed__1);
                crate::leanh::lean_inc(v_name_5577_);
                v___x_5582_ = l_Lean_MessageData_ofName(v_name_5577_);
                if v_isShared_5580_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_5579_, 7);
                    crate::leanh::lean_ctor_set(v___x_5579_, 1, v___x_5582_);
                    crate::leanh::lean_ctor_set(v___x_5579_, 0, v___x_5581_);
                    v___x_5584_ = v___x_5579_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5593_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5593_, 0, v___x_5581_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5593_, 1, v___x_5582_);
                    v___x_5584_ = v_reuseFailAlloc_5593_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_5585_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4___closed__3), core::ptr::addr_of_mut!(l_Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4___closed__3_once), _init_l_Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4___closed__3);
                v___x_5586_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_5586_, 0, v___x_5584_);
                crate::leanh::lean_ctor_set(v___x_5586_, 1, v___x_5585_);
                v_disable_5587_ = l_Lean_MessageData_note(v___x_5586_);
                v___x_5588_ = l_Lean_Linter_linterMessageTag;
                v___x_5589_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_5589_, 0, v_msg_5567_);
                crate::leanh::lean_ctor_set(v___x_5589_, 1, v_disable_5587_);
                v___x_5590_ = crate::leanh::lean_alloc_ctor(8, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_5590_, 0, v___x_5588_);
                crate::leanh::lean_ctor_set(v___x_5590_, 1, v___x_5589_);
                v___x_5591_ = crate::leanh::lean_alloc_ctor(8, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_5591_, 0, v_name_5577_);
                crate::leanh::lean_ctor_set(v___x_5591_, 1, v___x_5590_);
                v___x_5592_ = l_Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4_spec__7(v_stx_5566_, v___x_5591_, v___y_5568_, v___y_5569_, v___y_5570_, v___y_5571_, v___y_5572_, v___y_5573_, v___y_5574_, v___y_5575_);
                return v___x_5592_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4___boxed(
    mut v_linterOption_5596_: *mut crate::leanh::LeanObject,
    mut v_stx_5597_: *mut crate::leanh::LeanObject,
    mut v_msg_5598_: *mut crate::leanh::LeanObject,
    mut v___y_5599_: *mut crate::leanh::LeanObject,
    mut v___y_5600_: *mut crate::leanh::LeanObject,
    mut v___y_5601_: *mut crate::leanh::LeanObject,
    mut v___y_5602_: *mut crate::leanh::LeanObject,
    mut v___y_5603_: *mut crate::leanh::LeanObject,
    mut v___y_5604_: *mut crate::leanh::LeanObject,
    mut v___y_5605_: *mut crate::leanh::LeanObject,
    mut v___y_5606_: *mut crate::leanh::LeanObject,
    mut v___y_5607_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5608_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5608_ = l_Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4(v_linterOption_5596_, v_stx_5597_, v_msg_5598_, v___y_5599_, v___y_5600_, v___y_5601_, v___y_5602_, v___y_5603_, v___y_5604_, v___y_5605_, v___y_5606_);
    crate::leanh::lean_dec(v___y_5606_);
    crate::leanh::lean_dec_ref(v___y_5605_);
    crate::leanh::lean_dec(v___y_5604_);
    crate::leanh::lean_dec_ref(v___y_5603_);
    crate::leanh::lean_dec(v___y_5602_);
    crate::leanh::lean_dec_ref(v___y_5601_);
    crate::leanh::lean_dec(v___y_5600_);
    crate::leanh::lean_dec_ref(v___y_5599_);
    crate::leanh::lean_dec(v_stx_5597_);
    return v_res_5608_;
}
pub unsafe fn l_Lean_Elab_withInfoTreeContext___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__8___redArg___lam__0(
    mut v___y_5609_: *mut crate::leanh::LeanObject,
    mut v_mkInfoTree_5610_: *mut crate::leanh::LeanObject,
    mut v___y_5611_: *mut crate::leanh::LeanObject,
    mut v___y_5612_: *mut crate::leanh::LeanObject,
    mut v___y_5613_: *mut crate::leanh::LeanObject,
    mut v___y_5614_: *mut crate::leanh::LeanObject,
    mut v___y_5615_: *mut crate::leanh::LeanObject,
    mut v___y_5616_: *mut crate::leanh::LeanObject,
    mut v___y_5617_: *mut crate::leanh::LeanObject,
    mut v_a_5618_: *mut crate::leanh::LeanObject,
    mut v_a_x3f_5619_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5621_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_infoState_5622_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_trees_5623_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5624_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5625_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5627_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5628_: u8 = 0;
    let mut v___x_5629_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_infoState_5630_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_5631_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_5632_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ngen_5633_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_5634_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_traceState_5635_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_cache_5636_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_messages_5637_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_5638_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5640_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5641_: u8 = 0;
    let mut v_enabled_5642_: u8 = 0;
    let mut v_assignment_5643_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_lazyAssignment_5644_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5646_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5647_: u8 = 0;
    let mut v___x_5648_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5650_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5652_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5653_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5654_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5656_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5657_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5658_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5659_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5660_: u8 = 0;
    let mut v_unused_5661_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5662_: u8 = 0;
    let mut v_isSharedCheck_5663_: u8 = 0;
    let mut v_a_5664_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5666_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5667_: u8 = 0;
    let mut v___x_5669_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5670_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5671_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5621_ = lean_st_ref_get(v___y_5609_);
                v_infoState_5622_ = crate::leanh::lean_ctor_get(v___x_5621_, 7);
                crate::leanh::lean_inc_ref(v_infoState_5622_);
                crate::leanh::lean_dec(v___x_5621_);
                v_trees_5623_ = crate::leanh::lean_ctor_get(v_infoState_5622_, 2);
                crate::leanh::lean_inc_ref(v_trees_5623_);
                crate::leanh::lean_dec_ref(v_infoState_5622_);
                crate::leanh::lean_inc(v___y_5609_);
                crate::leanh::lean_inc_ref(v___y_5617_);
                crate::leanh::lean_inc(v___y_5616_);
                crate::leanh::lean_inc_ref(v___y_5615_);
                crate::leanh::lean_inc(v___y_5614_);
                crate::leanh::lean_inc_ref(v___y_5613_);
                crate::leanh::lean_inc(v___y_5612_);
                crate::leanh::lean_inc_ref(v___y_5611_);
                v___x_5624_ = crate::leanh::lean_apply_10(
                    v_mkInfoTree_5610_,
                    v_trees_5623_,
                    v___y_5611_,
                    v___y_5612_,
                    v___y_5613_,
                    v___y_5614_,
                    v___y_5615_,
                    v___y_5616_,
                    v___y_5617_,
                    v___y_5609_,
                    crate::leanh::lean_box(0),
                );
                if crate::leanh::lean_obj_tag(v___x_5624_) == 0 {
                    v_a_5625_ = crate::leanh::lean_ctor_get(v___x_5624_, 0);
                    v_isSharedCheck_5663_ = (!crate::leanh::lean_is_exclusive(v___x_5624_)) as u8;
                    if v_isSharedCheck_5663_ == 0 {
                        v___x_5627_ = v___x_5624_;
                        v_isShared_5628_ = v_isSharedCheck_5663_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_5625_);
                        crate::leanh::lean_dec(v___x_5624_);
                        v___x_5627_ = crate::leanh::lean_box(0);
                        v_isShared_5628_ = v_isSharedCheck_5663_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_a_5618_);
                    v_a_5664_ = crate::leanh::lean_ctor_get(v___x_5624_, 0);
                    v_isSharedCheck_5671_ = (!crate::leanh::lean_is_exclusive(v___x_5624_)) as u8;
                    if v_isSharedCheck_5671_ == 0 {
                        v___x_5666_ = v___x_5624_;
                        v_isShared_5667_ = v_isSharedCheck_5671_;
                        state = 7;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_5664_);
                        crate::leanh::lean_dec(v___x_5624_);
                        v___x_5666_ = crate::leanh::lean_box(0);
                        v_isShared_5667_ = v_isSharedCheck_5671_;
                        state = 7;
                        continue;
                    }
                }
            }
            1 => {
                v___x_5629_ = lean_st_ref_take(v___y_5609_);
                v_infoState_5630_ = crate::leanh::lean_ctor_get(v___x_5629_, 7);
                v_env_5631_ = crate::leanh::lean_ctor_get(v___x_5629_, 0);
                v_nextMacroScope_5632_ = crate::leanh::lean_ctor_get(v___x_5629_, 1);
                v_ngen_5633_ = crate::leanh::lean_ctor_get(v___x_5629_, 2);
                v_auxDeclNGen_5634_ = crate::leanh::lean_ctor_get(v___x_5629_, 3);
                v_traceState_5635_ = crate::leanh::lean_ctor_get(v___x_5629_, 4);
                v_cache_5636_ = crate::leanh::lean_ctor_get(v___x_5629_, 5);
                v_messages_5637_ = crate::leanh::lean_ctor_get(v___x_5629_, 6);
                v_snapshotTasks_5638_ = crate::leanh::lean_ctor_get(v___x_5629_, 8);
                v_isSharedCheck_5662_ = (!crate::leanh::lean_is_exclusive(v___x_5629_)) as u8;
                if v_isSharedCheck_5662_ == 0 {
                    v___x_5640_ = v___x_5629_;
                    v_isShared_5641_ = v_isSharedCheck_5662_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snapshotTasks_5638_);
                    crate::leanh::lean_inc(v_infoState_5630_);
                    crate::leanh::lean_inc(v_messages_5637_);
                    crate::leanh::lean_inc(v_cache_5636_);
                    crate::leanh::lean_inc(v_traceState_5635_);
                    crate::leanh::lean_inc(v_auxDeclNGen_5634_);
                    crate::leanh::lean_inc(v_ngen_5633_);
                    crate::leanh::lean_inc(v_nextMacroScope_5632_);
                    crate::leanh::lean_inc(v_env_5631_);
                    crate::leanh::lean_dec(v___x_5629_);
                    v___x_5640_ = crate::leanh::lean_box(0);
                    v_isShared_5641_ = v_isSharedCheck_5662_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_enabled_5642_ = crate::leanh::lean_ctor_get_uint8(
                    v_infoState_5630_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u32,
                );
                v_assignment_5643_ = crate::leanh::lean_ctor_get(v_infoState_5630_, 0);
                v_lazyAssignment_5644_ = crate::leanh::lean_ctor_get(v_infoState_5630_, 1);
                v_isSharedCheck_5660_ = (!crate::leanh::lean_is_exclusive(v_infoState_5630_)) as u8;
                if v_isSharedCheck_5660_ == 0 {
                    v_unused_5661_ = crate::leanh::lean_ctor_get(v_infoState_5630_, 2);
                    crate::leanh::lean_dec(v_unused_5661_);
                    v___x_5646_ = v_infoState_5630_;
                    v_isShared_5647_ = v_isSharedCheck_5660_;
                    state = 3;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_lazyAssignment_5644_);
                    crate::leanh::lean_inc(v_assignment_5643_);
                    crate::leanh::lean_dec(v_infoState_5630_);
                    v___x_5646_ = crate::leanh::lean_box(0);
                    v_isShared_5647_ = v_isSharedCheck_5660_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_5648_ = l_Lean_PersistentArray_push___redArg(v_a_5618_, v_a_5625_);
                if v_isShared_5647_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5646_, 2, v___x_5648_);
                    v___x_5650_ = v___x_5646_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_5659_ = crate::leanh::lean_alloc_ctor(0, 3, (1) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5659_, 0, v_assignment_5643_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5659_, 1, v_lazyAssignment_5644_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5659_, 2, v___x_5648_);
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_5659_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u32,
                        v_enabled_5642_,
                    );
                    v___x_5650_ = v_reuseFailAlloc_5659_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                if v_isShared_5641_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5640_, 7, v___x_5650_);
                    v___x_5652_ = v___x_5640_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_5658_ = crate::leanh::lean_alloc_ctor(0, 9, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5658_, 0, v_env_5631_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5658_, 1, v_nextMacroScope_5632_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5658_, 2, v_ngen_5633_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5658_, 3, v_auxDeclNGen_5634_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5658_, 4, v_traceState_5635_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5658_, 5, v_cache_5636_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5658_, 6, v_messages_5637_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5658_, 7, v___x_5650_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5658_, 8, v_snapshotTasks_5638_);
                    v___x_5652_ = v_reuseFailAlloc_5658_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v___x_5653_ = lean_st_ref_set(v___y_5609_, v___x_5652_);
                v___x_5654_ = crate::leanh::lean_box(0);
                if v_isShared_5628_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5627_, 0, v___x_5654_);
                    v___x_5656_ = v___x_5627_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_5657_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5657_, 0, v___x_5654_);
                    v___x_5656_ = v_reuseFailAlloc_5657_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_5656_;
            }
            7 => {
                if v_isShared_5667_ == 0 {
                    v___x_5669_ = v___x_5666_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_5670_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5670_, 0, v_a_5664_);
                    v___x_5669_ = v_reuseFailAlloc_5670_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_5669_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_withInfoTreeContext___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__8___redArg___lam__0___boxed(
    mut v___y_5672_: *mut crate::leanh::LeanObject,
    mut v_mkInfoTree_5673_: *mut crate::leanh::LeanObject,
    mut v___y_5674_: *mut crate::leanh::LeanObject,
    mut v___y_5675_: *mut crate::leanh::LeanObject,
    mut v___y_5676_: *mut crate::leanh::LeanObject,
    mut v___y_5677_: *mut crate::leanh::LeanObject,
    mut v___y_5678_: *mut crate::leanh::LeanObject,
    mut v___y_5679_: *mut crate::leanh::LeanObject,
    mut v___y_5680_: *mut crate::leanh::LeanObject,
    mut v_a_5681_: *mut crate::leanh::LeanObject,
    mut v_a_x3f_5682_: *mut crate::leanh::LeanObject,
    mut v___y_5683_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5684_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5684_ = l_Lean_Elab_withInfoTreeContext___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__8___redArg___lam__0(v___y_5672_, v_mkInfoTree_5673_, v___y_5674_, v___y_5675_, v___y_5676_, v___y_5677_, v___y_5678_, v___y_5679_, v___y_5680_, v_a_5681_, v_a_x3f_5682_);
    crate::leanh::lean_dec(v_a_x3f_5682_);
    crate::leanh::lean_dec_ref(v___y_5680_);
    crate::leanh::lean_dec(v___y_5679_);
    crate::leanh::lean_dec_ref(v___y_5678_);
    crate::leanh::lean_dec(v___y_5677_);
    crate::leanh::lean_dec_ref(v___y_5676_);
    crate::leanh::lean_dec(v___y_5675_);
    crate::leanh::lean_dec_ref(v___y_5674_);
    crate::leanh::lean_dec(v___y_5672_);
    return v_res_5684_;
}
pub unsafe fn l_Lean_Elab_withInfoTreeContext___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__8___redArg(
    mut v_x_5685_: *mut crate::leanh::LeanObject,
    mut v_mkInfoTree_5686_: *mut crate::leanh::LeanObject,
    mut v___y_5687_: *mut crate::leanh::LeanObject,
    mut v___y_5688_: *mut crate::leanh::LeanObject,
    mut v___y_5689_: *mut crate::leanh::LeanObject,
    mut v___y_5690_: *mut crate::leanh::LeanObject,
    mut v___y_5691_: *mut crate::leanh::LeanObject,
    mut v___y_5692_: *mut crate::leanh::LeanObject,
    mut v___y_5693_: *mut crate::leanh::LeanObject,
    mut v___y_5694_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5696_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_infoState_5697_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_enabled_5698_: u8 = 0;
    let mut v___x_5699_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5700_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5701_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_5702_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5703_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5705_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5706_: u8 = 0;
    let mut v___x_5708_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5709_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5711_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5712_: u8 = 0;
    let mut v___x_5714_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5715_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5716_: u8 = 0;
    let mut v_unused_5717_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5718_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5720_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5721_: u8 = 0;
    let mut v___x_5723_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5724_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5725_: u8 = 0;
    let mut v_reuseFailAlloc_5726_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5727_: u8 = 0;
    let mut v_a_5728_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5729_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5730_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5732_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5733_: u8 = 0;
    let mut v___x_5735_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5736_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5737_: u8 = 0;
    let mut v_unused_5738_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5739_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5741_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5742_: u8 = 0;
    let mut v___x_5744_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5745_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5746_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5696_ = lean_st_ref_get(v___y_5694_);
                v_infoState_5697_ = crate::leanh::lean_ctor_get(v___x_5696_, 7);
                crate::leanh::lean_inc_ref(v_infoState_5697_);
                crate::leanh::lean_dec(v___x_5696_);
                v_enabled_5698_ = crate::leanh::lean_ctor_get_uint8(
                    v_infoState_5697_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u32,
                );
                crate::leanh::lean_dec_ref(v_infoState_5697_);
                if v_enabled_5698_ == 0 {
                    crate::leanh::lean_dec_ref(v_mkInfoTree_5686_);
                    crate::leanh::lean_inc(v___y_5694_);
                    crate::leanh::lean_inc_ref(v___y_5693_);
                    crate::leanh::lean_inc(v___y_5692_);
                    crate::leanh::lean_inc_ref(v___y_5691_);
                    crate::leanh::lean_inc(v___y_5690_);
                    crate::leanh::lean_inc_ref(v___y_5689_);
                    crate::leanh::lean_inc(v___y_5688_);
                    crate::leanh::lean_inc_ref(v___y_5687_);
                    v___x_5699_ = crate::leanh::lean_apply_9(
                        v_x_5685_,
                        v___y_5687_,
                        v___y_5688_,
                        v___y_5689_,
                        v___y_5690_,
                        v___y_5691_,
                        v___y_5692_,
                        v___y_5693_,
                        v___y_5694_,
                        crate::leanh::lean_box(0),
                    );
                    return v___x_5699_;
                } else {
                    v___x_5700_ = l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__7___redArg(v___y_5694_);
                    v_a_5701_ = crate::leanh::lean_ctor_get(v___x_5700_, 0);
                    crate::leanh::lean_inc(v_a_5701_);
                    crate::leanh::lean_dec_ref(v___x_5700_);
                    crate::leanh::lean_inc(v___y_5694_);
                    crate::leanh::lean_inc_ref(v___y_5693_);
                    crate::leanh::lean_inc(v___y_5692_);
                    crate::leanh::lean_inc_ref(v___y_5691_);
                    crate::leanh::lean_inc(v___y_5690_);
                    crate::leanh::lean_inc_ref(v___y_5689_);
                    crate::leanh::lean_inc(v___y_5688_);
                    crate::leanh::lean_inc_ref(v___y_5687_);
                    v_r_5702_ = crate::leanh::lean_apply_9(
                        v_x_5685_,
                        v___y_5687_,
                        v___y_5688_,
                        v___y_5689_,
                        v___y_5690_,
                        v___y_5691_,
                        v___y_5692_,
                        v___y_5693_,
                        v___y_5694_,
                        crate::leanh::lean_box(0),
                    );
                    if crate::leanh::lean_obj_tag(v_r_5702_) == 0 {
                        v_a_5703_ = crate::leanh::lean_ctor_get(v_r_5702_, 0);
                        v_isSharedCheck_5727_ = (!crate::leanh::lean_is_exclusive(v_r_5702_)) as u8;
                        if v_isSharedCheck_5727_ == 0 {
                            v___x_5705_ = v_r_5702_;
                            v_isShared_5706_ = v_isSharedCheck_5727_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_5703_);
                            crate::leanh::lean_dec(v_r_5702_);
                            v___x_5705_ = crate::leanh::lean_box(0);
                            v_isShared_5706_ = v_isSharedCheck_5727_;
                            state = 1;
                            continue;
                        }
                    } else {
                        v_a_5728_ = crate::leanh::lean_ctor_get(v_r_5702_, 0);
                        crate::leanh::lean_inc(v_a_5728_);
                        crate::leanh::lean_dec_ref_known(v_r_5702_, 1);
                        v___x_5729_ = crate::leanh::lean_box(0);
                        v___x_5730_ = l_Lean_Elab_withInfoTreeContext___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__8___redArg___lam__0(v___y_5694_, v_mkInfoTree_5686_, v___y_5687_, v___y_5688_, v___y_5689_, v___y_5690_, v___y_5691_, v___y_5692_, v___y_5693_, v_a_5701_, v___x_5729_);
                        if crate::leanh::lean_obj_tag(v___x_5730_) == 0 {
                            v_isSharedCheck_5737_ =
                                (!crate::leanh::lean_is_exclusive(v___x_5730_)) as u8;
                            if v_isSharedCheck_5737_ == 0 {
                                v_unused_5738_ = crate::leanh::lean_ctor_get(v___x_5730_, 0);
                                crate::leanh::lean_dec(v_unused_5738_);
                                v___x_5732_ = v___x_5730_;
                                v_isShared_5733_ = v_isSharedCheck_5737_;
                                state = 7;
                                continue;
                            } else {
                                crate::leanh::lean_dec(v___x_5730_);
                                v___x_5732_ = crate::leanh::lean_box(0);
                                v_isShared_5733_ = v_isSharedCheck_5737_;
                                state = 7;
                                continue;
                            }
                        } else {
                            crate::leanh::lean_dec(v_a_5728_);
                            v_a_5739_ = crate::leanh::lean_ctor_get(v___x_5730_, 0);
                            v_isSharedCheck_5746_ =
                                (!crate::leanh::lean_is_exclusive(v___x_5730_)) as u8;
                            if v_isSharedCheck_5746_ == 0 {
                                v___x_5741_ = v___x_5730_;
                                v_isShared_5742_ = v_isSharedCheck_5746_;
                                state = 9;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_5739_);
                                crate::leanh::lean_dec(v___x_5730_);
                                v___x_5741_ = crate::leanh::lean_box(0);
                                v_isShared_5742_ = v_isSharedCheck_5746_;
                                state = 9;
                                continue;
                            }
                        }
                    }
                }
            }
            1 => {
                crate::leanh::lean_inc(v_a_5703_);
                if v_isShared_5706_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_5705_, 1);
                    v___x_5708_ = v___x_5705_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5726_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5726_, 0, v_a_5703_);
                    v___x_5708_ = v_reuseFailAlloc_5726_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_5709_ = l_Lean_Elab_withInfoTreeContext___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__8___redArg___lam__0(v___y_5694_, v_mkInfoTree_5686_, v___y_5687_, v___y_5688_, v___y_5689_, v___y_5690_, v___y_5691_, v___y_5692_, v___y_5693_, v_a_5701_, v___x_5708_);
                crate::leanh::lean_dec_ref(v___x_5708_);
                if crate::leanh::lean_obj_tag(v___x_5709_) == 0 {
                    v_isSharedCheck_5716_ = (!crate::leanh::lean_is_exclusive(v___x_5709_)) as u8;
                    if v_isSharedCheck_5716_ == 0 {
                        v_unused_5717_ = crate::leanh::lean_ctor_get(v___x_5709_, 0);
                        crate::leanh::lean_dec(v_unused_5717_);
                        v___x_5711_ = v___x_5709_;
                        v_isShared_5712_ = v_isSharedCheck_5716_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v___x_5709_);
                        v___x_5711_ = crate::leanh::lean_box(0);
                        v_isShared_5712_ = v_isSharedCheck_5716_;
                        state = 3;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_a_5703_);
                    v_a_5718_ = crate::leanh::lean_ctor_get(v___x_5709_, 0);
                    v_isSharedCheck_5725_ = (!crate::leanh::lean_is_exclusive(v___x_5709_)) as u8;
                    if v_isSharedCheck_5725_ == 0 {
                        v___x_5720_ = v___x_5709_;
                        v_isShared_5721_ = v_isSharedCheck_5725_;
                        state = 5;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_5718_);
                        crate::leanh::lean_dec(v___x_5709_);
                        v___x_5720_ = crate::leanh::lean_box(0);
                        v_isShared_5721_ = v_isSharedCheck_5725_;
                        state = 5;
                        continue;
                    }
                }
            }
            3 => {
                if v_isShared_5712_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5711_, 0, v_a_5703_);
                    v___x_5714_ = v___x_5711_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_5715_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5715_, 0, v_a_5703_);
                    v___x_5714_ = v_reuseFailAlloc_5715_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_5714_;
            }
            5 => {
                if v_isShared_5721_ == 0 {
                    v___x_5723_ = v___x_5720_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_5724_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5724_, 0, v_a_5718_);
                    v___x_5723_ = v_reuseFailAlloc_5724_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_5723_;
            }
            7 => {
                if v_isShared_5733_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_5732_, 1);
                    crate::leanh::lean_ctor_set(v___x_5732_, 0, v_a_5728_);
                    v___x_5735_ = v___x_5732_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_5736_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5736_, 0, v_a_5728_);
                    v___x_5735_ = v_reuseFailAlloc_5736_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_5735_;
            }
            9 => {
                if v_isShared_5742_ == 0 {
                    v___x_5744_ = v___x_5741_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_5745_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5745_, 0, v_a_5739_);
                    v___x_5744_ = v_reuseFailAlloc_5745_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_5744_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_withInfoTreeContext___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__8___redArg___boxed(
    mut v_x_5747_: *mut crate::leanh::LeanObject,
    mut v_mkInfoTree_5748_: *mut crate::leanh::LeanObject,
    mut v___y_5749_: *mut crate::leanh::LeanObject,
    mut v___y_5750_: *mut crate::leanh::LeanObject,
    mut v___y_5751_: *mut crate::leanh::LeanObject,
    mut v___y_5752_: *mut crate::leanh::LeanObject,
    mut v___y_5753_: *mut crate::leanh::LeanObject,
    mut v___y_5754_: *mut crate::leanh::LeanObject,
    mut v___y_5755_: *mut crate::leanh::LeanObject,
    mut v___y_5756_: *mut crate::leanh::LeanObject,
    mut v___y_5757_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5758_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5758_ = l_Lean_Elab_withInfoTreeContext___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__8___redArg(v_x_5747_, v_mkInfoTree_5748_, v___y_5749_, v___y_5750_, v___y_5751_, v___y_5752_, v___y_5753_, v___y_5754_, v___y_5755_, v___y_5756_);
    crate::leanh::lean_dec(v___y_5756_);
    crate::leanh::lean_dec_ref(v___y_5755_);
    crate::leanh::lean_dec(v___y_5754_);
    crate::leanh::lean_dec_ref(v___y_5753_);
    crate::leanh::lean_dec(v___y_5752_);
    crate::leanh::lean_dec_ref(v___y_5751_);
    crate::leanh::lean_dec(v___y_5750_);
    crate::leanh::lean_dec_ref(v___y_5749_);
    return v_res_5758_;
}
pub unsafe fn l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__3_spec__5___redArg(
    mut v_o_5759_: *mut crate::leanh::LeanObject,
    mut v___y_5760_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5762_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_5763_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5764_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toEnvExtension_5765_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_asyncMode_5766_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5767_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5768_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_linterSets_5769_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5770_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5771_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5762_ = lean_st_ref_get(v___y_5760_);
    v_env_5763_ = crate::leanh::lean_ctor_get(v___x_5762_, 0);
    crate::leanh::lean_inc_ref(v_env_5763_);
    crate::leanh::lean_dec(v___x_5762_);
    v___x_5764_ = l_Lean_Linter_linterSetsExt;
    v_toEnvExtension_5765_ = crate::leanh::lean_ctor_get(v___x_5764_, 0);
    v_asyncMode_5766_ = crate::leanh::lean_ctor_get(v_toEnvExtension_5765_, 2);
    v___x_5767_ = crate::leanh::lean_box(1);
    v___x_5768_ = crate::leanh::lean_box(0);
    v_linterSets_5769_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(
        v___x_5767_,
        v___x_5764_,
        v_env_5763_,
        v_asyncMode_5766_,
        v___x_5768_,
    );
    v___x_5770_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_5770_, 0, v_o_5759_);
    crate::leanh::lean_ctor_set(v___x_5770_, 1, v_linterSets_5769_);
    v___x_5771_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_5771_, 0, v___x_5770_);
    return v___x_5771_;
}
pub unsafe fn l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__3_spec__5___redArg___boxed(
    mut v_o_5772_: *mut crate::leanh::LeanObject,
    mut v___y_5773_: *mut crate::leanh::LeanObject,
    mut v___y_5774_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5775_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5775_ = l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__3_spec__5___redArg(v_o_5772_, v___y_5773_);
    crate::leanh::lean_dec(v___y_5773_);
    return v_res_5775_;
}
pub unsafe fn l_Lean_Linter_getLinterOptions___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__3(
    mut v___y_5776_: *mut crate::leanh::LeanObject,
    mut v___y_5777_: *mut crate::leanh::LeanObject,
    mut v___y_5778_: *mut crate::leanh::LeanObject,
    mut v___y_5779_: *mut crate::leanh::LeanObject,
    mut v___y_5780_: *mut crate::leanh::LeanObject,
    mut v___y_5781_: *mut crate::leanh::LeanObject,
    mut v___y_5782_: *mut crate::leanh::LeanObject,
    mut v___y_5783_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_options_5785_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5786_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_options_5785_ = crate::leanh::lean_ctor_get(v___y_5782_, 2);
    crate::leanh::lean_inc_ref(v_options_5785_);
    v___x_5786_ = l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__3_spec__5___redArg(v_options_5785_, v___y_5783_);
    return v___x_5786_;
}
pub unsafe fn l_Lean_Linter_getLinterOptions___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__3___boxed(
    mut v___y_5787_: *mut crate::leanh::LeanObject,
    mut v___y_5788_: *mut crate::leanh::LeanObject,
    mut v___y_5789_: *mut crate::leanh::LeanObject,
    mut v___y_5790_: *mut crate::leanh::LeanObject,
    mut v___y_5791_: *mut crate::leanh::LeanObject,
    mut v___y_5792_: *mut crate::leanh::LeanObject,
    mut v___y_5793_: *mut crate::leanh::LeanObject,
    mut v___y_5794_: *mut crate::leanh::LeanObject,
    mut v___y_5795_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5796_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5796_ = l_Lean_Linter_getLinterOptions___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__3(v___y_5787_, v___y_5788_, v___y_5789_, v___y_5790_, v___y_5791_, v___y_5792_, v___y_5793_, v___y_5794_);
    crate::leanh::lean_dec(v___y_5794_);
    crate::leanh::lean_dec_ref(v___y_5793_);
    crate::leanh::lean_dec(v___y_5792_);
    crate::leanh::lean_dec_ref(v___y_5791_);
    crate::leanh::lean_dec(v___y_5790_);
    crate::leanh::lean_dec_ref(v___y_5789_);
    crate::leanh::lean_dec(v___y_5788_);
    crate::leanh::lean_dec_ref(v___y_5787_);
    return v_res_5796_;
}
pub unsafe fn _init_l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__4___closed__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_5801_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5802_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5801_ = l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__4___closed__2;
    v___x_5802_ = l_Lean_stringToMessageData(v___x_5801_);
    return v___x_5802_;
}
pub unsafe fn _init_l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__4___closed__5()
-> *mut crate::leanh::LeanObject {
    let mut v___x_5804_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5805_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5804_ = l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__4___closed__4;
    v___x_5805_ = l_Lean_stringToMessageData(v___x_5804_);
    return v___x_5805_;
}
pub unsafe fn _init_l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__4___closed__7()
-> *mut crate::leanh::LeanObject {
    let mut v___x_5807_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5808_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5807_ = l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__4___closed__6;
    v___x_5808_ = l_Lean_stringToMessageData(v___x_5807_);
    return v___x_5808_;
}
pub unsafe fn _init_l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__4___closed__9()
-> *mut crate::leanh::LeanObject {
    let mut v___x_5810_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5811_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5810_ = l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__4___closed__8;
    v___x_5811_ = l_Lean_stringToMessageData(v___x_5810_);
    return v___x_5811_;
}
pub unsafe fn _init_l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__4___closed__11()
-> *mut crate::leanh::LeanObject {
    let mut v___x_5813_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5814_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5813_ = l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__4___closed__10;
    v___x_5814_ = l_Lean_stringToMessageData(v___x_5813_);
    return v___x_5814_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__4(
    mut v_usingArg_5818_: *mut crate::leanh::LeanObject,
    mut v_snd_5819_: *mut crate::leanh::LeanObject,
    mut v___x_5820_: u8,
    mut v___x_5821_: u8,
    mut v___x_5822_: *mut crate::leanh::LeanObject,
    mut v_useReducible_5823_: u8,
    mut v___x_5824_: u8,
    mut v___x_5825_: *mut crate::leanh::LeanObject,
    mut v___x_5826_: *mut crate::leanh::LeanObject,
    mut v_simprocs_5827_: *mut crate::leanh::LeanObject,
    mut v_discharge_x3f_5828_: *mut crate::leanh::LeanObject,
    mut v_snd_5829_: *mut crate::leanh::LeanObject,
    mut v___x_5830_: *mut crate::leanh::LeanObject,
    mut v___f_5831_: *mut crate::leanh::LeanObject,
    mut v___y_5832_: *mut crate::leanh::LeanObject,
    mut v___y_5833_: *mut crate::leanh::LeanObject,
    mut v___y_5834_: *mut crate::leanh::LeanObject,
    mut v___y_5835_: *mut crate::leanh::LeanObject,
    mut v___y_5836_: *mut crate::leanh::LeanObject,
    mut v___y_5837_: *mut crate::leanh::LeanObject,
    mut v___y_5838_: *mut crate::leanh::LeanObject,
    mut v___y_5839_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_5842_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5843_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5844_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5845_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5847_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5848_: u8 = 0;
    let mut v___x_5850_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5851_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5852_: u8 = 0;
    let mut v_unused_5853_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5855_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5856_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5857_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5858_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5859_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5860_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5861_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5862_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5863_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5864_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5865_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5866_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5867_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5868_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5869_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5870_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5871_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5872_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5873_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5874_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5875_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5876_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5877_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5878_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5879_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5880_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5881_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5883_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5884_: u8 = 0;
    let mut v___x_5886_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5887_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5888_: u8 = 0;
    let mut v_a_5889_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5891_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5892_: u8 = 0;
    let mut v___x_5894_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5895_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5896_: u8 = 0;
    let mut v_a_5897_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5899_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5900_: u8 = 0;
    let mut v___x_5902_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5903_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5904_: u8 = 0;
    let mut v___y_5906_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5907_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5908_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5909_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5910_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5911_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5912_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5913_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5914_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5915_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5916_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5917_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5918_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5919_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5920_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5921_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5922_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5923_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5924_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5925_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5926_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5927_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5928_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_5929_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_5930_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5932_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5933_: u8 = 0;
    let mut v___x_5934_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5935_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5936_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5937_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_5938_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_5939_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5941_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5942_: u8 = 0;
    let mut v___x_5943_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5944_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5945_: u8 = 0;
    let mut v_fvarId_5946_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_lctx_5947_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5948_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_5949_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5950_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5951_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5952_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5954_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5955_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5957_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5958_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5959_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5960_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5961_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5962_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5964_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5965_: u8 = 0;
    let mut v___x_5967_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5968_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5969_: u8 = 0;
    let mut v_reuseFailAlloc_5970_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5971_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5972_: u8 = 0;
    let mut v_unused_5973_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_5974_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_5975_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_5976_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_5977_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5978_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5979_: u8 = 0;
    let mut v___x_5980_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5981_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5983_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5984_: u8 = 0;
    let mut v___x_5986_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5987_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5988_: u8 = 0;
    let mut v_isSharedCheck_5989_: u8 = 0;
    let mut v_a_5990_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5992_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5993_: u8 = 0;
    let mut v___x_5995_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5996_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5997_: u8 = 0;
    let mut v_a_5998_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6000_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6001_: u8 = 0;
    let mut v___x_6003_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6004_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6005_: u8 = 0;
    let mut v_a_6006_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6008_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6009_: u8 = 0;
    let mut v___x_6011_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6012_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6013_: u8 = 0;
    let mut v_a_6014_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6016_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6017_: u8 = 0;
    let mut v___x_6019_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6020_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6021_: u8 = 0;
    let mut v_val_6022_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6024_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6025_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6026_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6027_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6028_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6029_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6030_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6031_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6032_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6033_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6034_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6035_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6036_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_6037_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6038_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6039_: u8 = 0;
    let mut v___x_6040_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6041_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6042_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6043_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6044_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6045_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6046_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6047_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6048_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6049_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6051_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6052_: u8 = 0;
    let mut v___x_6054_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6055_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6056_: u8 = 0;
    let mut v_mvarCounter_6057_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6058_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6060_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6061_: u8 = 0;
    let mut v___x_6063_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6064_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6065_: u8 = 0;
    let mut v_a_6066_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6068_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6069_: u8 = 0;
    let mut v___x_6071_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6072_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6073_: u8 = 0;
    let mut v___x_6074_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_infoState_6075_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_enabled_6076_: u8 = 0;
    let mut v___x_6077_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6078_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_6079_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6080_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6081_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6083_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6084_: u8 = 0;
    let mut v___x_6086_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6087_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6088_: u8 = 0;
    let mut v_lctx_6089_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6090_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6091_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_6092_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6093_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6094_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6095_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6096_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6097_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6099_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6100_: u8 = 0;
    let mut v_fst_6101_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_6102_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_6103_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_6104_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6105_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6107_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6108_: u8 = 0;
    let mut v___x_6110_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6111_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6112_: u8 = 0;
    let mut v_unused_6113_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6114_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6116_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6117_: u8 = 0;
    let mut v___x_6119_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6120_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6121_: u8 = 0;
    let mut v___x_6123_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6124_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6125_: u8 = 0;
    let mut v_a_6126_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6128_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6129_: u8 = 0;
    let mut v___x_6131_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6132_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6133_: u8 = 0;
    let mut v___x_6134_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6136_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6137_: u8 = 0;
    let mut v___x_6139_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6140_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6141_: u8 = 0;
    let mut v_unused_6142_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6143_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6145_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6146_: u8 = 0;
    let mut v___x_6148_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6149_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6150_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_usingArg_5818_) == 1 {
                    v_val_6022_ = crate::leanh::lean_ctor_get(v_usingArg_5818_, 0);
                    crate::leanh::lean_inc(v_val_6022_);
                    crate::leanh::lean_dec_ref_known(v_usingArg_5818_, 1);
                    v___x_6074_ = lean_st_ref_get(v___y_5839_);
                    v_infoState_6075_ = crate::leanh::lean_ctor_get(v___x_6074_, 7);
                    crate::leanh::lean_inc_ref(v_infoState_6075_);
                    crate::leanh::lean_dec(v___x_6074_);
                    v_enabled_6076_ = crate::leanh::lean_ctor_get_uint8(
                        v_infoState_6075_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u32,
                    );
                    crate::leanh::lean_dec_ref(v_infoState_6075_);
                    if v_enabled_6076_ == 0 {
                        crate::leanh::lean_dec_ref(v___f_5831_);
                        v___y_6024_ = v___y_5832_;
                        v___y_6025_ = v___y_5833_;
                        v___y_6026_ = v___y_5834_;
                        v___y_6027_ = v___y_5835_;
                        v___y_6028_ = v___y_5836_;
                        v___y_6029_ = v___y_5837_;
                        v___y_6030_ = v___y_5838_;
                        v___y_6031_ = v___y_5839_;
                        state = 28;
                        continue;
                    } else {
                        v___x_6077_ = l_Lean_Elab_getResetInfoTrees___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__7___redArg(v___y_5839_);
                        v_a_6078_ = crate::leanh::lean_ctor_get(v___x_6077_, 0);
                        crate::leanh::lean_inc(v_a_6078_);
                        crate::leanh::lean_dec_ref(v___x_6077_);
                        v___f_6079_ = crate::leanh::lean_alloc_closure(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__3___boxed as *mut core::ffi::c_void, 10, 1);
                        crate::leanh::lean_closure_set(v___f_6079_, 0, v_a_6078_);
                        v___x_6080_ = l_Lean_Elab_withInfoTreeContext___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__8___redArg(v___f_6079_, v___f_5831_, v___y_5832_, v___y_5833_, v___y_5834_, v___y_5835_, v___y_5836_, v___y_5837_, v___y_5838_, v___y_5839_);
                        if crate::leanh::lean_obj_tag(v___x_6080_) == 0 {
                            crate::leanh::lean_dec_ref_known(v___x_6080_, 1);
                            v___y_6024_ = v___y_5832_;
                            v___y_6025_ = v___y_5833_;
                            v___y_6026_ = v___y_5834_;
                            v___y_6027_ = v___y_5835_;
                            v___y_6028_ = v___y_5836_;
                            v___y_6029_ = v___y_5837_;
                            v___y_6030_ = v___y_5838_;
                            v___y_6031_ = v___y_5839_;
                            state = 28;
                            continue;
                        } else {
                            crate::leanh::lean_dec(v_val_6022_);
                            crate::leanh::lean_dec_ref(v_snd_5829_);
                            crate::leanh::lean_dec(v_discharge_x3f_5828_);
                            crate::leanh::lean_dec_ref(v_simprocs_5827_);
                            crate::leanh::lean_dec_ref(v___x_5826_);
                            crate::leanh::lean_dec_ref(v___x_5822_);
                            crate::leanh::lean_dec(v_snd_5819_);
                            v_a_6081_ = crate::leanh::lean_ctor_get(v___x_6080_, 0);
                            v_isSharedCheck_6088_ =
                                (!crate::leanh::lean_is_exclusive(v___x_6080_)) as u8;
                            if v_isSharedCheck_6088_ == 0 {
                                v___x_6083_ = v___x_6080_;
                                v_isShared_6084_ = v_isSharedCheck_6088_;
                                state = 35;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_6081_);
                                crate::leanh::lean_dec(v___x_6080_);
                                v___x_6083_ = crate::leanh::lean_box(0);
                                v_isShared_6084_ = v_isSharedCheck_6088_;
                                state = 35;
                                continue;
                            }
                        }
                    }
                } else {
                    crate::leanh::lean_dec_ref(v___f_5831_);
                    crate::leanh::lean_dec_ref(v___x_5822_);
                    crate::leanh::lean_dec(v_usingArg_5818_);
                    v_lctx_6089_ = crate::leanh::lean_ctor_get(v___y_5836_, 2);
                    v___x_6090_ = l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__4___closed__13;
                    v___x_6091_ =
                        l_Lean_LocalContext_findFromUserName_x3f(v_lctx_6089_, v___x_6090_);
                    if crate::leanh::lean_obj_tag(v___x_6091_) == 1 {
                        v_val_6092_ = crate::leanh::lean_ctor_get(v___x_6091_, 0);
                        crate::leanh::lean_inc(v_val_6092_);
                        crate::leanh::lean_dec_ref_known(v___x_6091_, 1);
                        v___x_6093_ = l_Lean_LocalDecl_fvarId(v_val_6092_);
                        crate::leanh::lean_dec(v_val_6092_);
                        v___x_6094_ = lean_mk_empty_array_with_capacity(v___x_5825_);
                        v___x_6095_ = lean_array_push(v___x_6094_, v___x_6093_);
                        crate::leanh::lean_inc_ref(v_snd_5829_);
                        v___x_6096_ = l_Lean_Meta_simpGoal(
                            v_snd_5819_,
                            v___x_5826_,
                            v_simprocs_5827_,
                            v_discharge_x3f_5828_,
                            v___x_5821_,
                            v___x_6095_,
                            v_snd_5829_,
                            v___y_5836_,
                            v___y_5837_,
                            v___y_5838_,
                            v___y_5839_,
                        );
                        if crate::leanh::lean_obj_tag(v___x_6096_) == 0 {
                            v_a_6097_ = crate::leanh::lean_ctor_get(v___x_6096_, 0);
                            v_isSharedCheck_6125_ =
                                (!crate::leanh::lean_is_exclusive(v___x_6096_)) as u8;
                            if v_isSharedCheck_6125_ == 0 {
                                v___x_6099_ = v___x_6096_;
                                v_isShared_6100_ = v_isSharedCheck_6125_;
                                state = 37;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_6097_);
                                crate::leanh::lean_dec(v___x_6096_);
                                v___x_6099_ = crate::leanh::lean_box(0);
                                v_isShared_6100_ = v_isSharedCheck_6125_;
                                state = 37;
                                continue;
                            }
                        } else {
                            crate::leanh::lean_dec_ref(v_snd_5829_);
                            v_a_6126_ = crate::leanh::lean_ctor_get(v___x_6096_, 0);
                            v_isSharedCheck_6133_ =
                                (!crate::leanh::lean_is_exclusive(v___x_6096_)) as u8;
                            if v_isSharedCheck_6133_ == 0 {
                                v___x_6128_ = v___x_6096_;
                                v_isShared_6129_ = v_isSharedCheck_6133_;
                                state = 43;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_6126_);
                                crate::leanh::lean_dec(v___x_6096_);
                                v___x_6128_ = crate::leanh::lean_box(0);
                                v_isShared_6129_ = v_isSharedCheck_6133_;
                                state = 43;
                                continue;
                            }
                        }
                    } else {
                        crate::leanh::lean_dec(v___x_6091_);
                        crate::leanh::lean_dec(v_discharge_x3f_5828_);
                        crate::leanh::lean_dec_ref(v_simprocs_5827_);
                        crate::leanh::lean_dec_ref(v___x_5826_);
                        v___x_6134_ = l_Lean_MVarId_assumption(
                            v_snd_5819_,
                            v___y_5836_,
                            v___y_5837_,
                            v___y_5838_,
                            v___y_5839_,
                        );
                        if crate::leanh::lean_obj_tag(v___x_6134_) == 0 {
                            v_isSharedCheck_6141_ =
                                (!crate::leanh::lean_is_exclusive(v___x_6134_)) as u8;
                            if v_isSharedCheck_6141_ == 0 {
                                v_unused_6142_ = crate::leanh::lean_ctor_get(v___x_6134_, 0);
                                crate::leanh::lean_dec(v_unused_6142_);
                                v___x_6136_ = v___x_6134_;
                                v_isShared_6137_ = v_isSharedCheck_6141_;
                                state = 45;
                                continue;
                            } else {
                                crate::leanh::lean_dec(v___x_6134_);
                                v___x_6136_ = crate::leanh::lean_box(0);
                                v_isShared_6137_ = v_isSharedCheck_6141_;
                                state = 45;
                                continue;
                            }
                        } else {
                            crate::leanh::lean_dec_ref(v_snd_5829_);
                            v_a_6143_ = crate::leanh::lean_ctor_get(v___x_6134_, 0);
                            v_isSharedCheck_6150_ =
                                (!crate::leanh::lean_is_exclusive(v___x_6134_)) as u8;
                            if v_isSharedCheck_6150_ == 0 {
                                v___x_6145_ = v___x_6134_;
                                v_isShared_6146_ = v_isSharedCheck_6150_;
                                state = 47;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_6143_);
                                crate::leanh::lean_dec(v___x_6134_);
                                v___x_6145_ = crate::leanh::lean_box(0);
                                v_isShared_6146_ = v_isSharedCheck_6150_;
                                state = 47;
                                continue;
                            }
                        }
                    }
                }
            }
            1 => {
                v___x_5845_ = l_Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__2___redArg(v_snd_5819_, v___y_5842_, v___y_5844_);
                v_isSharedCheck_5852_ = (!crate::leanh::lean_is_exclusive(v___x_5845_)) as u8;
                if v_isSharedCheck_5852_ == 0 {
                    v_unused_5853_ = crate::leanh::lean_ctor_get(v___x_5845_, 0);
                    crate::leanh::lean_dec(v_unused_5853_);
                    v___x_5847_ = v___x_5845_;
                    v_isShared_5848_ = v_isSharedCheck_5852_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_dec(v___x_5845_);
                    v___x_5847_ = crate::leanh::lean_box(0);
                    v_isShared_5848_ = v_isSharedCheck_5852_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                if v_isShared_5848_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5847_, 0, v___y_5843_);
                    v___x_5850_ = v___x_5847_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_5851_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5851_, 0, v___y_5843_);
                    v___x_5850_ = v_reuseFailAlloc_5851_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_5850_;
            }
            4 => {
                v___x_5871_ = l_Lean_Core_mkFreshUserName(v___y_5864_, v___y_5859_, v___y_5869_);
                if crate::leanh::lean_obj_tag(v___x_5871_) == 0 {
                    v_a_5872_ = crate::leanh::lean_ctor_get(v___x_5871_, 0);
                    crate::leanh::lean_inc_n(v_a_5872_, 2);
                    crate::leanh::lean_dec_ref_known(v___x_5871_, 1);
                    v___x_5873_ = l_Lean_MVarId_rename(
                        v___y_5862_,
                        v___y_5870_,
                        v_a_5872_,
                        v___y_5863_,
                        v___y_5868_,
                        v___y_5859_,
                        v___y_5869_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_5873_) == 0 {
                        v_a_5874_ = crate::leanh::lean_ctor_get(v___x_5873_, 0);
                        crate::leanh::lean_inc_n(v_a_5874_, 2);
                        crate::leanh::lean_dec_ref_known(v___x_5873_, 1);
                        v___x_5875_ = crate::leanh::lean_box((v___x_5820_) as usize);
                        v___x_5876_ = crate::leanh::lean_box((v___x_5821_) as usize);
                        v___x_5877_ = crate::leanh::lean_box((v_useReducible_5823_) as usize);
                        v___x_5878_ = crate::leanh::lean_box((v___x_5824_) as usize);
                        v___f_5879_ = crate::leanh::lean_alloc_closure(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__2___boxed as *mut core::ffi::c_void, 19, 10);
                        crate::leanh::lean_closure_set(v___f_5879_, 0, v_a_5874_);
                        crate::leanh::lean_closure_set(v___f_5879_, 1, v_a_5872_);
                        crate::leanh::lean_closure_set(v___f_5879_, 2, v___x_5875_);
                        crate::leanh::lean_closure_set(v___f_5879_, 3, v___x_5876_);
                        crate::leanh::lean_closure_set(v___f_5879_, 4, v___y_5855_);
                        crate::leanh::lean_closure_set(v___f_5879_, 5, v___y_5856_);
                        crate::leanh::lean_closure_set(v___f_5879_, 6, v___x_5822_);
                        crate::leanh::lean_closure_set(v___f_5879_, 7, v___y_5857_);
                        crate::leanh::lean_closure_set(v___f_5879_, 8, v___x_5877_);
                        crate::leanh::lean_closure_set(v___f_5879_, 9, v___x_5878_);
                        v___x_5880_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__5___redArg(v_a_5874_, v___f_5879_, v___y_5866_, v___y_5865_, v___y_5858_, v___y_5861_, v___y_5863_, v___y_5868_, v___y_5859_, v___y_5869_);
                        if crate::leanh::lean_obj_tag(v___x_5880_) == 0 {
                            crate::leanh::lean_dec_ref_known(v___x_5880_, 1);
                            v___y_5842_ = v___y_5860_;
                            v___y_5843_ = v___y_5867_;
                            v___y_5844_ = v___y_5868_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_dec_ref(v___y_5867_);
                            crate::leanh::lean_dec_ref(v___y_5860_);
                            crate::leanh::lean_dec(v_snd_5819_);
                            v_a_5881_ = crate::leanh::lean_ctor_get(v___x_5880_, 0);
                            v_isSharedCheck_5888_ =
                                (!crate::leanh::lean_is_exclusive(v___x_5880_)) as u8;
                            if v_isSharedCheck_5888_ == 0 {
                                v___x_5883_ = v___x_5880_;
                                v_isShared_5884_ = v_isSharedCheck_5888_;
                                state = 5;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_5881_);
                                crate::leanh::lean_dec(v___x_5880_);
                                v___x_5883_ = crate::leanh::lean_box(0);
                                v_isShared_5884_ = v_isSharedCheck_5888_;
                                state = 5;
                                continue;
                            }
                        }
                    } else {
                        crate::leanh::lean_dec(v_a_5872_);
                        crate::leanh::lean_dec_ref(v___y_5867_);
                        crate::leanh::lean_dec_ref(v___y_5860_);
                        crate::leanh::lean_dec(v___y_5857_);
                        crate::leanh::lean_dec(v___y_5856_);
                        crate::leanh::lean_dec_ref(v___y_5855_);
                        crate::leanh::lean_dec_ref(v___x_5822_);
                        crate::leanh::lean_dec(v_snd_5819_);
                        v_a_5889_ = crate::leanh::lean_ctor_get(v___x_5873_, 0);
                        v_isSharedCheck_5896_ =
                            (!crate::leanh::lean_is_exclusive(v___x_5873_)) as u8;
                        if v_isSharedCheck_5896_ == 0 {
                            v___x_5891_ = v___x_5873_;
                            v_isShared_5892_ = v_isSharedCheck_5896_;
                            state = 7;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_5889_);
                            crate::leanh::lean_dec(v___x_5873_);
                            v___x_5891_ = crate::leanh::lean_box(0);
                            v_isShared_5892_ = v_isSharedCheck_5896_;
                            state = 7;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec(v___y_5870_);
                    crate::leanh::lean_dec_ref(v___y_5867_);
                    crate::leanh::lean_dec(v___y_5862_);
                    crate::leanh::lean_dec_ref(v___y_5860_);
                    crate::leanh::lean_dec(v___y_5857_);
                    crate::leanh::lean_dec(v___y_5856_);
                    crate::leanh::lean_dec_ref(v___y_5855_);
                    crate::leanh::lean_dec_ref(v___x_5822_);
                    crate::leanh::lean_dec(v_snd_5819_);
                    v_a_5897_ = crate::leanh::lean_ctor_get(v___x_5871_, 0);
                    v_isSharedCheck_5904_ = (!crate::leanh::lean_is_exclusive(v___x_5871_)) as u8;
                    if v_isSharedCheck_5904_ == 0 {
                        v___x_5899_ = v___x_5871_;
                        v_isShared_5900_ = v_isSharedCheck_5904_;
                        state = 9;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_5897_);
                        crate::leanh::lean_dec(v___x_5871_);
                        v___x_5899_ = crate::leanh::lean_box(0);
                        v_isShared_5900_ = v_isSharedCheck_5904_;
                        state = 9;
                        continue;
                    }
                }
            }
            5 => {
                if v_isShared_5884_ == 0 {
                    v___x_5886_ = v___x_5883_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_5887_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5887_, 0, v_a_5881_);
                    v___x_5886_ = v_reuseFailAlloc_5887_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_5886_;
            }
            7 => {
                if v_isShared_5892_ == 0 {
                    v___x_5894_ = v___x_5891_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_5895_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5895_, 0, v_a_5889_);
                    v___x_5894_ = v_reuseFailAlloc_5895_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_5894_;
            }
            9 => {
                if v_isShared_5900_ == 0 {
                    v___x_5902_ = v___x_5899_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_5903_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5903_, 0, v_a_5897_);
                    v___x_5902_ = v_reuseFailAlloc_5903_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_5902_;
            }
            11 => {
                crate::leanh::lean_inc(v_snd_5819_);
                v___x_5919_ = l_Lean_MVarId_getType(
                    v_snd_5819_,
                    v___y_5915_,
                    v___y_5916_,
                    v___y_5917_,
                    v___y_5918_,
                );
                if crate::leanh::lean_obj_tag(v___x_5919_) == 0 {
                    v_a_5920_ = crate::leanh::lean_ctor_get(v___x_5919_, 0);
                    crate::leanh::lean_inc(v_a_5920_);
                    crate::leanh::lean_dec_ref_known(v___x_5919_, 1);
                    crate::leanh::lean_inc(v_snd_5819_);
                    v___x_5921_ = l_Lean_MVarId_getTag(
                        v_snd_5819_,
                        v___y_5915_,
                        v___y_5916_,
                        v___y_5917_,
                        v___y_5918_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_5921_) == 0 {
                        v_a_5922_ = crate::leanh::lean_ctor_get(v___x_5921_, 0);
                        crate::leanh::lean_inc(v_a_5922_);
                        crate::leanh::lean_dec_ref_known(v___x_5921_, 1);
                        v___x_5923_ = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(
                            v_a_5920_,
                            v_a_5922_,
                            v___y_5915_,
                            v___y_5916_,
                            v___y_5917_,
                            v___y_5918_,
                        );
                        if crate::leanh::lean_obj_tag(v___x_5923_) == 0 {
                            v_a_5924_ = crate::leanh::lean_ctor_get(v___x_5923_, 0);
                            crate::leanh::lean_inc(v_a_5924_);
                            crate::leanh::lean_dec_ref_known(v___x_5923_, 1);
                            v___x_5925_ = l_Lean_Expr_mvarId_x21(v_a_5924_);
                            v___x_5926_ = l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__4___closed__1;
                            crate::leanh::lean_inc_ref(v___y_5909_);
                            v___x_5927_ = l_Lean_MVarId_note(
                                v___x_5925_,
                                v___x_5926_,
                                v___y_5909_,
                                v___y_5910_,
                                v___y_5915_,
                                v___y_5916_,
                                v___y_5917_,
                                v___y_5918_,
                            );
                            if crate::leanh::lean_obj_tag(v___x_5927_) == 0 {
                                v_a_5928_ = crate::leanh::lean_ctor_get(v___x_5927_, 0);
                                crate::leanh::lean_inc(v_a_5928_);
                                crate::leanh::lean_dec_ref_known(v___x_5927_, 1);
                                v_fst_5929_ = crate::leanh::lean_ctor_get(v_a_5928_, 0);
                                v_snd_5930_ = crate::leanh::lean_ctor_get(v_a_5928_, 1);
                                v_isSharedCheck_5989_ =
                                    (!crate::leanh::lean_is_exclusive(v_a_5928_)) as u8;
                                if v_isSharedCheck_5989_ == 0 {
                                    v___x_5932_ = v_a_5928_;
                                    v_isShared_5933_ = v_isSharedCheck_5989_;
                                    state = 12;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_snd_5930_);
                                    crate::leanh::lean_inc(v_fst_5929_);
                                    crate::leanh::lean_dec(v_a_5928_);
                                    v___x_5932_ = crate::leanh::lean_box(0);
                                    v_isShared_5933_ = v_isSharedCheck_5989_;
                                    state = 12;
                                    continue;
                                }
                            } else {
                                crate::leanh::lean_dec(v_a_5924_);
                                crate::leanh::lean_dec_ref(v___y_5909_);
                                crate::leanh::lean_dec(v___y_5908_);
                                crate::leanh::lean_dec(v___y_5907_);
                                crate::leanh::lean_dec_ref(v___y_5906_);
                                crate::leanh::lean_dec_ref(v_snd_5829_);
                                crate::leanh::lean_dec(v_discharge_x3f_5828_);
                                crate::leanh::lean_dec_ref(v_simprocs_5827_);
                                crate::leanh::lean_dec_ref(v___x_5826_);
                                crate::leanh::lean_dec_ref(v___x_5822_);
                                crate::leanh::lean_dec(v_snd_5819_);
                                v_a_5990_ = crate::leanh::lean_ctor_get(v___x_5927_, 0);
                                v_isSharedCheck_5997_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_5927_)) as u8;
                                if v_isSharedCheck_5997_ == 0 {
                                    v___x_5992_ = v___x_5927_;
                                    v_isShared_5993_ = v_isSharedCheck_5997_;
                                    state = 20;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_a_5990_);
                                    crate::leanh::lean_dec(v___x_5927_);
                                    v___x_5992_ = crate::leanh::lean_box(0);
                                    v_isShared_5993_ = v_isSharedCheck_5997_;
                                    state = 20;
                                    continue;
                                }
                            }
                        } else {
                            crate::leanh::lean_dec(v___y_5910_);
                            crate::leanh::lean_dec_ref(v___y_5909_);
                            crate::leanh::lean_dec(v___y_5908_);
                            crate::leanh::lean_dec(v___y_5907_);
                            crate::leanh::lean_dec_ref(v___y_5906_);
                            crate::leanh::lean_dec_ref(v_snd_5829_);
                            crate::leanh::lean_dec(v_discharge_x3f_5828_);
                            crate::leanh::lean_dec_ref(v_simprocs_5827_);
                            crate::leanh::lean_dec_ref(v___x_5826_);
                            crate::leanh::lean_dec_ref(v___x_5822_);
                            crate::leanh::lean_dec(v_snd_5819_);
                            v_a_5998_ = crate::leanh::lean_ctor_get(v___x_5923_, 0);
                            v_isSharedCheck_6005_ =
                                (!crate::leanh::lean_is_exclusive(v___x_5923_)) as u8;
                            if v_isSharedCheck_6005_ == 0 {
                                v___x_6000_ = v___x_5923_;
                                v_isShared_6001_ = v_isSharedCheck_6005_;
                                state = 22;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_5998_);
                                crate::leanh::lean_dec(v___x_5923_);
                                v___x_6000_ = crate::leanh::lean_box(0);
                                v_isShared_6001_ = v_isSharedCheck_6005_;
                                state = 22;
                                continue;
                            }
                        }
                    } else {
                        crate::leanh::lean_dec(v_a_5920_);
                        crate::leanh::lean_dec(v___y_5910_);
                        crate::leanh::lean_dec_ref(v___y_5909_);
                        crate::leanh::lean_dec(v___y_5908_);
                        crate::leanh::lean_dec(v___y_5907_);
                        crate::leanh::lean_dec_ref(v___y_5906_);
                        crate::leanh::lean_dec_ref(v_snd_5829_);
                        crate::leanh::lean_dec(v_discharge_x3f_5828_);
                        crate::leanh::lean_dec_ref(v_simprocs_5827_);
                        crate::leanh::lean_dec_ref(v___x_5826_);
                        crate::leanh::lean_dec_ref(v___x_5822_);
                        crate::leanh::lean_dec(v_snd_5819_);
                        v_a_6006_ = crate::leanh::lean_ctor_get(v___x_5921_, 0);
                        v_isSharedCheck_6013_ =
                            (!crate::leanh::lean_is_exclusive(v___x_5921_)) as u8;
                        if v_isSharedCheck_6013_ == 0 {
                            v___x_6008_ = v___x_5921_;
                            v_isShared_6009_ = v_isSharedCheck_6013_;
                            state = 24;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_6006_);
                            crate::leanh::lean_dec(v___x_5921_);
                            v___x_6008_ = crate::leanh::lean_box(0);
                            v_isShared_6009_ = v_isSharedCheck_6013_;
                            state = 24;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec(v___y_5910_);
                    crate::leanh::lean_dec_ref(v___y_5909_);
                    crate::leanh::lean_dec(v___y_5908_);
                    crate::leanh::lean_dec(v___y_5907_);
                    crate::leanh::lean_dec_ref(v___y_5906_);
                    crate::leanh::lean_dec_ref(v_snd_5829_);
                    crate::leanh::lean_dec(v_discharge_x3f_5828_);
                    crate::leanh::lean_dec_ref(v_simprocs_5827_);
                    crate::leanh::lean_dec_ref(v___x_5826_);
                    crate::leanh::lean_dec_ref(v___x_5822_);
                    crate::leanh::lean_dec(v_snd_5819_);
                    v_a_6014_ = crate::leanh::lean_ctor_get(v___x_5919_, 0);
                    v_isSharedCheck_6021_ = (!crate::leanh::lean_is_exclusive(v___x_5919_)) as u8;
                    if v_isSharedCheck_6021_ == 0 {
                        v___x_6016_ = v___x_5919_;
                        v_isShared_6017_ = v_isSharedCheck_6021_;
                        state = 26;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_6014_);
                        crate::leanh::lean_dec(v___x_5919_);
                        v___x_6016_ = crate::leanh::lean_box(0);
                        v_isShared_6017_ = v_isSharedCheck_6021_;
                        state = 26;
                        continue;
                    }
                }
            }
            12 => {
                v___x_5934_ = lean_mk_empty_array_with_capacity(v___x_5825_);
                crate::leanh::lean_inc(v_fst_5929_);
                v___x_5935_ = lean_array_push(v___x_5934_, v_fst_5929_);
                v___x_5936_ = l_Lean_Meta_simpGoal(
                    v_snd_5930_,
                    v___x_5826_,
                    v_simprocs_5827_,
                    v_discharge_x3f_5828_,
                    v___x_5821_,
                    v___x_5935_,
                    v_snd_5829_,
                    v___y_5915_,
                    v___y_5916_,
                    v___y_5917_,
                    v___y_5918_,
                );
                if crate::leanh::lean_obj_tag(v___x_5936_) == 0 {
                    v_a_5937_ = crate::leanh::lean_ctor_get(v___x_5936_, 0);
                    crate::leanh::lean_inc(v_a_5937_);
                    crate::leanh::lean_dec_ref_known(v___x_5936_, 1);
                    v_fst_5938_ = crate::leanh::lean_ctor_get(v_a_5937_, 0);
                    if crate::leanh::lean_obj_tag(v_fst_5938_) == 0 {
                        crate::leanh::lean_dec(v_fst_5929_);
                        crate::leanh::lean_dec(v___y_5908_);
                        crate::leanh::lean_dec(v___y_5907_);
                        crate::leanh::lean_dec_ref(v___y_5906_);
                        crate::leanh::lean_dec_ref(v___x_5822_);
                        v_snd_5939_ = crate::leanh::lean_ctor_get(v_a_5937_, 1);
                        v_isSharedCheck_5972_ = (!crate::leanh::lean_is_exclusive(v_a_5937_)) as u8;
                        if v_isSharedCheck_5972_ == 0 {
                            v_unused_5973_ = crate::leanh::lean_ctor_get(v_a_5937_, 0);
                            crate::leanh::lean_dec(v_unused_5973_);
                            v___x_5941_ = v_a_5937_;
                            v_isShared_5942_ = v_isSharedCheck_5972_;
                            state = 13;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_snd_5939_);
                            crate::leanh::lean_dec(v_a_5937_);
                            v___x_5941_ = crate::leanh::lean_box(0);
                            v_isShared_5942_ = v_isSharedCheck_5972_;
                            state = 13;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_del_object(v___x_5932_);
                        crate::leanh::lean_dec_ref(v___y_5909_);
                        v_val_5974_ = crate::leanh::lean_ctor_get(v_fst_5938_, 0);
                        crate::leanh::lean_inc(v_val_5974_);
                        v_snd_5975_ = crate::leanh::lean_ctor_get(v_a_5937_, 1);
                        crate::leanh::lean_inc(v_snd_5975_);
                        crate::leanh::lean_dec(v_a_5937_);
                        v_fst_5976_ = crate::leanh::lean_ctor_get(v_val_5974_, 0);
                        crate::leanh::lean_inc(v_fst_5976_);
                        v_snd_5977_ = crate::leanh::lean_ctor_get(v_val_5974_, 1);
                        crate::leanh::lean_inc(v_snd_5977_);
                        crate::leanh::lean_dec(v_val_5974_);
                        v___x_5978_ = lean_array_get_size(v_fst_5976_);
                        v___x_5979_ = lean_nat_dec_lt(v___x_5830_, v___x_5978_);
                        if v___x_5979_ == 0 {
                            crate::leanh::lean_dec(v_fst_5976_);
                            v___y_5855_ = v___y_5906_;
                            v___y_5856_ = v___y_5907_;
                            v___y_5857_ = v___y_5908_;
                            v___y_5858_ = v___y_5913_;
                            v___y_5859_ = v___y_5917_;
                            v___y_5860_ = v_a_5924_;
                            v___y_5861_ = v___y_5914_;
                            v___y_5862_ = v_snd_5977_;
                            v___y_5863_ = v___y_5915_;
                            v___y_5864_ = v___x_5926_;
                            v___y_5865_ = v___y_5912_;
                            v___y_5866_ = v___y_5911_;
                            v___y_5867_ = v_snd_5975_;
                            v___y_5868_ = v___y_5916_;
                            v___y_5869_ = v___y_5918_;
                            v___y_5870_ = v_fst_5929_;
                            state = 4;
                            continue;
                        } else {
                            crate::leanh::lean_dec(v_fst_5929_);
                            v___x_5980_ = lean_array_fget(v_fst_5976_, v___x_5830_);
                            crate::leanh::lean_dec(v_fst_5976_);
                            v___y_5855_ = v___y_5906_;
                            v___y_5856_ = v___y_5907_;
                            v___y_5857_ = v___y_5908_;
                            v___y_5858_ = v___y_5913_;
                            v___y_5859_ = v___y_5917_;
                            v___y_5860_ = v_a_5924_;
                            v___y_5861_ = v___y_5914_;
                            v___y_5862_ = v_snd_5977_;
                            v___y_5863_ = v___y_5915_;
                            v___y_5864_ = v___x_5926_;
                            v___y_5865_ = v___y_5912_;
                            v___y_5866_ = v___y_5911_;
                            v___y_5867_ = v_snd_5975_;
                            v___y_5868_ = v___y_5916_;
                            v___y_5869_ = v___y_5918_;
                            v___y_5870_ = v___x_5980_;
                            state = 4;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_5932_);
                    crate::leanh::lean_dec(v_fst_5929_);
                    crate::leanh::lean_dec(v_a_5924_);
                    crate::leanh::lean_dec_ref(v___y_5909_);
                    crate::leanh::lean_dec(v___y_5908_);
                    crate::leanh::lean_dec(v___y_5907_);
                    crate::leanh::lean_dec_ref(v___y_5906_);
                    crate::leanh::lean_dec_ref(v___x_5822_);
                    crate::leanh::lean_dec(v_snd_5819_);
                    v_a_5981_ = crate::leanh::lean_ctor_get(v___x_5936_, 0);
                    v_isSharedCheck_5988_ = (!crate::leanh::lean_is_exclusive(v___x_5936_)) as u8;
                    if v_isSharedCheck_5988_ == 0 {
                        v___x_5983_ = v___x_5936_;
                        v_isShared_5984_ = v_isSharedCheck_5988_;
                        state = 18;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_5981_);
                        crate::leanh::lean_dec(v___x_5936_);
                        v___x_5983_ = crate::leanh::lean_box(0);
                        v_isShared_5984_ = v_isSharedCheck_5988_;
                        state = 18;
                        continue;
                    }
                }
            }
            13 => {
                v___x_5943_ = l_Lean_Linter_getLinterOptions___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__3(v___y_5911_, v___y_5912_, v___y_5913_, v___y_5914_, v___y_5915_, v___y_5916_, v___y_5917_, v___y_5918_);
                v_a_5944_ = crate::leanh::lean_ctor_get(v___x_5943_, 0);
                crate::leanh::lean_inc(v_a_5944_);
                crate::leanh::lean_dec_ref(v___x_5943_);
                v___x_5945_ = l_Lean_Elab_Tactic_Simpa_getLinterUnnecessarySimpa(v_a_5944_);
                crate::leanh::lean_dec(v_a_5944_);
                if v___x_5945_ == 0 {
                    crate::leanh::lean_del_object(v___x_5941_);
                    crate::leanh::lean_del_object(v___x_5932_);
                    crate::leanh::lean_dec_ref(v___y_5909_);
                    v___y_5842_ = v_a_5924_;
                    v___y_5843_ = v_snd_5939_;
                    v___y_5844_ = v___y_5916_;
                    state = 1;
                    continue;
                } else {
                    if crate::leanh::lean_obj_tag(v___y_5909_) == 1 {
                        v_fvarId_5946_ = crate::leanh::lean_ctor_get(v___y_5909_, 0);
                        v_lctx_5947_ = crate::leanh::lean_ctor_get(v___y_5915_, 2);
                        crate::leanh::lean_inc(v_fvarId_5946_);
                        crate::leanh::lean_inc_ref(v_lctx_5947_);
                        v___x_5948_ = l_Lean_LocalContext_getRoundtrippingUserName_x3f(
                            v_lctx_5947_,
                            v_fvarId_5946_,
                        );
                        if crate::leanh::lean_obj_tag(v___x_5948_) == 0 {
                            crate::leanh::lean_dec_ref_known(v___y_5909_, 1);
                            crate::leanh::lean_del_object(v___x_5941_);
                            crate::leanh::lean_del_object(v___x_5932_);
                            v___y_5842_ = v_a_5924_;
                            v___y_5843_ = v_snd_5939_;
                            v___y_5844_ = v___y_5916_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_dec_ref_known(v___x_5948_, 1);
                            if v___x_5824_ == 0 {
                                crate::leanh::lean_dec_ref_known(v___y_5909_, 1);
                                crate::leanh::lean_del_object(v___x_5941_);
                                crate::leanh::lean_del_object(v___x_5932_);
                                v___y_5842_ = v_a_5924_;
                                v___y_5843_ = v_snd_5939_;
                                v___y_5844_ = v___y_5916_;
                                state = 1;
                                continue;
                            } else {
                                v_ref_5949_ = crate::leanh::lean_ctor_get(v___y_5917_, 5);
                                v___x_5950_ = l_linter_unnecessarySimpa;
                                v___x_5951_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__4___closed__3), core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__4___closed__3_once), _init_l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__4___closed__3);
                                v___x_5952_ = l_Lean_MessageData_ofExpr(v___y_5909_);
                                crate::leanh::lean_inc_ref(v___x_5952_);
                                if v_isShared_5942_ == 0 {
                                    crate::leanh::lean_ctor_set_tag(v___x_5941_, 7);
                                    crate::leanh::lean_ctor_set(v___x_5941_, 1, v___x_5952_);
                                    crate::leanh::lean_ctor_set(v___x_5941_, 0, v___x_5951_);
                                    v___x_5954_ = v___x_5941_;
                                    state = 14;
                                    continue;
                                } else {
                                    v_reuseFailAlloc_5971_ =
                                        crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                                    crate::leanh::lean_ctor_set(
                                        v_reuseFailAlloc_5971_,
                                        0,
                                        v___x_5951_,
                                    );
                                    crate::leanh::lean_ctor_set(
                                        v_reuseFailAlloc_5971_,
                                        1,
                                        v___x_5952_,
                                    );
                                    v___x_5954_ = v_reuseFailAlloc_5971_;
                                    state = 14;
                                    continue;
                                }
                            }
                        }
                    } else {
                        crate::leanh::lean_del_object(v___x_5941_);
                        crate::leanh::lean_del_object(v___x_5932_);
                        crate::leanh::lean_dec_ref(v___y_5909_);
                        v___y_5842_ = v_a_5924_;
                        v___y_5843_ = v_snd_5939_;
                        v___y_5844_ = v___y_5916_;
                        state = 1;
                        continue;
                    }
                }
            }
            14 => {
                v___x_5955_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__4___closed__5), core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__4___closed__5_once), _init_l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__4___closed__5);
                if v_isShared_5933_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_5932_, 7);
                    crate::leanh::lean_ctor_set(v___x_5932_, 1, v___x_5955_);
                    crate::leanh::lean_ctor_set(v___x_5932_, 0, v___x_5954_);
                    v___x_5957_ = v___x_5932_;
                    state = 15;
                    continue;
                } else {
                    v_reuseFailAlloc_5970_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5970_, 0, v___x_5954_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5970_, 1, v___x_5955_);
                    v___x_5957_ = v_reuseFailAlloc_5970_;
                    state = 15;
                    continue;
                }
            }
            15 => {
                v___x_5958_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_5958_, 0, v___x_5957_);
                crate::leanh::lean_ctor_set(v___x_5958_, 1, v___x_5952_);
                v___x_5959_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__4___closed__7), core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__4___closed__7_once), _init_l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__4___closed__7);
                v___x_5960_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_5960_, 0, v___x_5958_);
                crate::leanh::lean_ctor_set(v___x_5960_, 1, v___x_5959_);
                v___x_5961_ = l_Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4(v___x_5950_, v_ref_5949_, v___x_5960_, v___y_5911_, v___y_5912_, v___y_5913_, v___y_5914_, v___y_5915_, v___y_5916_, v___y_5917_, v___y_5918_);
                if crate::leanh::lean_obj_tag(v___x_5961_) == 0 {
                    crate::leanh::lean_dec_ref_known(v___x_5961_, 1);
                    v___y_5842_ = v_a_5924_;
                    v___y_5843_ = v_snd_5939_;
                    v___y_5844_ = v___y_5916_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_dec(v_snd_5939_);
                    crate::leanh::lean_dec(v_a_5924_);
                    crate::leanh::lean_dec(v_snd_5819_);
                    v_a_5962_ = crate::leanh::lean_ctor_get(v___x_5961_, 0);
                    v_isSharedCheck_5969_ = (!crate::leanh::lean_is_exclusive(v___x_5961_)) as u8;
                    if v_isSharedCheck_5969_ == 0 {
                        v___x_5964_ = v___x_5961_;
                        v_isShared_5965_ = v_isSharedCheck_5969_;
                        state = 16;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_5962_);
                        crate::leanh::lean_dec(v___x_5961_);
                        v___x_5964_ = crate::leanh::lean_box(0);
                        v_isShared_5965_ = v_isSharedCheck_5969_;
                        state = 16;
                        continue;
                    }
                }
            }
            16 => {
                if v_isShared_5965_ == 0 {
                    v___x_5967_ = v___x_5964_;
                    state = 17;
                    continue;
                } else {
                    v_reuseFailAlloc_5968_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5968_, 0, v_a_5962_);
                    v___x_5967_ = v_reuseFailAlloc_5968_;
                    state = 17;
                    continue;
                }
            }
            17 => {
                return v___x_5967_;
            }
            18 => {
                if v_isShared_5984_ == 0 {
                    v___x_5986_ = v___x_5983_;
                    state = 19;
                    continue;
                } else {
                    v_reuseFailAlloc_5987_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5987_, 0, v_a_5981_);
                    v___x_5986_ = v_reuseFailAlloc_5987_;
                    state = 19;
                    continue;
                }
            }
            19 => {
                return v___x_5986_;
            }
            20 => {
                if v_isShared_5993_ == 0 {
                    v___x_5995_ = v___x_5992_;
                    state = 21;
                    continue;
                } else {
                    v_reuseFailAlloc_5996_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5996_, 0, v_a_5990_);
                    v___x_5995_ = v_reuseFailAlloc_5996_;
                    state = 21;
                    continue;
                }
            }
            21 => {
                return v___x_5995_;
            }
            22 => {
                if v_isShared_6001_ == 0 {
                    v___x_6003_ = v___x_6000_;
                    state = 23;
                    continue;
                } else {
                    v_reuseFailAlloc_6004_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6004_, 0, v_a_5998_);
                    v___x_6003_ = v_reuseFailAlloc_6004_;
                    state = 23;
                    continue;
                }
            }
            23 => {
                return v___x_6003_;
            }
            24 => {
                if v_isShared_6009_ == 0 {
                    v___x_6011_ = v___x_6008_;
                    state = 25;
                    continue;
                } else {
                    v_reuseFailAlloc_6012_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6012_, 0, v_a_6006_);
                    v___x_6011_ = v_reuseFailAlloc_6012_;
                    state = 25;
                    continue;
                }
            }
            25 => {
                return v___x_6011_;
            }
            26 => {
                if v_isShared_6017_ == 0 {
                    v___x_6019_ = v___x_6016_;
                    state = 27;
                    continue;
                } else {
                    v_reuseFailAlloc_6020_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6020_, 0, v_a_6014_);
                    v___x_6019_ = v_reuseFailAlloc_6020_;
                    state = 27;
                    continue;
                }
            }
            27 => {
                return v___x_6019_;
            }
            28 => {
                v___x_6032_ = lean_st_ref_get(v___y_6029_);
                v___x_6033_ = crate::leanh::lean_box(0);
                v___x_6034_ = l_Lean_Elab_Tactic_elabTerm(
                    v_val_6022_,
                    v___x_6033_,
                    v___x_5820_,
                    v___y_6024_,
                    v___y_6025_,
                    v___y_6026_,
                    v___y_6027_,
                    v___y_6028_,
                    v___y_6029_,
                    v___y_6030_,
                    v___y_6031_,
                );
                if crate::leanh::lean_obj_tag(v___x_6034_) == 0 {
                    v_a_6035_ = crate::leanh::lean_ctor_get(v___x_6034_, 0);
                    crate::leanh::lean_inc_n(v_a_6035_, 2);
                    crate::leanh::lean_dec_ref_known(v___x_6034_, 1);
                    v___x_6036_ = l_Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1(v_snd_5819_, v_a_6035_, v___y_6024_, v___y_6025_, v___y_6026_, v___y_6027_, v___y_6028_, v___y_6029_, v___y_6030_, v___y_6031_);
                    if crate::leanh::lean_obj_tag(v___x_6036_) == 0 {
                        v_mctx_6037_ = crate::leanh::lean_ctor_get(v___x_6032_, 0);
                        crate::leanh::lean_inc_ref(v_mctx_6037_);
                        crate::leanh::lean_dec(v___x_6032_);
                        v_a_6038_ = crate::leanh::lean_ctor_get(v___x_6036_, 0);
                        crate::leanh::lean_inc(v_a_6038_);
                        crate::leanh::lean_dec_ref_known(v___x_6036_, 1);
                        v___x_6039_ = (crate::leanh::lean_unbox(v_a_6038_) as u8);
                        crate::leanh::lean_dec(v_a_6038_);
                        if v___x_6039_ == 0 {
                            crate::leanh::lean_dec_ref(v_mctx_6037_);
                            crate::leanh::lean_dec_ref(v_snd_5829_);
                            crate::leanh::lean_dec(v_discharge_x3f_5828_);
                            crate::leanh::lean_dec_ref(v_simprocs_5827_);
                            crate::leanh::lean_dec_ref(v___x_5826_);
                            crate::leanh::lean_dec_ref(v___x_5822_);
                            v___x_6040_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__4___closed__9), core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__4___closed__9_once), _init_l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__4___closed__9);
                            v___x_6041_ = l_Lean_indentExpr(v_a_6035_);
                            v___x_6042_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_6042_, 0, v___x_6040_);
                            crate::leanh::lean_ctor_set(v___x_6042_, 1, v___x_6041_);
                            v___x_6043_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__4___closed__11), core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__4___closed__11_once), _init_l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__4___closed__11);
                            v___x_6044_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_6044_, 0, v___x_6042_);
                            crate::leanh::lean_ctor_set(v___x_6044_, 1, v___x_6043_);
                            v___x_6045_ = l_Lean_Expr_mvar___override(v_snd_5819_);
                            v___x_6046_ = l_Lean_MessageData_ofExpr(v___x_6045_);
                            v___x_6047_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_6047_, 0, v___x_6044_);
                            crate::leanh::lean_ctor_set(v___x_6047_, 1, v___x_6046_);
                            v___x_6048_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__6___redArg(v___x_6047_, v___y_6028_, v___y_6029_, v___y_6030_, v___y_6031_);
                            v_a_6049_ = crate::leanh::lean_ctor_get(v___x_6048_, 0);
                            v_isSharedCheck_6056_ =
                                (!crate::leanh::lean_is_exclusive(v___x_6048_)) as u8;
                            if v_isSharedCheck_6056_ == 0 {
                                v___x_6051_ = v___x_6048_;
                                v_isShared_6052_ = v_isSharedCheck_6056_;
                                state = 29;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_6049_);
                                crate::leanh::lean_dec(v___x_6048_);
                                v___x_6051_ = crate::leanh::lean_box(0);
                                v_isShared_6052_ = v_isSharedCheck_6056_;
                                state = 29;
                                continue;
                            }
                        } else {
                            v_mvarCounter_6057_ = crate::leanh::lean_ctor_get(v_mctx_6037_, 3);
                            crate::leanh::lean_inc(v_mvarCounter_6057_);
                            crate::leanh::lean_dec_ref(v_mctx_6037_);
                            crate::leanh::lean_inc(v_a_6035_);
                            v___y_5906_ = v_a_6035_;
                            v___y_5907_ = v_mvarCounter_6057_;
                            v___y_5908_ = v___x_6033_;
                            v___y_5909_ = v_a_6035_;
                            v___y_5910_ = v___x_6033_;
                            v___y_5911_ = v___y_6024_;
                            v___y_5912_ = v___y_6025_;
                            v___y_5913_ = v___y_6026_;
                            v___y_5914_ = v___y_6027_;
                            v___y_5915_ = v___y_6028_;
                            v___y_5916_ = v___y_6029_;
                            v___y_5917_ = v___y_6030_;
                            v___y_5918_ = v___y_6031_;
                            state = 11;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec(v_a_6035_);
                        crate::leanh::lean_dec(v___x_6032_);
                        crate::leanh::lean_dec_ref(v_snd_5829_);
                        crate::leanh::lean_dec(v_discharge_x3f_5828_);
                        crate::leanh::lean_dec_ref(v_simprocs_5827_);
                        crate::leanh::lean_dec_ref(v___x_5826_);
                        crate::leanh::lean_dec_ref(v___x_5822_);
                        crate::leanh::lean_dec(v_snd_5819_);
                        v_a_6058_ = crate::leanh::lean_ctor_get(v___x_6036_, 0);
                        v_isSharedCheck_6065_ =
                            (!crate::leanh::lean_is_exclusive(v___x_6036_)) as u8;
                        if v_isSharedCheck_6065_ == 0 {
                            v___x_6060_ = v___x_6036_;
                            v_isShared_6061_ = v_isSharedCheck_6065_;
                            state = 31;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_6058_);
                            crate::leanh::lean_dec(v___x_6036_);
                            v___x_6060_ = crate::leanh::lean_box(0);
                            v_isShared_6061_ = v_isSharedCheck_6065_;
                            state = 31;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec(v___x_6032_);
                    crate::leanh::lean_dec_ref(v_snd_5829_);
                    crate::leanh::lean_dec(v_discharge_x3f_5828_);
                    crate::leanh::lean_dec_ref(v_simprocs_5827_);
                    crate::leanh::lean_dec_ref(v___x_5826_);
                    crate::leanh::lean_dec_ref(v___x_5822_);
                    crate::leanh::lean_dec(v_snd_5819_);
                    v_a_6066_ = crate::leanh::lean_ctor_get(v___x_6034_, 0);
                    v_isSharedCheck_6073_ = (!crate::leanh::lean_is_exclusive(v___x_6034_)) as u8;
                    if v_isSharedCheck_6073_ == 0 {
                        v___x_6068_ = v___x_6034_;
                        v_isShared_6069_ = v_isSharedCheck_6073_;
                        state = 33;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_6066_);
                        crate::leanh::lean_dec(v___x_6034_);
                        v___x_6068_ = crate::leanh::lean_box(0);
                        v_isShared_6069_ = v_isSharedCheck_6073_;
                        state = 33;
                        continue;
                    }
                }
            }
            29 => {
                if v_isShared_6052_ == 0 {
                    v___x_6054_ = v___x_6051_;
                    state = 30;
                    continue;
                } else {
                    v_reuseFailAlloc_6055_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6055_, 0, v_a_6049_);
                    v___x_6054_ = v_reuseFailAlloc_6055_;
                    state = 30;
                    continue;
                }
            }
            30 => {
                return v___x_6054_;
            }
            31 => {
                if v_isShared_6061_ == 0 {
                    v___x_6063_ = v___x_6060_;
                    state = 32;
                    continue;
                } else {
                    v_reuseFailAlloc_6064_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6064_, 0, v_a_6058_);
                    v___x_6063_ = v_reuseFailAlloc_6064_;
                    state = 32;
                    continue;
                }
            }
            32 => {
                return v___x_6063_;
            }
            33 => {
                if v_isShared_6069_ == 0 {
                    v___x_6071_ = v___x_6068_;
                    state = 34;
                    continue;
                } else {
                    v_reuseFailAlloc_6072_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6072_, 0, v_a_6066_);
                    v___x_6071_ = v_reuseFailAlloc_6072_;
                    state = 34;
                    continue;
                }
            }
            34 => {
                return v___x_6071_;
            }
            35 => {
                if v_isShared_6084_ == 0 {
                    v___x_6086_ = v___x_6083_;
                    state = 36;
                    continue;
                } else {
                    v_reuseFailAlloc_6087_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6087_, 0, v_a_6081_);
                    v___x_6086_ = v_reuseFailAlloc_6087_;
                    state = 36;
                    continue;
                }
            }
            36 => {
                return v___x_6086_;
            }
            37 => {
                v_fst_6101_ = crate::leanh::lean_ctor_get(v_a_6097_, 0);
                if crate::leanh::lean_obj_tag(v_fst_6101_) == 1 {
                    crate::leanh::lean_del_object(v___x_6099_);
                    crate::leanh::lean_dec_ref(v_snd_5829_);
                    v_val_6102_ = crate::leanh::lean_ctor_get(v_fst_6101_, 0);
                    crate::leanh::lean_inc(v_val_6102_);
                    v_snd_6103_ = crate::leanh::lean_ctor_get(v_a_6097_, 1);
                    crate::leanh::lean_inc(v_snd_6103_);
                    crate::leanh::lean_dec(v_a_6097_);
                    v_snd_6104_ = crate::leanh::lean_ctor_get(v_val_6102_, 1);
                    crate::leanh::lean_inc(v_snd_6104_);
                    crate::leanh::lean_dec(v_val_6102_);
                    v___x_6105_ = l_Lean_MVarId_assumption(
                        v_snd_6104_,
                        v___y_5836_,
                        v___y_5837_,
                        v___y_5838_,
                        v___y_5839_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_6105_) == 0 {
                        v_isSharedCheck_6112_ =
                            (!crate::leanh::lean_is_exclusive(v___x_6105_)) as u8;
                        if v_isSharedCheck_6112_ == 0 {
                            v_unused_6113_ = crate::leanh::lean_ctor_get(v___x_6105_, 0);
                            crate::leanh::lean_dec(v_unused_6113_);
                            v___x_6107_ = v___x_6105_;
                            v_isShared_6108_ = v_isSharedCheck_6112_;
                            state = 38;
                            continue;
                        } else {
                            crate::leanh::lean_dec(v___x_6105_);
                            v___x_6107_ = crate::leanh::lean_box(0);
                            v_isShared_6108_ = v_isSharedCheck_6112_;
                            state = 38;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec(v_snd_6103_);
                        v_a_6114_ = crate::leanh::lean_ctor_get(v___x_6105_, 0);
                        v_isSharedCheck_6121_ =
                            (!crate::leanh::lean_is_exclusive(v___x_6105_)) as u8;
                        if v_isSharedCheck_6121_ == 0 {
                            v___x_6116_ = v___x_6105_;
                            v_isShared_6117_ = v_isSharedCheck_6121_;
                            state = 40;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_6114_);
                            crate::leanh::lean_dec(v___x_6105_);
                            v___x_6116_ = crate::leanh::lean_box(0);
                            v_isShared_6117_ = v_isSharedCheck_6121_;
                            state = 40;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec(v_a_6097_);
                    if v_isShared_6100_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_6099_, 0, v_snd_5829_);
                        v___x_6123_ = v___x_6099_;
                        state = 42;
                        continue;
                    } else {
                        v_reuseFailAlloc_6124_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_6124_, 0, v_snd_5829_);
                        v___x_6123_ = v_reuseFailAlloc_6124_;
                        state = 42;
                        continue;
                    }
                }
            }
            38 => {
                if v_isShared_6108_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_6107_, 0, v_snd_6103_);
                    v___x_6110_ = v___x_6107_;
                    state = 39;
                    continue;
                } else {
                    v_reuseFailAlloc_6111_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6111_, 0, v_snd_6103_);
                    v___x_6110_ = v_reuseFailAlloc_6111_;
                    state = 39;
                    continue;
                }
            }
            39 => {
                return v___x_6110_;
            }
            40 => {
                if v_isShared_6117_ == 0 {
                    v___x_6119_ = v___x_6116_;
                    state = 41;
                    continue;
                } else {
                    v_reuseFailAlloc_6120_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6120_, 0, v_a_6114_);
                    v___x_6119_ = v_reuseFailAlloc_6120_;
                    state = 41;
                    continue;
                }
            }
            41 => {
                return v___x_6119_;
            }
            42 => {
                return v___x_6123_;
            }
            43 => {
                if v_isShared_6129_ == 0 {
                    v___x_6131_ = v___x_6128_;
                    state = 44;
                    continue;
                } else {
                    v_reuseFailAlloc_6132_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6132_, 0, v_a_6126_);
                    v___x_6131_ = v_reuseFailAlloc_6132_;
                    state = 44;
                    continue;
                }
            }
            44 => {
                return v___x_6131_;
            }
            45 => {
                if v_isShared_6137_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_6136_, 0, v_snd_5829_);
                    v___x_6139_ = v___x_6136_;
                    state = 46;
                    continue;
                } else {
                    v_reuseFailAlloc_6140_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6140_, 0, v_snd_5829_);
                    v___x_6139_ = v_reuseFailAlloc_6140_;
                    state = 46;
                    continue;
                }
            }
            46 => {
                return v___x_6139_;
            }
            47 => {
                if v_isShared_6146_ == 0 {
                    v___x_6148_ = v___x_6145_;
                    state = 48;
                    continue;
                } else {
                    v_reuseFailAlloc_6149_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6149_, 0, v_a_6143_);
                    v___x_6148_ = v_reuseFailAlloc_6149_;
                    state = 48;
                    continue;
                }
            }
            48 => {
                return v___x_6148_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__4___boxed(
    _args: *mut *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_usingArg_6151_: *mut crate::leanh::LeanObject = *_args.add(0);
    let mut v_snd_6152_: *mut crate::leanh::LeanObject = *_args.add(1);
    let mut v___x_6153_: *mut crate::leanh::LeanObject = *_args.add(2);
    let mut v___x_6154_: *mut crate::leanh::LeanObject = *_args.add(3);
    let mut v___x_6155_: *mut crate::leanh::LeanObject = *_args.add(4);
    let mut v_useReducible_6156_: *mut crate::leanh::LeanObject = *_args.add(5);
    let mut v___x_6157_: *mut crate::leanh::LeanObject = *_args.add(6);
    let mut v___x_6158_: *mut crate::leanh::LeanObject = *_args.add(7);
    let mut v___x_6159_: *mut crate::leanh::LeanObject = *_args.add(8);
    let mut v_simprocs_6160_: *mut crate::leanh::LeanObject = *_args.add(9);
    let mut v_discharge_x3f_6161_: *mut crate::leanh::LeanObject = *_args.add(10);
    let mut v_snd_6162_: *mut crate::leanh::LeanObject = *_args.add(11);
    let mut v___x_6163_: *mut crate::leanh::LeanObject = *_args.add(12);
    let mut v___f_6164_: *mut crate::leanh::LeanObject = *_args.add(13);
    let mut v___y_6165_: *mut crate::leanh::LeanObject = *_args.add(14);
    let mut v___y_6166_: *mut crate::leanh::LeanObject = *_args.add(15);
    let mut v___y_6167_: *mut crate::leanh::LeanObject = *_args.add(16);
    let mut v___y_6168_: *mut crate::leanh::LeanObject = *_args.add(17);
    let mut v___y_6169_: *mut crate::leanh::LeanObject = *_args.add(18);
    let mut v___y_6170_: *mut crate::leanh::LeanObject = *_args.add(19);
    let mut v___y_6171_: *mut crate::leanh::LeanObject = *_args.add(20);
    let mut v___y_6172_: *mut crate::leanh::LeanObject = *_args.add(21);
    let mut v___y_6173_: *mut crate::leanh::LeanObject = *_args.add(22);
    let mut v___x_95754__boxed_6174_: u8 = 0;
    let mut v___x_95755__boxed_6175_: u8 = 0;
    let mut v_useReducible_boxed_6176_: u8 = 0;
    let mut v___x_95757__boxed_6177_: u8 = 0;
    let mut v_res_6178_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_95754__boxed_6174_ = (crate::leanh::lean_unbox(v___x_6153_) as u8);
    v___x_95755__boxed_6175_ = (crate::leanh::lean_unbox(v___x_6154_) as u8);
    v_useReducible_boxed_6176_ = (crate::leanh::lean_unbox(v_useReducible_6156_) as u8);
    v___x_95757__boxed_6177_ = (crate::leanh::lean_unbox(v___x_6157_) as u8);
    v_res_6178_ =
        l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__4(
            v_usingArg_6151_,
            v_snd_6152_,
            v___x_95754__boxed_6174_,
            v___x_95755__boxed_6175_,
            v___x_6155_,
            v_useReducible_boxed_6176_,
            v___x_95757__boxed_6177_,
            v___x_6158_,
            v___x_6159_,
            v_simprocs_6160_,
            v_discharge_x3f_6161_,
            v_snd_6162_,
            v___x_6163_,
            v___f_6164_,
            v___y_6165_,
            v___y_6166_,
            v___y_6167_,
            v___y_6168_,
            v___y_6169_,
            v___y_6170_,
            v___y_6171_,
            v___y_6172_,
        );
    crate::leanh::lean_dec(v___y_6172_);
    crate::leanh::lean_dec_ref(v___y_6171_);
    crate::leanh::lean_dec(v___y_6170_);
    crate::leanh::lean_dec_ref(v___y_6169_);
    crate::leanh::lean_dec(v___y_6168_);
    crate::leanh::lean_dec_ref(v___y_6167_);
    crate::leanh::lean_dec(v___y_6166_);
    crate::leanh::lean_dec_ref(v___y_6165_);
    crate::leanh::lean_dec(v___x_6163_);
    crate::leanh::lean_dec(v___x_6158_);
    return v_res_6178_;
}
pub unsafe fn _init_l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__5___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_6179_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6179_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
    );
    return v___x_6179_;
}
pub unsafe fn _init_l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__5___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_6180_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6181_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6180_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__5___closed__0), core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__5___closed__0_once), _init_l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__5___closed__0);
    v___x_6181_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_6181_, 0, v___x_6180_);
    return v___x_6181_;
}
pub unsafe fn _init_l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__5___closed__2()
-> *mut crate::leanh::LeanObject {
    let mut v___x_6182_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6183_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6184_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6182_ = crate::leanh::lean_unsigned_to_nat(32);
    v___x_6183_ = lean_mk_empty_array_with_capacity(v___x_6182_);
    v___x_6184_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_6184_, 0, v___x_6183_);
    return v___x_6184_;
}
pub unsafe fn _init_l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__5___closed__5()
-> *mut crate::leanh::LeanObject {
    let mut v___x_6188_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6189_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6188_ = l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__5___closed__4;
    v___x_6189_ = l_Lean_MessageData_ofFormat(v___x_6188_);
    return v___x_6189_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__5(
    mut v___x_6190_: *mut crate::leanh::LeanObject,
    mut v_tk_6191_: *mut crate::leanh::LeanObject,
    mut v___x_6192_: *mut crate::leanh::LeanObject,
    mut v___x_6193_: *mut crate::leanh::LeanObject,
    mut v___x_6194_: *mut crate::leanh::LeanObject,
    mut v_simprocs_6195_: *mut crate::leanh::LeanObject,
    mut v___x_6196_: u8,
    mut v_usingArg_6197_: *mut crate::leanh::LeanObject,
    mut v___x_6198_: u8,
    mut v___x_6199_: *mut crate::leanh::LeanObject,
    mut v_useReducible_6200_: u8,
    mut v___x_6201_: u8,
    mut v___x_6202_: *mut crate::leanh::LeanObject,
    mut v_usingTk_x3f_6203_: *mut crate::leanh::LeanObject,
    mut v_discharge_x3f_6204_: *mut crate::leanh::LeanObject,
    mut v___y_6205_: *mut crate::leanh::LeanObject,
    mut v___y_6206_: *mut crate::leanh::LeanObject,
    mut v___y_6207_: *mut crate::leanh::LeanObject,
    mut v___y_6208_: *mut crate::leanh::LeanObject,
    mut v___y_6209_: *mut crate::leanh::LeanObject,
    mut v___y_6210_: *mut crate::leanh::LeanObject,
    mut v___y_6211_: *mut crate::leanh::LeanObject,
    mut v___y_6212_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_6215_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6216_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6217_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6218_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6219_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6220_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6221_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6222_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6223_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6224_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6225_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6226_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6227_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6228_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6229_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6230_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6231_: usize = 0;
    let mut v___x_6232_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6233_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6234_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6235_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6236_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_6237_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_6238_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_6239_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_6240_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6242_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6243_: u8 = 0;
    let mut v___x_6244_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6246_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6247_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_6248_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6249_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6250_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6251_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6252_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6253_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6254_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6255_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6257_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6258_: u8 = 0;
    let mut v___x_6260_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6261_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6262_: u8 = 0;
    let mut v_reuseFailAlloc_6263_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6264_: u8 = 0;
    let mut v_unused_6265_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6266_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6267_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6269_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6270_: u8 = 0;
    let mut v___x_6271_: u8 = 0;
    let mut v___x_6273_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6274_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_6275_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6276_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6277_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6278_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6280_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6281_: u8 = 0;
    let mut v___x_6283_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6284_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6285_: u8 = 0;
    let mut v_unused_6286_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6287_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6289_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6290_: u8 = 0;
    let mut v___x_6292_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6293_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6294_: u8 = 0;
    let mut v_isSharedCheck_6295_: u8 = 0;
    let mut v_a_6296_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6298_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6299_: u8 = 0;
    let mut v___x_6301_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6302_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6303_: u8 = 0;
    let mut v_a_6304_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6306_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6307_: u8 = 0;
    let mut v___x_6309_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6310_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6311_: u8 = 0;
    let mut v_a_6312_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6314_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6315_: u8 = 0;
    let mut v___x_6317_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6318_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6319_: u8 = 0;
    let mut v___x_6320_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_6321_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_usingTk_x3f_6203_) == 0 {
                    v___x_6320_ = crate::leanh::lean_box(0);
                    v___y_6215_ = v___x_6320_;
                    state = 1;
                    continue;
                } else {
                    v_val_6321_ = crate::leanh::lean_ctor_get(v_usingTk_x3f_6203_, 0);
                    crate::leanh::lean_inc(v_val_6321_);
                    crate::leanh::lean_dec_ref_known(v_usingTk_x3f_6203_, 1);
                    v___y_6215_ = v_val_6321_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_6216_ = lean_mk_empty_array_with_capacity(v___x_6190_);
                v___x_6217_ = lean_array_push(v___x_6216_, v_tk_6191_);
                v___x_6218_ = lean_array_push(v___x_6217_, v___y_6215_);
                v___x_6219_ = crate::leanh::lean_box(2);
                v___x_6220_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_6220_, 0, v___x_6219_);
                crate::leanh::lean_ctor_set(v___x_6220_, 1, v___x_6192_);
                crate::leanh::lean_ctor_set(v___x_6220_, 2, v___x_6218_);
                v___x_6221_ = l_Lean_Elab_Tactic_mkInitialTacticInfo(
                    v___x_6220_,
                    v___y_6205_,
                    v___y_6206_,
                    v___y_6207_,
                    v___y_6208_,
                    v___y_6209_,
                    v___y_6210_,
                    v___y_6211_,
                    v___y_6212_,
                );
                if crate::leanh::lean_obj_tag(v___x_6221_) == 0 {
                    v_a_6222_ = crate::leanh::lean_ctor_get(v___x_6221_, 0);
                    crate::leanh::lean_inc(v_a_6222_);
                    crate::leanh::lean_dec_ref_known(v___x_6221_, 1);
                    v___x_6223_ = l_Lean_Elab_Tactic_getMainGoal___redArg(
                        v___y_6206_,
                        v___y_6209_,
                        v___y_6210_,
                        v___y_6211_,
                        v___y_6212_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_6223_) == 0 {
                        v_a_6224_ = crate::leanh::lean_ctor_get(v___x_6223_, 0);
                        crate::leanh::lean_inc(v_a_6224_);
                        crate::leanh::lean_dec_ref_known(v___x_6223_, 1);
                        v___x_6225_ = lean_mk_empty_array_with_capacity(v___x_6193_);
                        v___x_6226_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__5___closed__1), core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__5___closed__1_once), _init_l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__5___closed__1);
                        crate::leanh::lean_inc_n(v___x_6193_, 3);
                        v___x_6227_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_6227_, 0, v___x_6226_);
                        crate::leanh::lean_ctor_set(v___x_6227_, 1, v___x_6193_);
                        v___x_6228_ = crate::leanh::lean_unsigned_to_nat(32);
                        v___x_6229_ = lean_mk_empty_array_with_capacity(v___x_6228_);
                        v___x_6230_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__5___closed__2), core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__5___closed__2_once), _init_l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__5___closed__2);
                        v___x_6231_ = 5usize;
                        v___x_6232_ = crate::leanh::lean_alloc_ctor(
                            0,
                            4,
                            (core::mem::size_of::<usize>() * 1) as u32,
                        );
                        crate::leanh::lean_ctor_set(v___x_6232_, 0, v___x_6230_);
                        crate::leanh::lean_ctor_set(v___x_6232_, 1, v___x_6229_);
                        crate::leanh::lean_ctor_set(v___x_6232_, 2, v___x_6193_);
                        crate::leanh::lean_ctor_set(v___x_6232_, 3, v___x_6193_);
                        crate::leanh::lean_ctor_set_usize(v___x_6232_, 4, v___x_6231_);
                        v___x_6233_ = crate::leanh::lean_alloc_ctor(0, 4, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_6233_, 0, v___x_6226_);
                        crate::leanh::lean_ctor_set(v___x_6233_, 1, v___x_6226_);
                        crate::leanh::lean_ctor_set(v___x_6233_, 2, v___x_6226_);
                        crate::leanh::lean_ctor_set(v___x_6233_, 3, v___x_6232_);
                        v___x_6234_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_6234_, 0, v___x_6227_);
                        crate::leanh::lean_ctor_set(v___x_6234_, 1, v___x_6233_);
                        crate::leanh::lean_inc_ref(v___x_6234_);
                        crate::leanh::lean_inc(v_discharge_x3f_6204_);
                        crate::leanh::lean_inc_ref(v_simprocs_6195_);
                        crate::leanh::lean_inc_ref(v___x_6194_);
                        v___x_6235_ = l_Lean_Meta_simpGoal(
                            v_a_6224_,
                            v___x_6194_,
                            v_simprocs_6195_,
                            v_discharge_x3f_6204_,
                            v___x_6196_,
                            v___x_6225_,
                            v___x_6234_,
                            v___y_6209_,
                            v___y_6210_,
                            v___y_6211_,
                            v___y_6212_,
                        );
                        if crate::leanh::lean_obj_tag(v___x_6235_) == 0 {
                            v_a_6236_ = crate::leanh::lean_ctor_get(v___x_6235_, 0);
                            crate::leanh::lean_inc(v_a_6236_);
                            crate::leanh::lean_dec_ref_known(v___x_6235_, 1);
                            v_fst_6237_ = crate::leanh::lean_ctor_get(v_a_6236_, 0);
                            if crate::leanh::lean_obj_tag(v_fst_6237_) == 1 {
                                crate::leanh::lean_dec_ref_known(v___x_6234_, 2);
                                v_val_6238_ = crate::leanh::lean_ctor_get(v_fst_6237_, 0);
                                crate::leanh::lean_inc(v_val_6238_);
                                v_snd_6239_ = crate::leanh::lean_ctor_get(v_a_6236_, 1);
                                crate::leanh::lean_inc(v_snd_6239_);
                                crate::leanh::lean_dec(v_a_6236_);
                                v_snd_6240_ = crate::leanh::lean_ctor_get(v_val_6238_, 1);
                                v_isSharedCheck_6264_ =
                                    (!crate::leanh::lean_is_exclusive(v_val_6238_)) as u8;
                                if v_isSharedCheck_6264_ == 0 {
                                    v_unused_6265_ = crate::leanh::lean_ctor_get(v_val_6238_, 0);
                                    crate::leanh::lean_dec(v_unused_6265_);
                                    v___x_6242_ = v_val_6238_;
                                    v_isShared_6243_ = v_isSharedCheck_6264_;
                                    state = 2;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_snd_6240_);
                                    crate::leanh::lean_dec(v_val_6238_);
                                    v___x_6242_ = crate::leanh::lean_box(0);
                                    v_isShared_6243_ = v_isSharedCheck_6264_;
                                    state = 2;
                                    continue;
                                }
                            } else {
                                crate::leanh::lean_dec(v_a_6236_);
                                crate::leanh::lean_dec(v_a_6222_);
                                crate::leanh::lean_dec(v_discharge_x3f_6204_);
                                crate::leanh::lean_dec(v___x_6202_);
                                crate::leanh::lean_dec_ref(v___x_6199_);
                                crate::leanh::lean_dec(v_usingArg_6197_);
                                crate::leanh::lean_dec_ref(v_simprocs_6195_);
                                crate::leanh::lean_dec_ref(v___x_6194_);
                                crate::leanh::lean_dec(v___x_6193_);
                                v___x_6266_ = l_Lean_Linter_getLinterOptions___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__3(v___y_6205_, v___y_6206_, v___y_6207_, v___y_6208_, v___y_6209_, v___y_6210_, v___y_6211_, v___y_6212_);
                                v_a_6267_ = crate::leanh::lean_ctor_get(v___x_6266_, 0);
                                v_isSharedCheck_6295_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_6266_)) as u8;
                                if v_isSharedCheck_6295_ == 0 {
                                    v___x_6269_ = v___x_6266_;
                                    v_isShared_6270_ = v_isSharedCheck_6295_;
                                    state = 6;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_a_6267_);
                                    crate::leanh::lean_dec(v___x_6266_);
                                    v___x_6269_ = crate::leanh::lean_box(0);
                                    v_isShared_6270_ = v_isSharedCheck_6295_;
                                    state = 6;
                                    continue;
                                }
                            }
                        } else {
                            crate::leanh::lean_dec_ref_known(v___x_6234_, 2);
                            crate::leanh::lean_dec(v_a_6222_);
                            crate::leanh::lean_dec(v_discharge_x3f_6204_);
                            crate::leanh::lean_dec(v___x_6202_);
                            crate::leanh::lean_dec_ref(v___x_6199_);
                            crate::leanh::lean_dec(v_usingArg_6197_);
                            crate::leanh::lean_dec_ref(v_simprocs_6195_);
                            crate::leanh::lean_dec_ref(v___x_6194_);
                            crate::leanh::lean_dec(v___x_6193_);
                            v_a_6296_ = crate::leanh::lean_ctor_get(v___x_6235_, 0);
                            v_isSharedCheck_6303_ =
                                (!crate::leanh::lean_is_exclusive(v___x_6235_)) as u8;
                            if v_isSharedCheck_6303_ == 0 {
                                v___x_6298_ = v___x_6235_;
                                v_isShared_6299_ = v_isSharedCheck_6303_;
                                state = 12;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_6296_);
                                crate::leanh::lean_dec(v___x_6235_);
                                v___x_6298_ = crate::leanh::lean_box(0);
                                v_isShared_6299_ = v_isSharedCheck_6303_;
                                state = 12;
                                continue;
                            }
                        }
                    } else {
                        crate::leanh::lean_dec(v_a_6222_);
                        crate::leanh::lean_dec(v_discharge_x3f_6204_);
                        crate::leanh::lean_dec(v___x_6202_);
                        crate::leanh::lean_dec_ref(v___x_6199_);
                        crate::leanh::lean_dec(v_usingArg_6197_);
                        crate::leanh::lean_dec_ref(v_simprocs_6195_);
                        crate::leanh::lean_dec_ref(v___x_6194_);
                        crate::leanh::lean_dec(v___x_6193_);
                        v_a_6304_ = crate::leanh::lean_ctor_get(v___x_6223_, 0);
                        v_isSharedCheck_6311_ =
                            (!crate::leanh::lean_is_exclusive(v___x_6223_)) as u8;
                        if v_isSharedCheck_6311_ == 0 {
                            v___x_6306_ = v___x_6223_;
                            v_isShared_6307_ = v_isSharedCheck_6311_;
                            state = 14;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_6304_);
                            crate::leanh::lean_dec(v___x_6223_);
                            v___x_6306_ = crate::leanh::lean_box(0);
                            v_isShared_6307_ = v_isSharedCheck_6311_;
                            state = 14;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec(v_discharge_x3f_6204_);
                    crate::leanh::lean_dec(v___x_6202_);
                    crate::leanh::lean_dec_ref(v___x_6199_);
                    crate::leanh::lean_dec(v_usingArg_6197_);
                    crate::leanh::lean_dec_ref(v_simprocs_6195_);
                    crate::leanh::lean_dec_ref(v___x_6194_);
                    crate::leanh::lean_dec(v___x_6193_);
                    v_a_6312_ = crate::leanh::lean_ctor_get(v___x_6221_, 0);
                    v_isSharedCheck_6319_ = (!crate::leanh::lean_is_exclusive(v___x_6221_)) as u8;
                    if v_isSharedCheck_6319_ == 0 {
                        v___x_6314_ = v___x_6221_;
                        v_isShared_6315_ = v_isSharedCheck_6319_;
                        state = 16;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_6312_);
                        crate::leanh::lean_dec(v___x_6221_);
                        v___x_6314_ = crate::leanh::lean_box(0);
                        v_isShared_6315_ = v_isSharedCheck_6319_;
                        state = 16;
                        continue;
                    }
                }
            }
            2 => {
                v___x_6244_ = crate::leanh::lean_box(0);
                crate::leanh::lean_inc(v_snd_6240_);
                if v_isShared_6243_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_6242_, 1);
                    crate::leanh::lean_ctor_set(v___x_6242_, 1, v___x_6244_);
                    crate::leanh::lean_ctor_set(v___x_6242_, 0, v_snd_6240_);
                    v___x_6246_ = v___x_6242_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_6263_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6263_, 0, v_snd_6240_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6263_, 1, v___x_6244_);
                    v___x_6246_ = v_reuseFailAlloc_6263_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_6247_ = l_Lean_Elab_Tactic_replaceMainGoal___redArg(
                    v___x_6246_,
                    v___y_6206_,
                    v___y_6209_,
                    v___y_6210_,
                    v___y_6211_,
                    v___y_6212_,
                );
                if crate::leanh::lean_obj_tag(v___x_6247_) == 0 {
                    crate::leanh::lean_dec_ref_known(v___x_6247_, 1);
                    v___f_6248_ = crate::leanh::lean_alloc_closure(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__1___boxed as *mut core::ffi::c_void, 11, 1);
                    crate::leanh::lean_closure_set(v___f_6248_, 0, v_a_6222_);
                    v___x_6249_ = crate::leanh::lean_box((v___x_6196_) as usize);
                    v___x_6250_ = crate::leanh::lean_box((v___x_6198_) as usize);
                    v___x_6251_ = crate::leanh::lean_box((v_useReducible_6200_) as usize);
                    v___x_6252_ = crate::leanh::lean_box((v___x_6201_) as usize);
                    crate::leanh::lean_inc(v_snd_6240_);
                    v___y_6253_ = crate::leanh::lean_alloc_closure(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__4___boxed as *mut core::ffi::c_void, 23, 14);
                    crate::leanh::lean_closure_set(v___y_6253_, 0, v_usingArg_6197_);
                    crate::leanh::lean_closure_set(v___y_6253_, 1, v_snd_6240_);
                    crate::leanh::lean_closure_set(v___y_6253_, 2, v___x_6249_);
                    crate::leanh::lean_closure_set(v___y_6253_, 3, v___x_6250_);
                    crate::leanh::lean_closure_set(v___y_6253_, 4, v___x_6199_);
                    crate::leanh::lean_closure_set(v___y_6253_, 5, v___x_6251_);
                    crate::leanh::lean_closure_set(v___y_6253_, 6, v___x_6252_);
                    crate::leanh::lean_closure_set(v___y_6253_, 7, v___x_6202_);
                    crate::leanh::lean_closure_set(v___y_6253_, 8, v___x_6194_);
                    crate::leanh::lean_closure_set(v___y_6253_, 9, v_simprocs_6195_);
                    crate::leanh::lean_closure_set(v___y_6253_, 10, v_discharge_x3f_6204_);
                    crate::leanh::lean_closure_set(v___y_6253_, 11, v_snd_6239_);
                    crate::leanh::lean_closure_set(v___y_6253_, 12, v___x_6193_);
                    crate::leanh::lean_closure_set(v___y_6253_, 13, v___f_6248_);
                    v___x_6254_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__5___redArg(v_snd_6240_, v___y_6253_, v___y_6205_, v___y_6206_, v___y_6207_, v___y_6208_, v___y_6209_, v___y_6210_, v___y_6211_, v___y_6212_);
                    return v___x_6254_;
                } else {
                    crate::leanh::lean_dec(v_snd_6240_);
                    crate::leanh::lean_dec(v_snd_6239_);
                    crate::leanh::lean_dec(v_a_6222_);
                    crate::leanh::lean_dec(v_discharge_x3f_6204_);
                    crate::leanh::lean_dec(v___x_6202_);
                    crate::leanh::lean_dec_ref(v___x_6199_);
                    crate::leanh::lean_dec(v_usingArg_6197_);
                    crate::leanh::lean_dec_ref(v_simprocs_6195_);
                    crate::leanh::lean_dec_ref(v___x_6194_);
                    crate::leanh::lean_dec(v___x_6193_);
                    v_a_6255_ = crate::leanh::lean_ctor_get(v___x_6247_, 0);
                    v_isSharedCheck_6262_ = (!crate::leanh::lean_is_exclusive(v___x_6247_)) as u8;
                    if v_isSharedCheck_6262_ == 0 {
                        v___x_6257_ = v___x_6247_;
                        v_isShared_6258_ = v_isSharedCheck_6262_;
                        state = 4;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_6255_);
                        crate::leanh::lean_dec(v___x_6247_);
                        v___x_6257_ = crate::leanh::lean_box(0);
                        v_isShared_6258_ = v_isSharedCheck_6262_;
                        state = 4;
                        continue;
                    }
                }
            }
            4 => {
                if v_isShared_6258_ == 0 {
                    v___x_6260_ = v___x_6257_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_6261_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6261_, 0, v_a_6255_);
                    v___x_6260_ = v_reuseFailAlloc_6261_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_6260_;
            }
            6 => {
                v___x_6271_ = l_Lean_Elab_Tactic_Simpa_getLinterUnnecessarySimpa(v_a_6267_);
                crate::leanh::lean_dec(v_a_6267_);
                if v___x_6271_ == 0 {
                    if v_isShared_6270_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_6269_, 0, v___x_6234_);
                        v___x_6273_ = v___x_6269_;
                        state = 7;
                        continue;
                    } else {
                        v_reuseFailAlloc_6274_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_6274_, 0, v___x_6234_);
                        v___x_6273_ = v_reuseFailAlloc_6274_;
                        state = 7;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_6269_);
                    v_ref_6275_ = crate::leanh::lean_ctor_get(v___y_6211_, 5);
                    v___x_6276_ = l_linter_unnecessarySimpa;
                    v___x_6277_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__5___closed__5), core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__5___closed__5_once), _init_l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__5___closed__5);
                    v___x_6278_ = l_Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4(v___x_6276_, v_ref_6275_, v___x_6277_, v___y_6205_, v___y_6206_, v___y_6207_, v___y_6208_, v___y_6209_, v___y_6210_, v___y_6211_, v___y_6212_);
                    if crate::leanh::lean_obj_tag(v___x_6278_) == 0 {
                        v_isSharedCheck_6285_ =
                            (!crate::leanh::lean_is_exclusive(v___x_6278_)) as u8;
                        if v_isSharedCheck_6285_ == 0 {
                            v_unused_6286_ = crate::leanh::lean_ctor_get(v___x_6278_, 0);
                            crate::leanh::lean_dec(v_unused_6286_);
                            v___x_6280_ = v___x_6278_;
                            v_isShared_6281_ = v_isSharedCheck_6285_;
                            state = 8;
                            continue;
                        } else {
                            crate::leanh::lean_dec(v___x_6278_);
                            v___x_6280_ = crate::leanh::lean_box(0);
                            v_isShared_6281_ = v_isSharedCheck_6285_;
                            state = 8;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec_ref_known(v___x_6234_, 2);
                        v_a_6287_ = crate::leanh::lean_ctor_get(v___x_6278_, 0);
                        v_isSharedCheck_6294_ =
                            (!crate::leanh::lean_is_exclusive(v___x_6278_)) as u8;
                        if v_isSharedCheck_6294_ == 0 {
                            v___x_6289_ = v___x_6278_;
                            v_isShared_6290_ = v_isSharedCheck_6294_;
                            state = 10;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_6287_);
                            crate::leanh::lean_dec(v___x_6278_);
                            v___x_6289_ = crate::leanh::lean_box(0);
                            v_isShared_6290_ = v_isSharedCheck_6294_;
                            state = 10;
                            continue;
                        }
                    }
                }
            }
            7 => {
                return v___x_6273_;
            }
            8 => {
                if v_isShared_6281_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_6280_, 0, v___x_6234_);
                    v___x_6283_ = v___x_6280_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_6284_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6284_, 0, v___x_6234_);
                    v___x_6283_ = v_reuseFailAlloc_6284_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_6283_;
            }
            10 => {
                if v_isShared_6290_ == 0 {
                    v___x_6292_ = v___x_6289_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_6293_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6293_, 0, v_a_6287_);
                    v___x_6292_ = v_reuseFailAlloc_6293_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                return v___x_6292_;
            }
            12 => {
                if v_isShared_6299_ == 0 {
                    v___x_6301_ = v___x_6298_;
                    state = 13;
                    continue;
                } else {
                    v_reuseFailAlloc_6302_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6302_, 0, v_a_6296_);
                    v___x_6301_ = v_reuseFailAlloc_6302_;
                    state = 13;
                    continue;
                }
            }
            13 => {
                return v___x_6301_;
            }
            14 => {
                if v_isShared_6307_ == 0 {
                    v___x_6309_ = v___x_6306_;
                    state = 15;
                    continue;
                } else {
                    v_reuseFailAlloc_6310_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6310_, 0, v_a_6304_);
                    v___x_6309_ = v_reuseFailAlloc_6310_;
                    state = 15;
                    continue;
                }
            }
            15 => {
                return v___x_6309_;
            }
            16 => {
                if v_isShared_6315_ == 0 {
                    v___x_6317_ = v___x_6314_;
                    state = 17;
                    continue;
                } else {
                    v_reuseFailAlloc_6318_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6318_, 0, v_a_6312_);
                    v___x_6317_ = v_reuseFailAlloc_6318_;
                    state = 17;
                    continue;
                }
            }
            17 => {
                return v___x_6317_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__5___boxed(
    _args: *mut *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6322_: *mut crate::leanh::LeanObject = *_args.add(0);
    let mut v_tk_6323_: *mut crate::leanh::LeanObject = *_args.add(1);
    let mut v___x_6324_: *mut crate::leanh::LeanObject = *_args.add(2);
    let mut v___x_6325_: *mut crate::leanh::LeanObject = *_args.add(3);
    let mut v___x_6326_: *mut crate::leanh::LeanObject = *_args.add(4);
    let mut v_simprocs_6327_: *mut crate::leanh::LeanObject = *_args.add(5);
    let mut v___x_6328_: *mut crate::leanh::LeanObject = *_args.add(6);
    let mut v_usingArg_6329_: *mut crate::leanh::LeanObject = *_args.add(7);
    let mut v___x_6330_: *mut crate::leanh::LeanObject = *_args.add(8);
    let mut v___x_6331_: *mut crate::leanh::LeanObject = *_args.add(9);
    let mut v_useReducible_6332_: *mut crate::leanh::LeanObject = *_args.add(10);
    let mut v___x_6333_: *mut crate::leanh::LeanObject = *_args.add(11);
    let mut v___x_6334_: *mut crate::leanh::LeanObject = *_args.add(12);
    let mut v_usingTk_x3f_6335_: *mut crate::leanh::LeanObject = *_args.add(13);
    let mut v_discharge_x3f_6336_: *mut crate::leanh::LeanObject = *_args.add(14);
    let mut v___y_6337_: *mut crate::leanh::LeanObject = *_args.add(15);
    let mut v___y_6338_: *mut crate::leanh::LeanObject = *_args.add(16);
    let mut v___y_6339_: *mut crate::leanh::LeanObject = *_args.add(17);
    let mut v___y_6340_: *mut crate::leanh::LeanObject = *_args.add(18);
    let mut v___y_6341_: *mut crate::leanh::LeanObject = *_args.add(19);
    let mut v___y_6342_: *mut crate::leanh::LeanObject = *_args.add(20);
    let mut v___y_6343_: *mut crate::leanh::LeanObject = *_args.add(21);
    let mut v___y_6344_: *mut crate::leanh::LeanObject = *_args.add(22);
    let mut v___y_6345_: *mut crate::leanh::LeanObject = *_args.add(23);
    let mut v___x_96478__boxed_6346_: u8 = 0;
    let mut v___x_96479__boxed_6347_: u8 = 0;
    let mut v_useReducible_boxed_6348_: u8 = 0;
    let mut v___x_96481__boxed_6349_: u8 = 0;
    let mut v_res_6350_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_96478__boxed_6346_ = (crate::leanh::lean_unbox(v___x_6328_) as u8);
    v___x_96479__boxed_6347_ = (crate::leanh::lean_unbox(v___x_6330_) as u8);
    v_useReducible_boxed_6348_ = (crate::leanh::lean_unbox(v_useReducible_6332_) as u8);
    v___x_96481__boxed_6349_ = (crate::leanh::lean_unbox(v___x_6333_) as u8);
    v_res_6350_ =
        l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__5(
            v___x_6322_,
            v_tk_6323_,
            v___x_6324_,
            v___x_6325_,
            v___x_6326_,
            v_simprocs_6327_,
            v___x_96478__boxed_6346_,
            v_usingArg_6329_,
            v___x_96479__boxed_6347_,
            v___x_6331_,
            v_useReducible_boxed_6348_,
            v___x_96481__boxed_6349_,
            v___x_6334_,
            v_usingTk_x3f_6335_,
            v_discharge_x3f_6336_,
            v___y_6337_,
            v___y_6338_,
            v___y_6339_,
            v___y_6340_,
            v___y_6341_,
            v___y_6342_,
            v___y_6343_,
            v___y_6344_,
        );
    crate::leanh::lean_dec(v___y_6344_);
    crate::leanh::lean_dec_ref(v___y_6343_);
    crate::leanh::lean_dec(v___y_6342_);
    crate::leanh::lean_dec_ref(v___y_6341_);
    crate::leanh::lean_dec(v___y_6340_);
    crate::leanh::lean_dec_ref(v___y_6339_);
    crate::leanh::lean_dec(v___y_6338_);
    crate::leanh::lean_dec_ref(v___y_6337_);
    crate::leanh::lean_dec(v___x_6322_);
    return v_res_6350_;
}
pub unsafe fn _init_l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__6()
-> *mut crate::leanh::LeanObject {
    let mut v___x_6358_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6359_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6360_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6361_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6362_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6363_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6358_ = l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__5;
    v___x_6359_ = crate::leanh::lean_unsigned_to_nat(38);
    v___x_6360_ = crate::leanh::lean_unsigned_to_nat(126);
    v___x_6361_ = l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__4;
    v___x_6362_ = l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__3;
    v___x_6363_ = l_mkPanicMessageWithDecl(
        v___x_6362_,
        v___x_6361_,
        v___x_6360_,
        v___x_6359_,
        v___x_6358_,
    );
    return v___x_6363_;
}
pub unsafe fn _init_l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__10()
-> *mut crate::leanh::LeanObject {
    let mut v___x_6368_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6368_ = l_Array_mkArray0(crate::leanh::lean_box(0));
    return v___x_6368_;
}
pub unsafe fn _init_l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__22()
-> *mut crate::leanh::LeanObject {
    let mut v___x_6380_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6381_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6382_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6383_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6384_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6385_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6380_ = l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__5;
    v___x_6381_ = crate::leanh::lean_unsigned_to_nat(15);
    v___x_6382_ = crate::leanh::lean_unsigned_to_nat(127);
    v___x_6383_ = l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__4;
    v___x_6384_ = l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__3;
    v___x_6385_ = l_mkPanicMessageWithDecl(
        v___x_6384_,
        v___x_6383_,
        v___x_6382_,
        v___x_6381_,
        v___x_6380_,
    );
    return v___x_6385_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6(
    mut v_tk_6387_: *mut crate::leanh::LeanObject,
    mut v___x_6388_: *mut crate::leanh::LeanObject,
    mut v___x_6389_: *mut crate::leanh::LeanObject,
    mut v___x_6390_: *mut crate::leanh::LeanObject,
    mut v___x_6391_: *mut crate::leanh::LeanObject,
    mut v___x_6392_: u8,
    mut v___x_6393_: *mut crate::leanh::LeanObject,
    mut v___x_6394_: *mut crate::leanh::LeanObject,
    mut v_useReducible_6395_: u8,
    mut v___f_6396_: *mut crate::leanh::LeanObject,
    mut v___x_6397_: *mut crate::leanh::LeanObject,
    mut v___x_6398_: *mut crate::leanh::LeanObject,
    mut v___x_6399_: *mut crate::leanh::LeanObject,
    mut v___x_6400_: *mut crate::leanh::LeanObject,
    mut v___x_6401_: *mut crate::leanh::LeanObject,
    mut v___x_6402_: *mut crate::leanh::LeanObject,
    mut v_usingArg_6403_: *mut crate::leanh::LeanObject,
    mut v___x_6404_: *mut crate::leanh::LeanObject,
    mut v___x_6405_: u8,
    mut v_usingTk_x3f_6406_: *mut crate::leanh::LeanObject,
    mut v_squeeze_6407_: *mut crate::leanh::LeanObject,
    mut v_unfold_6408_: *mut crate::leanh::LeanObject,
    mut v_args_6409_: *mut crate::leanh::LeanObject,
    mut v_only_6410_: *mut crate::leanh::LeanObject,
    mut v___y_6411_: *mut crate::leanh::LeanObject,
    mut v___y_6412_: *mut crate::leanh::LeanObject,
    mut v___y_6413_: *mut crate::leanh::LeanObject,
    mut v___y_6414_: *mut crate::leanh::LeanObject,
    mut v___y_6415_: *mut crate::leanh::LeanObject,
    mut v___y_6416_: *mut crate::leanh::LeanObject,
    mut v___y_6417_: *mut crate::leanh::LeanObject,
    mut v___y_6418_: *mut crate::leanh::LeanObject,
    mut v___y_6419_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_6422_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_diag_6423_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6424_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6426_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_stx_6427_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6428_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_6429_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6430_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6431_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6432_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6433_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6434_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6435_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6436_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6437_: u8 = 0;
    let mut v___x_6438_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6439_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6440_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6442_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6443_: u8 = 0;
    let mut v___x_6445_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6446_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6447_: u8 = 0;
    let mut v___y_6449_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_stx_6450_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6451_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6452_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_6453_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6455_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6456_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6457_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6458_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6459_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6460_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6461_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6462_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6463_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6464_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6465_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6466_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6467_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6469_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6470_: u8 = 0;
    let mut v___x_6472_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6473_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6474_: u8 = 0;
    let mut v_options_6475_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_6476_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6477_: u8 = 0;
    let mut v___x_6478_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6479_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6480_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6481_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6482_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6483_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6485_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6486_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6487_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6488_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6489_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6490_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6491_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6492_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6493_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6494_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6495_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6496_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6497_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6498_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6499_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6501_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6502_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6503_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6504_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6505_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6506_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6507_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6508_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6509_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6510_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6511_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6512_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6513_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_6514_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6515_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6516_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6517_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6518_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6520_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6521_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6522_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6523_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6524_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6525_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6526_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6527_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6528_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6529_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6530_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6531_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6532_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_6533_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6534_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6535_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6536_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6537_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6538_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6539_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6540_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6541_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6542_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6543_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6544_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6546_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6547_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6548_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6549_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6550_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6551_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6552_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6553_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6554_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6555_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6556_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6557_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6558_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_6559_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6560_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6561_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6562_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6563_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6564_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6566_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6567_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6568_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6569_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6570_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6571_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6572_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6573_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6574_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6575_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6576_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6577_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6578_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6579_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6580_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6581_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6582_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6583_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6584_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6585_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6587_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6588_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6589_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6590_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6591_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6592_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6593_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6594_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6595_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6596_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6597_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6598_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6599_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6600_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6601_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6602_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_6603_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6604_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6605_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6606_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6607_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6608_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6609_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6610_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6611_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6612_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6613_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6614_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6616_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6617_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6618_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6619_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6620_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6621_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6622_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6623_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6624_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6625_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6626_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6627_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6628_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6629_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6630_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6631_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_6632_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6633_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6634_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6635_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6636_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6637_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6639_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6640_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6641_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6642_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6643_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6644_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6645_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6646_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6647_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6648_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6649_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6650_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6651_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6652_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6653_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6655_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6656_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6657_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6658_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6659_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6660_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6661_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6662_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6663_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6664_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6665_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6666_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6667_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_6668_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6669_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6670_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6671_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6672_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6674_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6675_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6676_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6677_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6678_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6679_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6680_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6681_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6682_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6683_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6684_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6685_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6686_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_6687_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6688_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6689_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6690_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6691_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6692_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6693_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6694_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6695_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6696_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6697_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6698_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6700_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6701_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6702_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6703_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6704_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6705_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6706_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6707_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6708_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6709_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6710_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6711_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6712_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_6713_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6714_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6715_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6716_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6717_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6718_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6720_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6721_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6722_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6723_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6724_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6725_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6726_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6727_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6728_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6729_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6730_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6731_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6732_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6733_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6734_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6735_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6736_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6737_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6738_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6740_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6741_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6742_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6743_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6744_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6745_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6746_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6747_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6748_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6749_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6750_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6751_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6752_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6753_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6754_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_6755_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6756_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6757_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6758_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6759_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6760_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6761_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6762_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6763_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6764_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6765_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6766_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6768_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6769_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6770_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6771_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6772_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6773_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6774_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6775_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6776_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6777_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6778_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6779_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6780_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6781_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6782_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_6783_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6784_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6785_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6786_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6787_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6788_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6790_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6791_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6792_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6793_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6794_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6795_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6796_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6797_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6798_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6799_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6800_: u8 = 0;
    let mut v___y_6801_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6802_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6803_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6804_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_6805_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6806_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6807_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6808_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6809_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6810_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6811_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6812_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6813_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6814_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_6815_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6816_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6817_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6818_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6820_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6821_: u8 = 0;
    let mut v___x_6823_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6824_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6825_: u8 = 0;
    let mut v___x_6826_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6827_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6828_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6829_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6830_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_6831_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6832_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6833_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6834_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6836_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6837_: u8 = 0;
    let mut v___x_6839_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6840_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6841_: u8 = 0;
    let mut v_val_6842_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6843_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6844_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6845_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6846_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6847_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6848_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6849_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6850_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6851_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6852_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6853_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6854_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_6855_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6856_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6857_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6858_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6860_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6861_: u8 = 0;
    let mut v___x_6863_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6864_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6865_: u8 = 0;
    let mut v___x_6866_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6867_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6868_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6869_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6870_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6871_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6872_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_6873_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6874_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6875_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6876_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6878_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6879_: u8 = 0;
    let mut v___x_6881_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6882_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6883_: u8 = 0;
    let mut v___y_6885_: u8 = 0;
    let mut v___y_6886_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6887_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6888_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6889_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6890_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6891_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_args_6892_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6893_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6894_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6895_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6896_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6897_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6898_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6899_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6900_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6901_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6902_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6903_: u8 = 0;
    let mut v___x_6904_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6905_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6906_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6907_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6909_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6910_: u8 = 0;
    let mut v___x_6912_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6913_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6914_: u8 = 0;
    let mut v___x_6915_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6916_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_6917_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6919_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6920_: u8 = 0;
    let mut v___x_6922_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6923_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6924_: u8 = 0;
    let mut v___y_6926_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6927_: u8 = 0;
    let mut v___y_6928_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6929_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6930_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6931_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_only_6932_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6933_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6934_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6935_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6936_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6937_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6938_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6939_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6940_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6941_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6942_: u8 = 0;
    let mut v___x_6943_: u8 = 0;
    let mut v___x_6944_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6945_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6946_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6947_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6949_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6950_: u8 = 0;
    let mut v___x_6952_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6953_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6954_: u8 = 0;
    let mut v___x_6955_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6956_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6957_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6958_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6960_: u8 = 0;
    let mut v___y_6961_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6962_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6963_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_usedTheorems_6964_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6965_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6966_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6967_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6968_: u8 = 0;
    let mut v___x_6969_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6970_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6971_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6972_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6974_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6975_: u8 = 0;
    let mut v___x_6977_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6978_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6979_: u8 = 0;
    let mut v___x_6980_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6981_: u8 = 0;
    let mut v___x_6982_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6983_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6984_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6985_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6987_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6988_: u8 = 0;
    let mut v___x_6990_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6991_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6992_: u8 = 0;
    let mut v___x_6993_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6994_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6995_: u8 = 0;
    let mut v___x_6996_: u8 = 0;
    let mut v___x_6997_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6998_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6999_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_7000_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7002_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7003_: u8 = 0;
    let mut v___x_7005_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7006_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7007_: u8 = 0;
    let mut v___x_7008_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7009_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7010_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_7011_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7013_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7014_: u8 = 0;
    let mut v___x_7016_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7017_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7018_: u8 = 0;
    let mut v___y_7020_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7021_: u8 = 0;
    let mut v___y_7022_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_7023_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7025_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7026_: u8 = 0;
    let mut v___x_7027_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7029_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7030_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7031_: u8 = 0;
    let mut v___y_7033_: u8 = 0;
    let mut v___y_7034_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7035_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7036_: u8 = 0;
    let mut v___y_7038_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7039_: u8 = 0;
    let mut v___y_7040_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7041_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7042_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7043_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7044_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7045_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7046_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7047_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_7048_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7049_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_7050_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7051_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7052_: u8 = 0;
    let mut v_a_7053_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7055_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7056_: u8 = 0;
    let mut v___x_7058_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7059_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7060_: u8 = 0;
    let mut v___y_7062_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7063_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7064_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7065_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7066_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7067_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7068_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7069_: u8 = 0;
    let mut v___x_7070_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7071_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7072_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7073_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7074_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7075_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_7076_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ctx_7077_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_simprocs_7078_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_dischargeWrapper_7079_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ctx_7080_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_simprocs_7081_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_dischargeWrapper_7082_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ctx_7083_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_simprocs_7084_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_dischargeWrapper_7085_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7086_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_7087_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7089_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7090_: u8 = 0;
    let mut v___x_7092_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7093_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7094_: u8 = 0;
    let mut v___y_7096_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7097_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7098_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7099_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_7100_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7101_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7102_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7103_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7104_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7105_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7106_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7107_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7108_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7110_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7111_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7112_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_7113_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7114_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7115_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7116_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7117_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7118_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7119_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_7120_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7121_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7122_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_options_6475_ = crate::leanh::lean_ctor_get(v___y_6418_, 2);
                v_ref_6476_ = crate::leanh::lean_ctor_get(v___y_6418_, 5);
                v___x_6477_ = 0;
                v___x_6478_ = l_Lean_SourceInfo_fromRef(v_ref_6476_, v___x_6477_);
                v___x_6479_ = l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__7;
                crate::leanh::lean_inc_ref(v___x_6390_);
                crate::leanh::lean_inc_ref(v___x_6389_);
                crate::leanh::lean_inc_ref(v___x_6388_);
                v___x_6480_ =
                    l_Lean_Name_mkStr4(v___x_6388_, v___x_6389_, v___x_6390_, v___x_6479_);
                crate::leanh::lean_inc(v___x_6478_);
                v___x_6481_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_6481_, 0, v___x_6478_);
                crate::leanh::lean_ctor_set(v___x_6481_, 1, v___x_6479_);
                v___x_6482_ = l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__9;
                v___x_6483_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__10), core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__10_once), _init_l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__10);
                if crate::leanh::lean_obj_tag(v___y_6411_) == 0 {
                    v___x_7119_ = lean_mk_empty_array_with_capacity(v___x_6391_);
                    v___y_7110_ = v___x_7119_;
                    state = 60;
                    continue;
                } else {
                    v_val_7120_ = crate::leanh::lean_ctor_get(v___y_6411_, 0);
                    crate::leanh::lean_inc(v_val_7120_);
                    crate::leanh::lean_dec_ref_known(v___y_6411_, 1);
                    v___x_7121_ = lean_mk_empty_array_with_capacity(v___x_6391_);
                    v___x_7122_ = lean_array_push(v___x_7121_, v_val_7120_);
                    v___y_7110_ = v___x_7122_;
                    state = 60;
                    continue;
                }
            }
            1 => {
                v_diag_6423_ = crate::leanh::lean_ctor_get(v___y_6422_, 1);
                crate::leanh::lean_inc_ref(v_diag_6423_);
                crate::leanh::lean_dec_ref(v___y_6422_);
                v___x_6424_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_6424_, 0, v_diag_6423_);
                return v___x_6424_;
            }
            2 => {
                v___x_6431_ = l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__1;
                v___x_6432_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_6432_, 0, v___x_6431_);
                crate::leanh::lean_ctor_set(v___x_6432_, 1, v_stx_6427_);
                v___x_6433_ = crate::leanh::lean_box(0);
                v___x_6434_ = crate::leanh::lean_alloc_ctor(0, 6, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_6434_, 0, v___x_6432_);
                crate::leanh::lean_ctor_set(v___x_6434_, 1, v___x_6433_);
                crate::leanh::lean_ctor_set(v___x_6434_, 2, v___x_6433_);
                crate::leanh::lean_ctor_set(v___x_6434_, 3, v___x_6433_);
                crate::leanh::lean_ctor_set(v___x_6434_, 4, v___x_6433_);
                crate::leanh::lean_ctor_set(v___x_6434_, 5, v___x_6433_);
                v___x_6435_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_6435_, 0, v_ref_6429_);
                v___x_6436_ = l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__2;
                v___x_6437_ = 4;
                v___x_6438_ = l_Lean_MessageData_nil;
                v___x_6439_ = l_Lean_Meta_Tactic_TryThis_addSuggestion(
                    v_tk_6387_,
                    v___x_6434_,
                    v___x_6435_,
                    v___x_6436_,
                    v___x_6433_,
                    v___x_6437_,
                    v___x_6438_,
                    v___y_6428_,
                    v___y_6430_,
                );
                crate::leanh::lean_dec(v___y_6430_);
                crate::leanh::lean_dec_ref(v___y_6428_);
                if crate::leanh::lean_obj_tag(v___x_6439_) == 0 {
                    crate::leanh::lean_dec_ref_known(v___x_6439_, 1);
                    v___y_6422_ = v___y_6426_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_dec_ref(v___y_6426_);
                    v_a_6440_ = crate::leanh::lean_ctor_get(v___x_6439_, 0);
                    v_isSharedCheck_6447_ = (!crate::leanh::lean_is_exclusive(v___x_6439_)) as u8;
                    if v_isSharedCheck_6447_ == 0 {
                        v___x_6442_ = v___x_6439_;
                        v_isShared_6443_ = v_isSharedCheck_6447_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_6440_);
                        crate::leanh::lean_dec(v___x_6439_);
                        v___x_6442_ = crate::leanh::lean_box(0);
                        v_isShared_6443_ = v_isSharedCheck_6447_;
                        state = 3;
                        continue;
                    }
                }
            }
            3 => {
                if v_isShared_6443_ == 0 {
                    v___x_6445_ = v___x_6442_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_6446_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6446_, 0, v_a_6440_);
                    v___x_6445_ = v_reuseFailAlloc_6446_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_6445_;
            }
            5 => {
                v_ref_6453_ = crate::leanh::lean_ctor_get(v___y_6451_, 5);
                crate::leanh::lean_inc(v_ref_6453_);
                v___y_6426_ = v___y_6449_;
                v_stx_6427_ = v_stx_6450_;
                v___y_6428_ = v___y_6451_;
                v_ref_6429_ = v_ref_6453_;
                v___y_6430_ = v___y_6452_;
                state = 2;
                continue;
            }
            6 => {
                v___x_6464_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__6), core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__6_once), _init_l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__6);
                v___x_6465_ = l_panic___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__9(v___x_6464_, v___y_6456_, v___y_6457_, v___y_6458_, v___y_6459_, v___y_6460_, v___y_6461_, v___y_6462_, v___y_6463_);
                crate::leanh::lean_dec(v___y_6461_);
                crate::leanh::lean_dec_ref(v___y_6460_);
                crate::leanh::lean_dec(v___y_6459_);
                crate::leanh::lean_dec_ref(v___y_6458_);
                crate::leanh::lean_dec(v___y_6457_);
                crate::leanh::lean_dec_ref(v___y_6456_);
                if crate::leanh::lean_obj_tag(v___x_6465_) == 0 {
                    v_a_6466_ = crate::leanh::lean_ctor_get(v___x_6465_, 0);
                    crate::leanh::lean_inc(v_a_6466_);
                    crate::leanh::lean_dec_ref_known(v___x_6465_, 1);
                    v___y_6449_ = v___y_6455_;
                    v_stx_6450_ = v_a_6466_;
                    v___y_6451_ = v___y_6462_;
                    v___y_6452_ = v___y_6463_;
                    state = 5;
                    continue;
                } else {
                    crate::leanh::lean_dec(v___y_6463_);
                    crate::leanh::lean_dec_ref(v___y_6462_);
                    crate::leanh::lean_dec_ref(v___y_6455_);
                    crate::leanh::lean_dec(v_tk_6387_);
                    v_a_6467_ = crate::leanh::lean_ctor_get(v___x_6465_, 0);
                    v_isSharedCheck_6474_ = (!crate::leanh::lean_is_exclusive(v___x_6465_)) as u8;
                    if v_isSharedCheck_6474_ == 0 {
                        v___x_6469_ = v___x_6465_;
                        v_isShared_6470_ = v_isSharedCheck_6474_;
                        state = 7;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_6467_);
                        crate::leanh::lean_dec(v___x_6465_);
                        v___x_6469_ = crate::leanh::lean_box(0);
                        v_isShared_6470_ = v_isSharedCheck_6474_;
                        state = 7;
                        continue;
                    }
                }
            }
            7 => {
                if v_isShared_6470_ == 0 {
                    v___x_6472_ = v___x_6469_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_6473_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6473_, 0, v_a_6467_);
                    v___x_6472_ = v_reuseFailAlloc_6473_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_6472_;
            }
            9 => {
                v___x_6496_ = l_Array_append___redArg(v___x_6483_, v___y_6495_);
                crate::leanh::lean_dec_ref(v___y_6495_);
                crate::leanh::lean_inc_n(v___y_6486_, 2);
                v___x_6497_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_6497_, 0, v___y_6486_);
                crate::leanh::lean_ctor_set(v___x_6497_, 1, v___x_6482_);
                crate::leanh::lean_ctor_set(v___x_6497_, 2, v___x_6496_);
                v___x_6498_ = l_Lean_Syntax_node5(
                    v___y_6486_,
                    v___x_6393_,
                    v___y_6492_,
                    v___y_6491_,
                    v___y_6490_,
                    v___y_6488_,
                    v___x_6497_,
                );
                v___x_6499_ =
                    l_Lean_Syntax_node2(v___y_6486_, v___y_6494_, v___y_6493_, v___x_6498_);
                v___y_6449_ = v___y_6487_;
                v_stx_6450_ = v___x_6499_;
                v___y_6451_ = v___y_6489_;
                v___y_6452_ = v___y_6485_;
                state = 5;
                continue;
            }
            10 => {
                v___x_6512_ = l_Array_append___redArg(v___x_6483_, v___y_6511_);
                crate::leanh::lean_dec_ref(v___y_6511_);
                crate::leanh::lean_inc(v___y_6502_);
                v___x_6513_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_6513_, 0, v___y_6502_);
                crate::leanh::lean_ctor_set(v___x_6513_, 1, v___x_6482_);
                crate::leanh::lean_ctor_set(v___x_6513_, 2, v___x_6512_);
                if crate::leanh::lean_obj_tag(v___y_6505_) == 1 {
                    crate::leanh::lean_dec(v___x_6391_);
                    v_val_6514_ = crate::leanh::lean_ctor_get(v___y_6505_, 0);
                    crate::leanh::lean_inc(v_val_6514_);
                    crate::leanh::lean_dec_ref_known(v___y_6505_, 1);
                    v___x_6515_ = l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__11;
                    crate::leanh::lean_inc(v___y_6502_);
                    v___x_6516_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_6516_, 0, v___y_6502_);
                    crate::leanh::lean_ctor_set(v___x_6516_, 1, v___x_6515_);
                    v___x_6517_ = l_Array_mkArray2___redArg(v___x_6516_, v_val_6514_);
                    v___y_6485_ = v___y_6501_;
                    v___y_6486_ = v___y_6502_;
                    v___y_6487_ = v___y_6503_;
                    v___y_6488_ = v___x_6513_;
                    v___y_6489_ = v___y_6504_;
                    v___y_6490_ = v___y_6506_;
                    v___y_6491_ = v___y_6508_;
                    v___y_6492_ = v___y_6507_;
                    v___y_6493_ = v___y_6509_;
                    v___y_6494_ = v___y_6510_;
                    v___y_6495_ = v___x_6517_;
                    state = 9;
                    continue;
                } else {
                    crate::leanh::lean_dec(v___y_6505_);
                    v___x_6518_ = lean_mk_empty_array_with_capacity(v___x_6391_);
                    crate::leanh::lean_dec(v___x_6391_);
                    v___y_6485_ = v___y_6501_;
                    v___y_6486_ = v___y_6502_;
                    v___y_6487_ = v___y_6503_;
                    v___y_6488_ = v___x_6513_;
                    v___y_6489_ = v___y_6504_;
                    v___y_6490_ = v___y_6506_;
                    v___y_6491_ = v___y_6508_;
                    v___y_6492_ = v___y_6507_;
                    v___y_6493_ = v___y_6509_;
                    v___y_6494_ = v___y_6510_;
                    v___y_6495_ = v___x_6518_;
                    state = 9;
                    continue;
                }
            }
            11 => {
                v___x_6531_ = l_Array_append___redArg(v___x_6483_, v___y_6530_);
                crate::leanh::lean_dec_ref(v___y_6530_);
                crate::leanh::lean_inc(v___y_6522_);
                v___x_6532_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_6532_, 0, v___y_6522_);
                crate::leanh::lean_ctor_set(v___x_6532_, 1, v___x_6482_);
                crate::leanh::lean_ctor_set(v___x_6532_, 2, v___x_6531_);
                if crate::leanh::lean_obj_tag(v___y_6520_) == 1 {
                    v_val_6533_ = crate::leanh::lean_ctor_get(v___y_6520_, 0);
                    crate::leanh::lean_inc(v_val_6533_);
                    crate::leanh::lean_dec_ref_known(v___y_6520_, 1);
                    v___x_6534_ = l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__12;
                    v___x_6535_ =
                        l_Lean_Name_mkStr4(v___x_6388_, v___x_6389_, v___x_6390_, v___x_6534_);
                    v___x_6536_ = l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__13;
                    crate::leanh::lean_inc_n(v___y_6522_, 4);
                    v___x_6537_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_6537_, 0, v___y_6522_);
                    crate::leanh::lean_ctor_set(v___x_6537_, 1, v___x_6536_);
                    v___x_6538_ = l_Array_append___redArg(v___x_6483_, v_val_6533_);
                    crate::leanh::lean_dec(v_val_6533_);
                    v___x_6539_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_6539_, 0, v___y_6522_);
                    crate::leanh::lean_ctor_set(v___x_6539_, 1, v___x_6482_);
                    crate::leanh::lean_ctor_set(v___x_6539_, 2, v___x_6538_);
                    v___x_6540_ = l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__14;
                    v___x_6541_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_6541_, 0, v___y_6522_);
                    crate::leanh::lean_ctor_set(v___x_6541_, 1, v___x_6540_);
                    v___x_6542_ = l_Lean_Syntax_node3(
                        v___y_6522_,
                        v___x_6535_,
                        v___x_6537_,
                        v___x_6539_,
                        v___x_6541_,
                    );
                    v___x_6543_ = l_Array_mkArray1___redArg(v___x_6542_);
                    v___y_6501_ = v___y_6521_;
                    v___y_6502_ = v___y_6522_;
                    v___y_6503_ = v___y_6523_;
                    v___y_6504_ = v___y_6524_;
                    v___y_6505_ = v___y_6525_;
                    v___y_6506_ = v___x_6532_;
                    v___y_6507_ = v___y_6527_;
                    v___y_6508_ = v___y_6526_;
                    v___y_6509_ = v___y_6528_;
                    v___y_6510_ = v___y_6529_;
                    v___y_6511_ = v___x_6543_;
                    state = 10;
                    continue;
                } else {
                    crate::leanh::lean_dec(v___y_6520_);
                    crate::leanh::lean_dec_ref(v___x_6390_);
                    crate::leanh::lean_dec_ref(v___x_6389_);
                    crate::leanh::lean_dec_ref(v___x_6388_);
                    v___x_6544_ = lean_mk_empty_array_with_capacity(v___x_6391_);
                    v___y_6501_ = v___y_6521_;
                    v___y_6502_ = v___y_6522_;
                    v___y_6503_ = v___y_6523_;
                    v___y_6504_ = v___y_6524_;
                    v___y_6505_ = v___y_6525_;
                    v___y_6506_ = v___x_6532_;
                    v___y_6507_ = v___y_6527_;
                    v___y_6508_ = v___y_6526_;
                    v___y_6509_ = v___y_6528_;
                    v___y_6510_ = v___y_6529_;
                    v___y_6511_ = v___x_6544_;
                    state = 10;
                    continue;
                }
            }
            12 => {
                v___x_6557_ = l_Array_append___redArg(v___x_6483_, v___y_6556_);
                crate::leanh::lean_dec_ref(v___y_6556_);
                crate::leanh::lean_inc(v___y_6548_);
                v___x_6558_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_6558_, 0, v___y_6548_);
                crate::leanh::lean_ctor_set(v___x_6558_, 1, v___x_6482_);
                crate::leanh::lean_ctor_set(v___x_6558_, 2, v___x_6557_);
                if crate::leanh::lean_obj_tag(v___y_6553_) == 1 {
                    v_val_6559_ = crate::leanh::lean_ctor_get(v___y_6553_, 0);
                    crate::leanh::lean_inc(v_val_6559_);
                    crate::leanh::lean_dec_ref_known(v___y_6553_, 1);
                    v___x_6560_ = l_Lean_SourceInfo_fromRef(v_val_6559_, v___x_6392_);
                    crate::leanh::lean_dec(v_val_6559_);
                    v___x_6561_ = l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__15;
                    v___x_6562_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_6562_, 0, v___x_6560_);
                    crate::leanh::lean_ctor_set(v___x_6562_, 1, v___x_6561_);
                    v___x_6563_ = l_Array_mkArray1___redArg(v___x_6562_);
                    v___y_6520_ = v___y_6547_;
                    v___y_6521_ = v___y_6546_;
                    v___y_6522_ = v___y_6548_;
                    v___y_6523_ = v___y_6549_;
                    v___y_6524_ = v___y_6550_;
                    v___y_6525_ = v___y_6551_;
                    v___y_6526_ = v___x_6558_;
                    v___y_6527_ = v___y_6552_;
                    v___y_6528_ = v___y_6554_;
                    v___y_6529_ = v___y_6555_;
                    v___y_6530_ = v___x_6563_;
                    state = 11;
                    continue;
                } else {
                    crate::leanh::lean_dec(v___y_6553_);
                    v___x_6564_ = lean_mk_empty_array_with_capacity(v___x_6391_);
                    v___y_6520_ = v___y_6547_;
                    v___y_6521_ = v___y_6546_;
                    v___y_6522_ = v___y_6548_;
                    v___y_6523_ = v___y_6549_;
                    v___y_6524_ = v___y_6550_;
                    v___y_6525_ = v___y_6551_;
                    v___y_6526_ = v___x_6558_;
                    v___y_6527_ = v___y_6552_;
                    v___y_6528_ = v___y_6554_;
                    v___y_6529_ = v___y_6555_;
                    v___y_6530_ = v___x_6564_;
                    state = 11;
                    continue;
                }
            }
            13 => {
                v___x_6580_ = l_Array_append___redArg(v___x_6483_, v___y_6579_);
                crate::leanh::lean_dec_ref(v___y_6579_);
                crate::leanh::lean_inc_n(v___y_6577_, 3);
                v___x_6581_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_6581_, 0, v___y_6577_);
                crate::leanh::lean_ctor_set(v___x_6581_, 1, v___x_6482_);
                crate::leanh::lean_ctor_set(v___x_6581_, 2, v___x_6580_);
                v___x_6582_ = l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__16;
                v___x_6583_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_6583_, 0, v___y_6577_);
                crate::leanh::lean_ctor_set(v___x_6583_, 1, v___x_6582_);
                v___x_6584_ = l_Lean_Syntax_node6(
                    v___y_6577_,
                    v___y_6571_,
                    v___y_6576_,
                    v___y_6572_,
                    v___y_6573_,
                    v___x_6581_,
                    v___x_6583_,
                    v___y_6574_,
                );
                v___x_6585_ = l_Lean_Syntax_node4(
                    v___y_6577_,
                    v___y_6575_,
                    v___y_6570_,
                    v___y_6567_,
                    v___y_6578_,
                    v___x_6584_,
                );
                v___y_6449_ = v___y_6568_;
                v_stx_6450_ = v___x_6585_;
                v___y_6451_ = v___y_6569_;
                v___y_6452_ = v___y_6566_;
                state = 5;
                continue;
            }
            14 => {
                v___x_6601_ = l_Array_append___redArg(v___x_6483_, v___y_6600_);
                crate::leanh::lean_dec_ref(v___y_6600_);
                crate::leanh::lean_inc(v___y_6598_);
                v___x_6602_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_6602_, 0, v___y_6598_);
                crate::leanh::lean_ctor_set(v___x_6602_, 1, v___x_6482_);
                crate::leanh::lean_ctor_set(v___x_6602_, 2, v___x_6601_);
                if crate::leanh::lean_obj_tag(v___y_6592_) == 1 {
                    crate::leanh::lean_dec(v___x_6391_);
                    v_val_6603_ = crate::leanh::lean_ctor_get(v___y_6592_, 0);
                    crate::leanh::lean_inc(v_val_6603_);
                    crate::leanh::lean_dec_ref_known(v___y_6592_, 1);
                    v___x_6604_ = l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__12;
                    v___x_6605_ =
                        l_Lean_Name_mkStr4(v___x_6388_, v___x_6389_, v___x_6390_, v___x_6604_);
                    v___x_6606_ = l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__13;
                    crate::leanh::lean_inc_n(v___y_6598_, 4);
                    v___x_6607_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_6607_, 0, v___y_6598_);
                    crate::leanh::lean_ctor_set(v___x_6607_, 1, v___x_6606_);
                    v___x_6608_ = l_Array_append___redArg(v___x_6483_, v_val_6603_);
                    crate::leanh::lean_dec(v_val_6603_);
                    v___x_6609_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_6609_, 0, v___y_6598_);
                    crate::leanh::lean_ctor_set(v___x_6609_, 1, v___x_6482_);
                    crate::leanh::lean_ctor_set(v___x_6609_, 2, v___x_6608_);
                    v___x_6610_ = l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__14;
                    v___x_6611_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_6611_, 0, v___y_6598_);
                    crate::leanh::lean_ctor_set(v___x_6611_, 1, v___x_6610_);
                    v___x_6612_ = l_Lean_Syntax_node3(
                        v___y_6598_,
                        v___x_6605_,
                        v___x_6607_,
                        v___x_6609_,
                        v___x_6611_,
                    );
                    v___x_6613_ = l_Array_mkArray1___redArg(v___x_6612_);
                    v___y_6566_ = v___y_6587_;
                    v___y_6567_ = v___y_6588_;
                    v___y_6568_ = v___y_6589_;
                    v___y_6569_ = v___y_6590_;
                    v___y_6570_ = v___y_6591_;
                    v___y_6571_ = v___y_6593_;
                    v___y_6572_ = v___y_6594_;
                    v___y_6573_ = v___x_6602_;
                    v___y_6574_ = v___y_6595_;
                    v___y_6575_ = v___y_6596_;
                    v___y_6576_ = v___y_6597_;
                    v___y_6577_ = v___y_6598_;
                    v___y_6578_ = v___y_6599_;
                    v___y_6579_ = v___x_6613_;
                    state = 13;
                    continue;
                } else {
                    crate::leanh::lean_dec(v___y_6592_);
                    crate::leanh::lean_dec_ref(v___x_6390_);
                    crate::leanh::lean_dec_ref(v___x_6389_);
                    crate::leanh::lean_dec_ref(v___x_6388_);
                    v___x_6614_ = lean_mk_empty_array_with_capacity(v___x_6391_);
                    crate::leanh::lean_dec(v___x_6391_);
                    v___y_6566_ = v___y_6587_;
                    v___y_6567_ = v___y_6588_;
                    v___y_6568_ = v___y_6589_;
                    v___y_6569_ = v___y_6590_;
                    v___y_6570_ = v___y_6591_;
                    v___y_6571_ = v___y_6593_;
                    v___y_6572_ = v___y_6594_;
                    v___y_6573_ = v___x_6602_;
                    v___y_6574_ = v___y_6595_;
                    v___y_6575_ = v___y_6596_;
                    v___y_6576_ = v___y_6597_;
                    v___y_6577_ = v___y_6598_;
                    v___y_6578_ = v___y_6599_;
                    v___y_6579_ = v___x_6614_;
                    state = 13;
                    continue;
                }
            }
            15 => {
                v___x_6630_ = l_Array_append___redArg(v___x_6483_, v___y_6629_);
                crate::leanh::lean_dec_ref(v___y_6629_);
                crate::leanh::lean_inc(v___y_6626_);
                v___x_6631_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_6631_, 0, v___y_6626_);
                crate::leanh::lean_ctor_set(v___x_6631_, 1, v___x_6482_);
                crate::leanh::lean_ctor_set(v___x_6631_, 2, v___x_6630_);
                if crate::leanh::lean_obj_tag(v___y_6628_) == 1 {
                    v_val_6632_ = crate::leanh::lean_ctor_get(v___y_6628_, 0);
                    crate::leanh::lean_inc(v_val_6632_);
                    crate::leanh::lean_dec_ref_known(v___y_6628_, 1);
                    v___x_6633_ = l_Lean_SourceInfo_fromRef(v_val_6632_, v___x_6392_);
                    crate::leanh::lean_dec(v_val_6632_);
                    v___x_6634_ = l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__15;
                    v___x_6635_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_6635_, 0, v___x_6633_);
                    crate::leanh::lean_ctor_set(v___x_6635_, 1, v___x_6634_);
                    v___x_6636_ = l_Array_mkArray1___redArg(v___x_6635_);
                    v___y_6587_ = v___y_6616_;
                    v___y_6588_ = v___y_6617_;
                    v___y_6589_ = v___y_6618_;
                    v___y_6590_ = v___y_6619_;
                    v___y_6591_ = v___y_6620_;
                    v___y_6592_ = v___y_6621_;
                    v___y_6593_ = v___y_6622_;
                    v___y_6594_ = v___x_6631_;
                    v___y_6595_ = v___y_6623_;
                    v___y_6596_ = v___y_6624_;
                    v___y_6597_ = v___y_6625_;
                    v___y_6598_ = v___y_6626_;
                    v___y_6599_ = v___y_6627_;
                    v___y_6600_ = v___x_6636_;
                    state = 14;
                    continue;
                } else {
                    crate::leanh::lean_dec(v___y_6628_);
                    v___x_6637_ = lean_mk_empty_array_with_capacity(v___x_6391_);
                    v___y_6587_ = v___y_6616_;
                    v___y_6588_ = v___y_6617_;
                    v___y_6589_ = v___y_6618_;
                    v___y_6590_ = v___y_6619_;
                    v___y_6591_ = v___y_6620_;
                    v___y_6592_ = v___y_6621_;
                    v___y_6593_ = v___y_6622_;
                    v___y_6594_ = v___x_6631_;
                    v___y_6595_ = v___y_6623_;
                    v___y_6596_ = v___y_6624_;
                    v___y_6597_ = v___y_6625_;
                    v___y_6598_ = v___y_6626_;
                    v___y_6599_ = v___y_6627_;
                    v___y_6600_ = v___x_6637_;
                    state = 14;
                    continue;
                }
            }
            16 => {
                v___x_6650_ = l_Array_append___redArg(v___x_6483_, v___y_6649_);
                crate::leanh::lean_dec_ref(v___y_6649_);
                crate::leanh::lean_inc_n(v___y_6645_, 2);
                v___x_6651_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_6651_, 0, v___y_6645_);
                crate::leanh::lean_ctor_set(v___x_6651_, 1, v___x_6482_);
                crate::leanh::lean_ctor_set(v___x_6651_, 2, v___x_6650_);
                v___x_6652_ = l_Lean_Syntax_node5(
                    v___y_6645_,
                    v___x_6393_,
                    v___y_6647_,
                    v___y_6646_,
                    v___y_6640_,
                    v___y_6648_,
                    v___x_6651_,
                );
                crate::leanh::lean_inc(v___y_6641_);
                v___x_6653_ = l_Lean_Syntax_node4(
                    v___y_6645_,
                    v___x_6394_,
                    v___y_6644_,
                    v___y_6641_,
                    v___y_6641_,
                    v___x_6652_,
                );
                v___y_6449_ = v___y_6642_;
                v_stx_6450_ = v___x_6653_;
                v___y_6451_ = v___y_6643_;
                v___y_6452_ = v___y_6639_;
                state = 5;
                continue;
            }
            17 => {
                v___x_6666_ = l_Array_append___redArg(v___x_6483_, v___y_6665_);
                crate::leanh::lean_dec_ref(v___y_6665_);
                crate::leanh::lean_inc(v___y_6662_);
                v___x_6667_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_6667_, 0, v___y_6662_);
                crate::leanh::lean_ctor_set(v___x_6667_, 1, v___x_6482_);
                crate::leanh::lean_ctor_set(v___x_6667_, 2, v___x_6666_);
                if crate::leanh::lean_obj_tag(v___y_6660_) == 1 {
                    crate::leanh::lean_dec(v___x_6391_);
                    v_val_6668_ = crate::leanh::lean_ctor_get(v___y_6660_, 0);
                    crate::leanh::lean_inc(v_val_6668_);
                    crate::leanh::lean_dec_ref_known(v___y_6660_, 1);
                    v___x_6669_ = l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__11;
                    crate::leanh::lean_inc(v___y_6662_);
                    v___x_6670_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_6670_, 0, v___y_6662_);
                    crate::leanh::lean_ctor_set(v___x_6670_, 1, v___x_6669_);
                    v___x_6671_ = l_Array_mkArray2___redArg(v___x_6670_, v_val_6668_);
                    v___y_6639_ = v___y_6655_;
                    v___y_6640_ = v___y_6656_;
                    v___y_6641_ = v___y_6657_;
                    v___y_6642_ = v___y_6658_;
                    v___y_6643_ = v___y_6659_;
                    v___y_6644_ = v___y_6661_;
                    v___y_6645_ = v___y_6662_;
                    v___y_6646_ = v___y_6664_;
                    v___y_6647_ = v___y_6663_;
                    v___y_6648_ = v___x_6667_;
                    v___y_6649_ = v___x_6671_;
                    state = 16;
                    continue;
                } else {
                    crate::leanh::lean_dec(v___y_6660_);
                    v___x_6672_ = lean_mk_empty_array_with_capacity(v___x_6391_);
                    crate::leanh::lean_dec(v___x_6391_);
                    v___y_6639_ = v___y_6655_;
                    v___y_6640_ = v___y_6656_;
                    v___y_6641_ = v___y_6657_;
                    v___y_6642_ = v___y_6658_;
                    v___y_6643_ = v___y_6659_;
                    v___y_6644_ = v___y_6661_;
                    v___y_6645_ = v___y_6662_;
                    v___y_6646_ = v___y_6664_;
                    v___y_6647_ = v___y_6663_;
                    v___y_6648_ = v___x_6667_;
                    v___y_6649_ = v___x_6672_;
                    state = 16;
                    continue;
                }
            }
            18 => {
                v___x_6685_ = l_Array_append___redArg(v___x_6483_, v___y_6684_);
                crate::leanh::lean_dec_ref(v___y_6684_);
                crate::leanh::lean_inc(v___y_6681_);
                v___x_6686_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_6686_, 0, v___y_6681_);
                crate::leanh::lean_ctor_set(v___x_6686_, 1, v___x_6482_);
                crate::leanh::lean_ctor_set(v___x_6686_, 2, v___x_6685_);
                if crate::leanh::lean_obj_tag(v___y_6674_) == 1 {
                    v_val_6687_ = crate::leanh::lean_ctor_get(v___y_6674_, 0);
                    crate::leanh::lean_inc(v_val_6687_);
                    crate::leanh::lean_dec_ref_known(v___y_6674_, 1);
                    v___x_6688_ = l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__12;
                    v___x_6689_ =
                        l_Lean_Name_mkStr4(v___x_6388_, v___x_6389_, v___x_6390_, v___x_6688_);
                    v___x_6690_ = l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__13;
                    crate::leanh::lean_inc_n(v___y_6681_, 4);
                    v___x_6691_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_6691_, 0, v___y_6681_);
                    crate::leanh::lean_ctor_set(v___x_6691_, 1, v___x_6690_);
                    v___x_6692_ = l_Array_append___redArg(v___x_6483_, v_val_6687_);
                    crate::leanh::lean_dec(v_val_6687_);
                    v___x_6693_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_6693_, 0, v___y_6681_);
                    crate::leanh::lean_ctor_set(v___x_6693_, 1, v___x_6482_);
                    crate::leanh::lean_ctor_set(v___x_6693_, 2, v___x_6692_);
                    v___x_6694_ = l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__14;
                    v___x_6695_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_6695_, 0, v___y_6681_);
                    crate::leanh::lean_ctor_set(v___x_6695_, 1, v___x_6694_);
                    v___x_6696_ = l_Lean_Syntax_node3(
                        v___y_6681_,
                        v___x_6689_,
                        v___x_6691_,
                        v___x_6693_,
                        v___x_6695_,
                    );
                    v___x_6697_ = l_Array_mkArray1___redArg(v___x_6696_);
                    v___y_6655_ = v___y_6675_;
                    v___y_6656_ = v___x_6686_;
                    v___y_6657_ = v___y_6676_;
                    v___y_6658_ = v___y_6677_;
                    v___y_6659_ = v___y_6678_;
                    v___y_6660_ = v___y_6680_;
                    v___y_6661_ = v___y_6679_;
                    v___y_6662_ = v___y_6681_;
                    v___y_6663_ = v___y_6683_;
                    v___y_6664_ = v___y_6682_;
                    v___y_6665_ = v___x_6697_;
                    state = 17;
                    continue;
                } else {
                    crate::leanh::lean_dec(v___y_6674_);
                    crate::leanh::lean_dec_ref(v___x_6390_);
                    crate::leanh::lean_dec_ref(v___x_6389_);
                    crate::leanh::lean_dec_ref(v___x_6388_);
                    v___x_6698_ = lean_mk_empty_array_with_capacity(v___x_6391_);
                    v___y_6655_ = v___y_6675_;
                    v___y_6656_ = v___x_6686_;
                    v___y_6657_ = v___y_6676_;
                    v___y_6658_ = v___y_6677_;
                    v___y_6659_ = v___y_6678_;
                    v___y_6660_ = v___y_6680_;
                    v___y_6661_ = v___y_6679_;
                    v___y_6662_ = v___y_6681_;
                    v___y_6663_ = v___y_6683_;
                    v___y_6664_ = v___y_6682_;
                    v___y_6665_ = v___x_6698_;
                    state = 17;
                    continue;
                }
            }
            19 => {
                v___x_6711_ = l_Array_append___redArg(v___x_6483_, v___y_6710_);
                crate::leanh::lean_dec_ref(v___y_6710_);
                crate::leanh::lean_inc(v___y_6707_);
                v___x_6712_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_6712_, 0, v___y_6707_);
                crate::leanh::lean_ctor_set(v___x_6712_, 1, v___x_6482_);
                crate::leanh::lean_ctor_set(v___x_6712_, 2, v___x_6711_);
                if crate::leanh::lean_obj_tag(v___y_6709_) == 1 {
                    v_val_6713_ = crate::leanh::lean_ctor_get(v___y_6709_, 0);
                    crate::leanh::lean_inc(v_val_6713_);
                    crate::leanh::lean_dec_ref_known(v___y_6709_, 1);
                    v___x_6714_ = l_Lean_SourceInfo_fromRef(v_val_6713_, v___x_6392_);
                    crate::leanh::lean_dec(v_val_6713_);
                    v___x_6715_ = l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__15;
                    v___x_6716_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_6716_, 0, v___x_6714_);
                    crate::leanh::lean_ctor_set(v___x_6716_, 1, v___x_6715_);
                    v___x_6717_ = l_Array_mkArray1___redArg(v___x_6716_);
                    v___y_6674_ = v___y_6701_;
                    v___y_6675_ = v___y_6700_;
                    v___y_6676_ = v___y_6702_;
                    v___y_6677_ = v___y_6703_;
                    v___y_6678_ = v___y_6704_;
                    v___y_6679_ = v___y_6706_;
                    v___y_6680_ = v___y_6705_;
                    v___y_6681_ = v___y_6707_;
                    v___y_6682_ = v___x_6712_;
                    v___y_6683_ = v___y_6708_;
                    v___y_6684_ = v___x_6717_;
                    state = 18;
                    continue;
                } else {
                    crate::leanh::lean_dec(v___y_6709_);
                    v___x_6718_ = lean_mk_empty_array_with_capacity(v___x_6391_);
                    v___y_6674_ = v___y_6701_;
                    v___y_6675_ = v___y_6700_;
                    v___y_6676_ = v___y_6702_;
                    v___y_6677_ = v___y_6703_;
                    v___y_6678_ = v___y_6704_;
                    v___y_6679_ = v___y_6706_;
                    v___y_6680_ = v___y_6705_;
                    v___y_6681_ = v___y_6707_;
                    v___y_6682_ = v___x_6712_;
                    v___y_6683_ = v___y_6708_;
                    v___y_6684_ = v___x_6718_;
                    state = 18;
                    continue;
                }
            }
            20 => {
                v___x_6733_ = l_Array_append___redArg(v___x_6483_, v___y_6732_);
                crate::leanh::lean_dec_ref(v___y_6732_);
                crate::leanh::lean_inc_n(v___y_6730_, 3);
                v___x_6734_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_6734_, 0, v___y_6730_);
                crate::leanh::lean_ctor_set(v___x_6734_, 1, v___x_6482_);
                crate::leanh::lean_ctor_set(v___x_6734_, 2, v___x_6733_);
                v___x_6735_ = l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__16;
                v___x_6736_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_6736_, 0, v___y_6730_);
                crate::leanh::lean_ctor_set(v___x_6736_, 1, v___x_6735_);
                v___x_6737_ = l_Lean_Syntax_node6(
                    v___y_6730_,
                    v___y_6725_,
                    v___y_6729_,
                    v___y_6727_,
                    v___y_6728_,
                    v___x_6734_,
                    v___x_6736_,
                    v___y_6731_,
                );
                crate::leanh::lean_inc(v___y_6723_);
                v___x_6738_ = l_Lean_Syntax_node4(
                    v___y_6730_,
                    v___y_6724_,
                    v___y_6726_,
                    v___y_6723_,
                    v___y_6723_,
                    v___x_6737_,
                );
                v___y_6449_ = v___y_6721_;
                v_stx_6450_ = v___x_6738_;
                v___y_6451_ = v___y_6722_;
                v___y_6452_ = v___y_6720_;
                state = 5;
                continue;
            }
            21 => {
                v___x_6753_ = l_Array_append___redArg(v___x_6483_, v___y_6752_);
                crate::leanh::lean_dec_ref(v___y_6752_);
                crate::leanh::lean_inc(v___y_6750_);
                v___x_6754_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_6754_, 0, v___y_6750_);
                crate::leanh::lean_ctor_set(v___x_6754_, 1, v___x_6482_);
                crate::leanh::lean_ctor_set(v___x_6754_, 2, v___x_6753_);
                if crate::leanh::lean_obj_tag(v___y_6745_) == 1 {
                    crate::leanh::lean_dec(v___x_6391_);
                    v_val_6755_ = crate::leanh::lean_ctor_get(v___y_6745_, 0);
                    crate::leanh::lean_inc(v_val_6755_);
                    crate::leanh::lean_dec_ref_known(v___y_6745_, 1);
                    v___x_6756_ = l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__12;
                    v___x_6757_ =
                        l_Lean_Name_mkStr4(v___x_6388_, v___x_6389_, v___x_6390_, v___x_6756_);
                    v___x_6758_ = l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__13;
                    crate::leanh::lean_inc_n(v___y_6750_, 4);
                    v___x_6759_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_6759_, 0, v___y_6750_);
                    crate::leanh::lean_ctor_set(v___x_6759_, 1, v___x_6758_);
                    v___x_6760_ = l_Array_append___redArg(v___x_6483_, v_val_6755_);
                    crate::leanh::lean_dec(v_val_6755_);
                    v___x_6761_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_6761_, 0, v___y_6750_);
                    crate::leanh::lean_ctor_set(v___x_6761_, 1, v___x_6482_);
                    crate::leanh::lean_ctor_set(v___x_6761_, 2, v___x_6760_);
                    v___x_6762_ = l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__14;
                    v___x_6763_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_6763_, 0, v___y_6750_);
                    crate::leanh::lean_ctor_set(v___x_6763_, 1, v___x_6762_);
                    v___x_6764_ = l_Lean_Syntax_node3(
                        v___y_6750_,
                        v___x_6757_,
                        v___x_6759_,
                        v___x_6761_,
                        v___x_6763_,
                    );
                    v___x_6765_ = l_Array_mkArray1___redArg(v___x_6764_);
                    v___y_6720_ = v___y_6740_;
                    v___y_6721_ = v___y_6741_;
                    v___y_6722_ = v___y_6742_;
                    v___y_6723_ = v___y_6743_;
                    v___y_6724_ = v___y_6744_;
                    v___y_6725_ = v___y_6746_;
                    v___y_6726_ = v___y_6747_;
                    v___y_6727_ = v___y_6748_;
                    v___y_6728_ = v___x_6754_;
                    v___y_6729_ = v___y_6749_;
                    v___y_6730_ = v___y_6750_;
                    v___y_6731_ = v___y_6751_;
                    v___y_6732_ = v___x_6765_;
                    state = 20;
                    continue;
                } else {
                    crate::leanh::lean_dec(v___y_6745_);
                    crate::leanh::lean_dec_ref(v___x_6390_);
                    crate::leanh::lean_dec_ref(v___x_6389_);
                    crate::leanh::lean_dec_ref(v___x_6388_);
                    v___x_6766_ = lean_mk_empty_array_with_capacity(v___x_6391_);
                    crate::leanh::lean_dec(v___x_6391_);
                    v___y_6720_ = v___y_6740_;
                    v___y_6721_ = v___y_6741_;
                    v___y_6722_ = v___y_6742_;
                    v___y_6723_ = v___y_6743_;
                    v___y_6724_ = v___y_6744_;
                    v___y_6725_ = v___y_6746_;
                    v___y_6726_ = v___y_6747_;
                    v___y_6727_ = v___y_6748_;
                    v___y_6728_ = v___x_6754_;
                    v___y_6729_ = v___y_6749_;
                    v___y_6730_ = v___y_6750_;
                    v___y_6731_ = v___y_6751_;
                    v___y_6732_ = v___x_6766_;
                    state = 20;
                    continue;
                }
            }
            22 => {
                v___x_6781_ = l_Array_append___redArg(v___x_6483_, v___y_6780_);
                crate::leanh::lean_dec_ref(v___y_6780_);
                crate::leanh::lean_inc(v___y_6777_);
                v___x_6782_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_6782_, 0, v___y_6777_);
                crate::leanh::lean_ctor_set(v___x_6782_, 1, v___x_6482_);
                crate::leanh::lean_ctor_set(v___x_6782_, 2, v___x_6781_);
                if crate::leanh::lean_obj_tag(v___y_6779_) == 1 {
                    v_val_6783_ = crate::leanh::lean_ctor_get(v___y_6779_, 0);
                    crate::leanh::lean_inc(v_val_6783_);
                    crate::leanh::lean_dec_ref_known(v___y_6779_, 1);
                    v___x_6784_ = l_Lean_SourceInfo_fromRef(v_val_6783_, v___x_6392_);
                    crate::leanh::lean_dec(v_val_6783_);
                    v___x_6785_ = l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__15;
                    v___x_6786_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_6786_, 0, v___x_6784_);
                    crate::leanh::lean_ctor_set(v___x_6786_, 1, v___x_6785_);
                    v___x_6787_ = l_Array_mkArray1___redArg(v___x_6786_);
                    v___y_6740_ = v___y_6768_;
                    v___y_6741_ = v___y_6769_;
                    v___y_6742_ = v___y_6770_;
                    v___y_6743_ = v___y_6771_;
                    v___y_6744_ = v___y_6772_;
                    v___y_6745_ = v___y_6773_;
                    v___y_6746_ = v___y_6774_;
                    v___y_6747_ = v___y_6775_;
                    v___y_6748_ = v___x_6782_;
                    v___y_6749_ = v___y_6776_;
                    v___y_6750_ = v___y_6777_;
                    v___y_6751_ = v___y_6778_;
                    v___y_6752_ = v___x_6787_;
                    state = 21;
                    continue;
                } else {
                    crate::leanh::lean_dec(v___y_6779_);
                    v___x_6788_ = lean_mk_empty_array_with_capacity(v___x_6391_);
                    v___y_6740_ = v___y_6768_;
                    v___y_6741_ = v___y_6769_;
                    v___y_6742_ = v___y_6770_;
                    v___y_6743_ = v___y_6771_;
                    v___y_6744_ = v___y_6772_;
                    v___y_6745_ = v___y_6773_;
                    v___y_6746_ = v___y_6774_;
                    v___y_6747_ = v___y_6775_;
                    v___y_6748_ = v___x_6782_;
                    v___y_6749_ = v___y_6776_;
                    v___y_6750_ = v___y_6777_;
                    v___y_6751_ = v___y_6778_;
                    v___y_6752_ = v___x_6788_;
                    state = 21;
                    continue;
                }
            }
            23 => {
                if v___y_6800_ == 0 {
                    if v_useReducible_6395_ == 0 {
                        crate::leanh::lean_dec(v___x_6394_);
                        crate::leanh::lean_dec(v___x_6393_);
                        if crate::leanh::lean_obj_tag(v___y_6793_) == 0 {
                            crate::leanh::lean_dec(v___y_6804_);
                            crate::leanh::lean_dec(v___y_6802_);
                            crate::leanh::lean_dec(v___y_6801_);
                            crate::leanh::lean_dec(v___y_6798_);
                            crate::leanh::lean_dec_ref(v___x_6397_);
                            crate::leanh::lean_dec_ref(v___f_6396_);
                            crate::leanh::lean_dec(v___x_6391_);
                            crate::leanh::lean_dec_ref(v___x_6390_);
                            crate::leanh::lean_dec_ref(v___x_6389_);
                            crate::leanh::lean_dec_ref(v___x_6388_);
                            v___y_6455_ = v___y_6791_;
                            v___y_6456_ = v___y_6796_;
                            v___y_6457_ = v___y_6799_;
                            v___y_6458_ = v___y_6794_;
                            v___y_6459_ = v___y_6803_;
                            v___y_6460_ = v___y_6797_;
                            v___y_6461_ = v___y_6795_;
                            v___y_6462_ = v___y_6792_;
                            v___y_6463_ = v___y_6790_;
                            state = 6;
                            continue;
                        } else {
                            v_val_6805_ = crate::leanh::lean_ctor_get(v___y_6793_, 0);
                            crate::leanh::lean_inc(v_val_6805_);
                            crate::leanh::lean_dec_ref_known(v___y_6793_, 1);
                            crate::leanh::lean_inc(v___y_6790_);
                            crate::leanh::lean_inc_ref(v___y_6792_);
                            v___x_6806_ = crate::leanh::lean_apply_9(
                                v___f_6396_,
                                v___y_6796_,
                                v___y_6799_,
                                v___y_6794_,
                                v___y_6803_,
                                v___y_6797_,
                                v___y_6795_,
                                v___y_6792_,
                                v___y_6790_,
                                crate::leanh::lean_box(0),
                            );
                            if crate::leanh::lean_obj_tag(v___x_6806_) == 0 {
                                v_a_6807_ = crate::leanh::lean_ctor_get(v___x_6806_, 0);
                                crate::leanh::lean_inc_n(v_a_6807_, 3);
                                crate::leanh::lean_dec_ref_known(v___x_6806_, 1);
                                v___x_6808_ = l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__17;
                                crate::leanh::lean_inc_ref_n(v___x_6390_, 2);
                                crate::leanh::lean_inc_ref_n(v___x_6389_, 2);
                                crate::leanh::lean_inc_ref_n(v___x_6388_, 2);
                                v___x_6809_ = l_Lean_Name_mkStr4(
                                    v___x_6388_,
                                    v___x_6389_,
                                    v___x_6390_,
                                    v___x_6808_,
                                );
                                v___x_6810_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                                crate::leanh::lean_ctor_set(v___x_6810_, 0, v_a_6807_);
                                crate::leanh::lean_ctor_set(v___x_6810_, 1, v___x_6397_);
                                v___x_6811_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                                crate::leanh::lean_ctor_set(v___x_6811_, 0, v_a_6807_);
                                crate::leanh::lean_ctor_set(v___x_6811_, 1, v___x_6482_);
                                crate::leanh::lean_ctor_set(v___x_6811_, 2, v___x_6483_);
                                v___x_6812_ = l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__18;
                                v___x_6813_ = l_Lean_Name_mkStr4(
                                    v___x_6388_,
                                    v___x_6389_,
                                    v___x_6390_,
                                    v___x_6812_,
                                );
                                if crate::leanh::lean_obj_tag(v___y_6804_) == 0 {
                                    v___x_6814_ = lean_mk_empty_array_with_capacity(v___x_6391_);
                                    v___y_6768_ = v___y_6790_;
                                    v___y_6769_ = v___y_6791_;
                                    v___y_6770_ = v___y_6792_;
                                    v___y_6771_ = v___x_6811_;
                                    v___y_6772_ = v___x_6809_;
                                    v___y_6773_ = v___y_6798_;
                                    v___y_6774_ = v___x_6813_;
                                    v___y_6775_ = v___x_6810_;
                                    v___y_6776_ = v___y_6801_;
                                    v___y_6777_ = v_a_6807_;
                                    v___y_6778_ = v_val_6805_;
                                    v___y_6779_ = v___y_6802_;
                                    v___y_6780_ = v___x_6814_;
                                    state = 22;
                                    continue;
                                } else {
                                    v_val_6815_ = crate::leanh::lean_ctor_get(v___y_6804_, 0);
                                    crate::leanh::lean_inc(v_val_6815_);
                                    crate::leanh::lean_dec_ref_known(v___y_6804_, 1);
                                    v___x_6816_ = lean_mk_empty_array_with_capacity(v___x_6391_);
                                    v___x_6817_ = lean_array_push(v___x_6816_, v_val_6815_);
                                    v___y_6768_ = v___y_6790_;
                                    v___y_6769_ = v___y_6791_;
                                    v___y_6770_ = v___y_6792_;
                                    v___y_6771_ = v___x_6811_;
                                    v___y_6772_ = v___x_6809_;
                                    v___y_6773_ = v___y_6798_;
                                    v___y_6774_ = v___x_6813_;
                                    v___y_6775_ = v___x_6810_;
                                    v___y_6776_ = v___y_6801_;
                                    v___y_6777_ = v_a_6807_;
                                    v___y_6778_ = v_val_6805_;
                                    v___y_6779_ = v___y_6802_;
                                    v___y_6780_ = v___x_6817_;
                                    state = 22;
                                    continue;
                                }
                            } else {
                                crate::leanh::lean_dec(v_val_6805_);
                                crate::leanh::lean_dec(v___y_6804_);
                                crate::leanh::lean_dec(v___y_6802_);
                                crate::leanh::lean_dec(v___y_6801_);
                                crate::leanh::lean_dec(v___y_6798_);
                                crate::leanh::lean_dec_ref(v___y_6792_);
                                crate::leanh::lean_dec_ref(v___y_6791_);
                                crate::leanh::lean_dec(v___y_6790_);
                                crate::leanh::lean_dec_ref(v___x_6397_);
                                crate::leanh::lean_dec(v___x_6391_);
                                crate::leanh::lean_dec_ref(v___x_6390_);
                                crate::leanh::lean_dec_ref(v___x_6389_);
                                crate::leanh::lean_dec_ref(v___x_6388_);
                                crate::leanh::lean_dec(v_tk_6387_);
                                v_a_6818_ = crate::leanh::lean_ctor_get(v___x_6806_, 0);
                                v_isSharedCheck_6825_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_6806_)) as u8;
                                if v_isSharedCheck_6825_ == 0 {
                                    v___x_6820_ = v___x_6806_;
                                    v_isShared_6821_ = v_isSharedCheck_6825_;
                                    state = 24;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_a_6818_);
                                    crate::leanh::lean_dec(v___x_6806_);
                                    v___x_6820_ = crate::leanh::lean_box(0);
                                    v_isShared_6821_ = v_isSharedCheck_6825_;
                                    state = 24;
                                    continue;
                                }
                            }
                        }
                    } else {
                        crate::leanh::lean_inc(v___y_6790_);
                        crate::leanh::lean_inc_ref(v___y_6792_);
                        v___x_6826_ = crate::leanh::lean_apply_9(
                            v___f_6396_,
                            v___y_6796_,
                            v___y_6799_,
                            v___y_6794_,
                            v___y_6803_,
                            v___y_6797_,
                            v___y_6795_,
                            v___y_6792_,
                            v___y_6790_,
                            crate::leanh::lean_box(0),
                        );
                        if crate::leanh::lean_obj_tag(v___x_6826_) == 0 {
                            v_a_6827_ = crate::leanh::lean_ctor_get(v___x_6826_, 0);
                            crate::leanh::lean_inc_n(v_a_6827_, 3);
                            crate::leanh::lean_dec_ref_known(v___x_6826_, 1);
                            v___x_6828_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_6828_, 0, v_a_6827_);
                            crate::leanh::lean_ctor_set(v___x_6828_, 1, v___x_6397_);
                            v___x_6829_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_6829_, 0, v_a_6827_);
                            crate::leanh::lean_ctor_set(v___x_6829_, 1, v___x_6482_);
                            crate::leanh::lean_ctor_set(v___x_6829_, 2, v___x_6483_);
                            if crate::leanh::lean_obj_tag(v___y_6804_) == 0 {
                                v___x_6830_ = lean_mk_empty_array_with_capacity(v___x_6391_);
                                v___y_6700_ = v___y_6790_;
                                v___y_6701_ = v___y_6798_;
                                v___y_6702_ = v___x_6829_;
                                v___y_6703_ = v___y_6791_;
                                v___y_6704_ = v___y_6792_;
                                v___y_6705_ = v___y_6793_;
                                v___y_6706_ = v___x_6828_;
                                v___y_6707_ = v_a_6827_;
                                v___y_6708_ = v___y_6801_;
                                v___y_6709_ = v___y_6802_;
                                v___y_6710_ = v___x_6830_;
                                state = 19;
                                continue;
                            } else {
                                v_val_6831_ = crate::leanh::lean_ctor_get(v___y_6804_, 0);
                                crate::leanh::lean_inc(v_val_6831_);
                                crate::leanh::lean_dec_ref_known(v___y_6804_, 1);
                                v___x_6832_ = lean_mk_empty_array_with_capacity(v___x_6391_);
                                v___x_6833_ = lean_array_push(v___x_6832_, v_val_6831_);
                                v___y_6700_ = v___y_6790_;
                                v___y_6701_ = v___y_6798_;
                                v___y_6702_ = v___x_6829_;
                                v___y_6703_ = v___y_6791_;
                                v___y_6704_ = v___y_6792_;
                                v___y_6705_ = v___y_6793_;
                                v___y_6706_ = v___x_6828_;
                                v___y_6707_ = v_a_6827_;
                                v___y_6708_ = v___y_6801_;
                                v___y_6709_ = v___y_6802_;
                                v___y_6710_ = v___x_6833_;
                                state = 19;
                                continue;
                            }
                        } else {
                            crate::leanh::lean_dec(v___y_6804_);
                            crate::leanh::lean_dec(v___y_6802_);
                            crate::leanh::lean_dec(v___y_6801_);
                            crate::leanh::lean_dec(v___y_6798_);
                            crate::leanh::lean_dec(v___y_6793_);
                            crate::leanh::lean_dec_ref(v___y_6792_);
                            crate::leanh::lean_dec_ref(v___y_6791_);
                            crate::leanh::lean_dec(v___y_6790_);
                            crate::leanh::lean_dec_ref(v___x_6397_);
                            crate::leanh::lean_dec(v___x_6394_);
                            crate::leanh::lean_dec(v___x_6393_);
                            crate::leanh::lean_dec(v___x_6391_);
                            crate::leanh::lean_dec_ref(v___x_6390_);
                            crate::leanh::lean_dec_ref(v___x_6389_);
                            crate::leanh::lean_dec_ref(v___x_6388_);
                            crate::leanh::lean_dec(v_tk_6387_);
                            v_a_6834_ = crate::leanh::lean_ctor_get(v___x_6826_, 0);
                            v_isSharedCheck_6841_ =
                                (!crate::leanh::lean_is_exclusive(v___x_6826_)) as u8;
                            if v_isSharedCheck_6841_ == 0 {
                                v___x_6836_ = v___x_6826_;
                                v_isShared_6837_ = v_isSharedCheck_6841_;
                                state = 26;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_6834_);
                                crate::leanh::lean_dec(v___x_6826_);
                                v___x_6836_ = crate::leanh::lean_box(0);
                                v_isShared_6837_ = v_isSharedCheck_6841_;
                                state = 26;
                                continue;
                            }
                        }
                    }
                } else {
                    crate::leanh::lean_dec(v___x_6394_);
                    if v_useReducible_6395_ == 0 {
                        crate::leanh::lean_dec(v___x_6393_);
                        if crate::leanh::lean_obj_tag(v___y_6793_) == 0 {
                            crate::leanh::lean_dec(v___y_6804_);
                            crate::leanh::lean_dec(v___y_6802_);
                            crate::leanh::lean_dec(v___y_6801_);
                            crate::leanh::lean_dec(v___y_6798_);
                            crate::leanh::lean_dec_ref(v___x_6397_);
                            crate::leanh::lean_dec_ref(v___f_6396_);
                            crate::leanh::lean_dec(v___x_6391_);
                            crate::leanh::lean_dec_ref(v___x_6390_);
                            crate::leanh::lean_dec_ref(v___x_6389_);
                            crate::leanh::lean_dec_ref(v___x_6388_);
                            v___y_6455_ = v___y_6791_;
                            v___y_6456_ = v___y_6796_;
                            v___y_6457_ = v___y_6799_;
                            v___y_6458_ = v___y_6794_;
                            v___y_6459_ = v___y_6803_;
                            v___y_6460_ = v___y_6797_;
                            v___y_6461_ = v___y_6795_;
                            v___y_6462_ = v___y_6792_;
                            v___y_6463_ = v___y_6790_;
                            state = 6;
                            continue;
                        } else {
                            v_val_6842_ = crate::leanh::lean_ctor_get(v___y_6793_, 0);
                            crate::leanh::lean_inc(v_val_6842_);
                            crate::leanh::lean_dec_ref_known(v___y_6793_, 1);
                            crate::leanh::lean_inc(v___y_6790_);
                            crate::leanh::lean_inc_ref(v___y_6792_);
                            v___x_6843_ = crate::leanh::lean_apply_9(
                                v___f_6396_,
                                v___y_6796_,
                                v___y_6799_,
                                v___y_6794_,
                                v___y_6803_,
                                v___y_6797_,
                                v___y_6795_,
                                v___y_6792_,
                                v___y_6790_,
                                crate::leanh::lean_box(0),
                            );
                            if crate::leanh::lean_obj_tag(v___x_6843_) == 0 {
                                v_a_6844_ = crate::leanh::lean_ctor_get(v___x_6843_, 0);
                                crate::leanh::lean_inc_n(v_a_6844_, 5);
                                crate::leanh::lean_dec_ref_known(v___x_6843_, 1);
                                v___x_6845_ = l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__17;
                                crate::leanh::lean_inc_ref_n(v___x_6390_, 2);
                                crate::leanh::lean_inc_ref_n(v___x_6389_, 2);
                                crate::leanh::lean_inc_ref_n(v___x_6388_, 2);
                                v___x_6846_ = l_Lean_Name_mkStr4(
                                    v___x_6388_,
                                    v___x_6389_,
                                    v___x_6390_,
                                    v___x_6845_,
                                );
                                v___x_6847_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                                crate::leanh::lean_ctor_set(v___x_6847_, 0, v_a_6844_);
                                crate::leanh::lean_ctor_set(v___x_6847_, 1, v___x_6397_);
                                v___x_6848_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                                crate::leanh::lean_ctor_set(v___x_6848_, 0, v_a_6844_);
                                crate::leanh::lean_ctor_set(v___x_6848_, 1, v___x_6482_);
                                crate::leanh::lean_ctor_set(v___x_6848_, 2, v___x_6483_);
                                v___x_6849_ = l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__19;
                                v___x_6850_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                                crate::leanh::lean_ctor_set(v___x_6850_, 0, v_a_6844_);
                                crate::leanh::lean_ctor_set(v___x_6850_, 1, v___x_6849_);
                                v___x_6851_ =
                                    l_Lean_Syntax_node1(v_a_6844_, v___x_6482_, v___x_6850_);
                                v___x_6852_ = l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__18;
                                v___x_6853_ = l_Lean_Name_mkStr4(
                                    v___x_6388_,
                                    v___x_6389_,
                                    v___x_6390_,
                                    v___x_6852_,
                                );
                                if crate::leanh::lean_obj_tag(v___y_6804_) == 0 {
                                    v___x_6854_ = lean_mk_empty_array_with_capacity(v___x_6391_);
                                    v___y_6616_ = v___y_6790_;
                                    v___y_6617_ = v___x_6848_;
                                    v___y_6618_ = v___y_6791_;
                                    v___y_6619_ = v___y_6792_;
                                    v___y_6620_ = v___x_6847_;
                                    v___y_6621_ = v___y_6798_;
                                    v___y_6622_ = v___x_6853_;
                                    v___y_6623_ = v_val_6842_;
                                    v___y_6624_ = v___x_6846_;
                                    v___y_6625_ = v___y_6801_;
                                    v___y_6626_ = v_a_6844_;
                                    v___y_6627_ = v___x_6851_;
                                    v___y_6628_ = v___y_6802_;
                                    v___y_6629_ = v___x_6854_;
                                    state = 15;
                                    continue;
                                } else {
                                    v_val_6855_ = crate::leanh::lean_ctor_get(v___y_6804_, 0);
                                    crate::leanh::lean_inc(v_val_6855_);
                                    crate::leanh::lean_dec_ref_known(v___y_6804_, 1);
                                    v___x_6856_ = lean_mk_empty_array_with_capacity(v___x_6391_);
                                    v___x_6857_ = lean_array_push(v___x_6856_, v_val_6855_);
                                    v___y_6616_ = v___y_6790_;
                                    v___y_6617_ = v___x_6848_;
                                    v___y_6618_ = v___y_6791_;
                                    v___y_6619_ = v___y_6792_;
                                    v___y_6620_ = v___x_6847_;
                                    v___y_6621_ = v___y_6798_;
                                    v___y_6622_ = v___x_6853_;
                                    v___y_6623_ = v_val_6842_;
                                    v___y_6624_ = v___x_6846_;
                                    v___y_6625_ = v___y_6801_;
                                    v___y_6626_ = v_a_6844_;
                                    v___y_6627_ = v___x_6851_;
                                    v___y_6628_ = v___y_6802_;
                                    v___y_6629_ = v___x_6857_;
                                    state = 15;
                                    continue;
                                }
                            } else {
                                crate::leanh::lean_dec(v_val_6842_);
                                crate::leanh::lean_dec(v___y_6804_);
                                crate::leanh::lean_dec(v___y_6802_);
                                crate::leanh::lean_dec(v___y_6801_);
                                crate::leanh::lean_dec(v___y_6798_);
                                crate::leanh::lean_dec_ref(v___y_6792_);
                                crate::leanh::lean_dec_ref(v___y_6791_);
                                crate::leanh::lean_dec(v___y_6790_);
                                crate::leanh::lean_dec_ref(v___x_6397_);
                                crate::leanh::lean_dec(v___x_6391_);
                                crate::leanh::lean_dec_ref(v___x_6390_);
                                crate::leanh::lean_dec_ref(v___x_6389_);
                                crate::leanh::lean_dec_ref(v___x_6388_);
                                crate::leanh::lean_dec(v_tk_6387_);
                                v_a_6858_ = crate::leanh::lean_ctor_get(v___x_6843_, 0);
                                v_isSharedCheck_6865_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_6843_)) as u8;
                                if v_isSharedCheck_6865_ == 0 {
                                    v___x_6860_ = v___x_6843_;
                                    v_isShared_6861_ = v_isSharedCheck_6865_;
                                    state = 28;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_a_6858_);
                                    crate::leanh::lean_dec(v___x_6843_);
                                    v___x_6860_ = crate::leanh::lean_box(0);
                                    v_isShared_6861_ = v_isSharedCheck_6865_;
                                    state = 28;
                                    continue;
                                }
                            }
                        }
                    } else {
                        crate::leanh::lean_dec_ref(v___x_6397_);
                        crate::leanh::lean_inc(v___y_6790_);
                        crate::leanh::lean_inc_ref(v___y_6792_);
                        v___x_6866_ = crate::leanh::lean_apply_9(
                            v___f_6396_,
                            v___y_6796_,
                            v___y_6799_,
                            v___y_6794_,
                            v___y_6803_,
                            v___y_6797_,
                            v___y_6795_,
                            v___y_6792_,
                            v___y_6790_,
                            crate::leanh::lean_box(0),
                        );
                        if crate::leanh::lean_obj_tag(v___x_6866_) == 0 {
                            v_a_6867_ = crate::leanh::lean_ctor_get(v___x_6866_, 0);
                            crate::leanh::lean_inc_n(v_a_6867_, 2);
                            crate::leanh::lean_dec_ref_known(v___x_6866_, 1);
                            v___x_6868_ = l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__20;
                            crate::leanh::lean_inc_ref(v___x_6390_);
                            crate::leanh::lean_inc_ref(v___x_6389_);
                            crate::leanh::lean_inc_ref(v___x_6388_);
                            v___x_6869_ = l_Lean_Name_mkStr4(
                                v___x_6388_,
                                v___x_6389_,
                                v___x_6390_,
                                v___x_6868_,
                            );
                            v___x_6870_ = l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__21;
                            v___x_6871_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_6871_, 0, v_a_6867_);
                            crate::leanh::lean_ctor_set(v___x_6871_, 1, v___x_6870_);
                            if crate::leanh::lean_obj_tag(v___y_6804_) == 0 {
                                v___x_6872_ = lean_mk_empty_array_with_capacity(v___x_6391_);
                                v___y_6546_ = v___y_6790_;
                                v___y_6547_ = v___y_6798_;
                                v___y_6548_ = v_a_6867_;
                                v___y_6549_ = v___y_6791_;
                                v___y_6550_ = v___y_6792_;
                                v___y_6551_ = v___y_6793_;
                                v___y_6552_ = v___y_6801_;
                                v___y_6553_ = v___y_6802_;
                                v___y_6554_ = v___x_6871_;
                                v___y_6555_ = v___x_6869_;
                                v___y_6556_ = v___x_6872_;
                                state = 12;
                                continue;
                            } else {
                                v_val_6873_ = crate::leanh::lean_ctor_get(v___y_6804_, 0);
                                crate::leanh::lean_inc(v_val_6873_);
                                crate::leanh::lean_dec_ref_known(v___y_6804_, 1);
                                v___x_6874_ = lean_mk_empty_array_with_capacity(v___x_6391_);
                                v___x_6875_ = lean_array_push(v___x_6874_, v_val_6873_);
                                v___y_6546_ = v___y_6790_;
                                v___y_6547_ = v___y_6798_;
                                v___y_6548_ = v_a_6867_;
                                v___y_6549_ = v___y_6791_;
                                v___y_6550_ = v___y_6792_;
                                v___y_6551_ = v___y_6793_;
                                v___y_6552_ = v___y_6801_;
                                v___y_6553_ = v___y_6802_;
                                v___y_6554_ = v___x_6871_;
                                v___y_6555_ = v___x_6869_;
                                v___y_6556_ = v___x_6875_;
                                state = 12;
                                continue;
                            }
                        } else {
                            crate::leanh::lean_dec(v___y_6804_);
                            crate::leanh::lean_dec(v___y_6802_);
                            crate::leanh::lean_dec(v___y_6801_);
                            crate::leanh::lean_dec(v___y_6798_);
                            crate::leanh::lean_dec(v___y_6793_);
                            crate::leanh::lean_dec_ref(v___y_6792_);
                            crate::leanh::lean_dec_ref(v___y_6791_);
                            crate::leanh::lean_dec(v___y_6790_);
                            crate::leanh::lean_dec(v___x_6393_);
                            crate::leanh::lean_dec(v___x_6391_);
                            crate::leanh::lean_dec_ref(v___x_6390_);
                            crate::leanh::lean_dec_ref(v___x_6389_);
                            crate::leanh::lean_dec_ref(v___x_6388_);
                            crate::leanh::lean_dec(v_tk_6387_);
                            v_a_6876_ = crate::leanh::lean_ctor_get(v___x_6866_, 0);
                            v_isSharedCheck_6883_ =
                                (!crate::leanh::lean_is_exclusive(v___x_6866_)) as u8;
                            if v_isSharedCheck_6883_ == 0 {
                                v___x_6878_ = v___x_6866_;
                                v_isShared_6879_ = v_isSharedCheck_6883_;
                                state = 30;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_6876_);
                                crate::leanh::lean_dec(v___x_6866_);
                                v___x_6878_ = crate::leanh::lean_box(0);
                                v_isShared_6879_ = v_isSharedCheck_6883_;
                                state = 30;
                                continue;
                            }
                        }
                    }
                }
            }
            24 => {
                if v_isShared_6821_ == 0 {
                    v___x_6823_ = v___x_6820_;
                    state = 25;
                    continue;
                } else {
                    v_reuseFailAlloc_6824_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6824_, 0, v_a_6818_);
                    v___x_6823_ = v_reuseFailAlloc_6824_;
                    state = 25;
                    continue;
                }
            }
            25 => {
                return v___x_6823_;
            }
            26 => {
                if v_isShared_6837_ == 0 {
                    v___x_6839_ = v___x_6836_;
                    state = 27;
                    continue;
                } else {
                    v_reuseFailAlloc_6840_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6840_, 0, v_a_6834_);
                    v___x_6839_ = v_reuseFailAlloc_6840_;
                    state = 27;
                    continue;
                }
            }
            27 => {
                return v___x_6839_;
            }
            28 => {
                if v_isShared_6861_ == 0 {
                    v___x_6863_ = v___x_6860_;
                    state = 29;
                    continue;
                } else {
                    v_reuseFailAlloc_6864_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6864_, 0, v_a_6858_);
                    v___x_6863_ = v_reuseFailAlloc_6864_;
                    state = 29;
                    continue;
                }
            }
            29 => {
                return v___x_6863_;
            }
            30 => {
                if v_isShared_6879_ == 0 {
                    v___x_6881_ = v___x_6878_;
                    state = 31;
                    continue;
                } else {
                    v_reuseFailAlloc_6882_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6882_, 0, v_a_6876_);
                    v___x_6881_ = v_reuseFailAlloc_6882_;
                    state = 31;
                    continue;
                }
            }
            31 => {
                return v___x_6881_;
            }
            32 => {
                v___x_6901_ = crate::leanh::lean_unsigned_to_nat(5);
                v___x_6902_ = l_Lean_Syntax_getArg(v___y_6888_, v___x_6901_);
                crate::leanh::lean_dec(v___y_6888_);
                v___x_6903_ = l_Lean_Syntax_matchesNull(v___x_6902_, v___x_6391_);
                if v___x_6903_ == 0 {
                    crate::leanh::lean_dec(v_args_6892_);
                    crate::leanh::lean_dec(v___y_6891_);
                    crate::leanh::lean_dec(v___y_6890_);
                    crate::leanh::lean_dec(v___y_6889_);
                    crate::leanh::lean_dec(v___y_6887_);
                    crate::leanh::lean_dec_ref(v___x_6397_);
                    crate::leanh::lean_dec_ref(v___f_6396_);
                    crate::leanh::lean_dec(v___x_6394_);
                    crate::leanh::lean_dec(v___x_6393_);
                    crate::leanh::lean_dec(v___x_6391_);
                    crate::leanh::lean_dec_ref(v___x_6390_);
                    crate::leanh::lean_dec_ref(v___x_6389_);
                    crate::leanh::lean_dec_ref(v___x_6388_);
                    v___x_6904_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__22), core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__22_once), _init_l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__22);
                    v___x_6905_ = l_panic___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__9(v___x_6904_, v___y_6893_, v___y_6894_, v___y_6895_, v___y_6896_, v___y_6897_, v___y_6898_, v___y_6899_, v___y_6900_);
                    crate::leanh::lean_dec(v___y_6898_);
                    crate::leanh::lean_dec_ref(v___y_6897_);
                    crate::leanh::lean_dec(v___y_6896_);
                    crate::leanh::lean_dec_ref(v___y_6895_);
                    crate::leanh::lean_dec(v___y_6894_);
                    crate::leanh::lean_dec_ref(v___y_6893_);
                    if crate::leanh::lean_obj_tag(v___x_6905_) == 0 {
                        v_a_6906_ = crate::leanh::lean_ctor_get(v___x_6905_, 0);
                        crate::leanh::lean_inc(v_a_6906_);
                        crate::leanh::lean_dec_ref_known(v___x_6905_, 1);
                        v___y_6449_ = v___y_6886_;
                        v_stx_6450_ = v_a_6906_;
                        v___y_6451_ = v___y_6899_;
                        v___y_6452_ = v___y_6900_;
                        state = 5;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v___y_6900_);
                        crate::leanh::lean_dec_ref(v___y_6899_);
                        crate::leanh::lean_dec_ref(v___y_6886_);
                        crate::leanh::lean_dec(v_tk_6387_);
                        v_a_6907_ = crate::leanh::lean_ctor_get(v___x_6905_, 0);
                        v_isSharedCheck_6914_ =
                            (!crate::leanh::lean_is_exclusive(v___x_6905_)) as u8;
                        if v_isSharedCheck_6914_ == 0 {
                            v___x_6909_ = v___x_6905_;
                            v_isShared_6910_ = v_isSharedCheck_6914_;
                            state = 33;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_6907_);
                            crate::leanh::lean_dec(v___x_6905_);
                            v___x_6909_ = crate::leanh::lean_box(0);
                            v_isShared_6910_ = v_isSharedCheck_6914_;
                            state = 33;
                            continue;
                        }
                    }
                } else {
                    v___x_6915_ = l_Lean_Syntax_getOptional_x3f(v___y_6891_);
                    crate::leanh::lean_dec(v___y_6891_);
                    if crate::leanh::lean_obj_tag(v___x_6915_) == 0 {
                        v___x_6916_ = crate::leanh::lean_box(0);
                        v___y_6790_ = v___y_6900_;
                        v___y_6791_ = v___y_6886_;
                        v___y_6792_ = v___y_6899_;
                        v___y_6793_ = v___y_6887_;
                        v___y_6794_ = v___y_6895_;
                        v___y_6795_ = v___y_6898_;
                        v___y_6796_ = v___y_6893_;
                        v___y_6797_ = v___y_6897_;
                        v___y_6798_ = v_args_6892_;
                        v___y_6799_ = v___y_6894_;
                        v___y_6800_ = v___y_6885_;
                        v___y_6801_ = v___y_6889_;
                        v___y_6802_ = v___y_6890_;
                        v___y_6803_ = v___y_6896_;
                        v___y_6804_ = v___x_6916_;
                        state = 23;
                        continue;
                    } else {
                        v_val_6917_ = crate::leanh::lean_ctor_get(v___x_6915_, 0);
                        v_isSharedCheck_6924_ =
                            (!crate::leanh::lean_is_exclusive(v___x_6915_)) as u8;
                        if v_isSharedCheck_6924_ == 0 {
                            v___x_6919_ = v___x_6915_;
                            v_isShared_6920_ = v_isSharedCheck_6924_;
                            state = 35;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_val_6917_);
                            crate::leanh::lean_dec(v___x_6915_);
                            v___x_6919_ = crate::leanh::lean_box(0);
                            v_isShared_6920_ = v_isSharedCheck_6924_;
                            state = 35;
                            continue;
                        }
                    }
                }
            }
            33 => {
                if v_isShared_6910_ == 0 {
                    v___x_6912_ = v___x_6909_;
                    state = 34;
                    continue;
                } else {
                    v_reuseFailAlloc_6913_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6913_, 0, v_a_6907_);
                    v___x_6912_ = v_reuseFailAlloc_6913_;
                    state = 34;
                    continue;
                }
            }
            34 => {
                return v___x_6912_;
            }
            35 => {
                if v_isShared_6920_ == 0 {
                    v___x_6922_ = v___x_6919_;
                    state = 36;
                    continue;
                } else {
                    v_reuseFailAlloc_6923_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6923_, 0, v_val_6917_);
                    v___x_6922_ = v_reuseFailAlloc_6923_;
                    state = 36;
                    continue;
                }
            }
            36 => {
                v___y_6790_ = v___y_6900_;
                v___y_6791_ = v___y_6886_;
                v___y_6792_ = v___y_6899_;
                v___y_6793_ = v___y_6887_;
                v___y_6794_ = v___y_6895_;
                v___y_6795_ = v___y_6898_;
                v___y_6796_ = v___y_6893_;
                v___y_6797_ = v___y_6897_;
                v___y_6798_ = v_args_6892_;
                v___y_6799_ = v___y_6894_;
                v___y_6800_ = v___y_6885_;
                v___y_6801_ = v___y_6889_;
                v___y_6802_ = v___y_6890_;
                v___y_6803_ = v___y_6896_;
                v___y_6804_ = v___x_6922_;
                state = 23;
                continue;
            }
            37 => {
                v___x_6941_ = l_Lean_Syntax_getArg(v___y_6929_, v___x_6398_);
                v___x_6942_ = l_Lean_Syntax_isNone(v___x_6941_);
                if v___x_6942_ == 0 {
                    crate::leanh::lean_inc(v___x_6941_);
                    v___x_6943_ = l_Lean_Syntax_matchesNull(v___x_6941_, v___x_6399_);
                    if v___x_6943_ == 0 {
                        crate::leanh::lean_dec(v___x_6941_);
                        crate::leanh::lean_dec(v_only_6932_);
                        crate::leanh::lean_dec(v___y_6931_);
                        crate::leanh::lean_dec(v___y_6930_);
                        crate::leanh::lean_dec(v___y_6929_);
                        crate::leanh::lean_dec(v___y_6928_);
                        crate::leanh::lean_dec(v___x_6400_);
                        crate::leanh::lean_dec_ref(v___x_6397_);
                        crate::leanh::lean_dec_ref(v___f_6396_);
                        crate::leanh::lean_dec(v___x_6394_);
                        crate::leanh::lean_dec(v___x_6393_);
                        crate::leanh::lean_dec(v___x_6391_);
                        crate::leanh::lean_dec_ref(v___x_6390_);
                        crate::leanh::lean_dec_ref(v___x_6389_);
                        crate::leanh::lean_dec_ref(v___x_6388_);
                        v___x_6944_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__22), core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__22_once), _init_l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__22);
                        v___x_6945_ = l_panic___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__9(v___x_6944_, v___y_6933_, v___y_6934_, v___y_6935_, v___y_6936_, v___y_6937_, v___y_6938_, v___y_6939_, v___y_6940_);
                        crate::leanh::lean_dec(v___y_6938_);
                        crate::leanh::lean_dec_ref(v___y_6937_);
                        crate::leanh::lean_dec(v___y_6936_);
                        crate::leanh::lean_dec_ref(v___y_6935_);
                        crate::leanh::lean_dec(v___y_6934_);
                        crate::leanh::lean_dec_ref(v___y_6933_);
                        if crate::leanh::lean_obj_tag(v___x_6945_) == 0 {
                            v_a_6946_ = crate::leanh::lean_ctor_get(v___x_6945_, 0);
                            crate::leanh::lean_inc(v_a_6946_);
                            crate::leanh::lean_dec_ref_known(v___x_6945_, 1);
                            v___y_6449_ = v___y_6926_;
                            v_stx_6450_ = v_a_6946_;
                            v___y_6451_ = v___y_6939_;
                            v___y_6452_ = v___y_6940_;
                            state = 5;
                            continue;
                        } else {
                            crate::leanh::lean_dec(v___y_6940_);
                            crate::leanh::lean_dec_ref(v___y_6939_);
                            crate::leanh::lean_dec_ref(v___y_6926_);
                            crate::leanh::lean_dec(v_tk_6387_);
                            v_a_6947_ = crate::leanh::lean_ctor_get(v___x_6945_, 0);
                            v_isSharedCheck_6954_ =
                                (!crate::leanh::lean_is_exclusive(v___x_6945_)) as u8;
                            if v_isSharedCheck_6954_ == 0 {
                                v___x_6949_ = v___x_6945_;
                                v_isShared_6950_ = v_isSharedCheck_6954_;
                                state = 38;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_6947_);
                                crate::leanh::lean_dec(v___x_6945_);
                                v___x_6949_ = crate::leanh::lean_box(0);
                                v_isShared_6950_ = v_isSharedCheck_6954_;
                                state = 38;
                                continue;
                            }
                        }
                    } else {
                        v___x_6955_ = l_Lean_Syntax_getArg(v___x_6941_, v___x_6400_);
                        crate::leanh::lean_dec(v___x_6400_);
                        crate::leanh::lean_dec(v___x_6941_);
                        v___x_6956_ = l_Lean_Syntax_getArgs(v___x_6955_);
                        crate::leanh::lean_dec(v___x_6955_);
                        v___x_6957_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_6957_, 0, v___x_6956_);
                        v___y_6885_ = v___y_6927_;
                        v___y_6886_ = v___y_6926_;
                        v___y_6887_ = v___y_6928_;
                        v___y_6888_ = v___y_6929_;
                        v___y_6889_ = v___y_6930_;
                        v___y_6890_ = v_only_6932_;
                        v___y_6891_ = v___y_6931_;
                        v_args_6892_ = v___x_6957_;
                        v___y_6893_ = v___y_6933_;
                        v___y_6894_ = v___y_6934_;
                        v___y_6895_ = v___y_6935_;
                        v___y_6896_ = v___y_6936_;
                        v___y_6897_ = v___y_6937_;
                        v___y_6898_ = v___y_6938_;
                        v___y_6899_ = v___y_6939_;
                        v___y_6900_ = v___y_6940_;
                        state = 32;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v___x_6941_);
                    crate::leanh::lean_dec(v___x_6400_);
                    v___x_6958_ = crate::leanh::lean_box(0);
                    v___y_6885_ = v___y_6927_;
                    v___y_6886_ = v___y_6926_;
                    v___y_6887_ = v___y_6928_;
                    v___y_6888_ = v___y_6929_;
                    v___y_6889_ = v___y_6930_;
                    v___y_6890_ = v_only_6932_;
                    v___y_6891_ = v___y_6931_;
                    v_args_6892_ = v___x_6958_;
                    v___y_6893_ = v___y_6933_;
                    v___y_6894_ = v___y_6934_;
                    v___y_6895_ = v___y_6935_;
                    v___y_6896_ = v___y_6936_;
                    v___y_6897_ = v___y_6937_;
                    v___y_6898_ = v___y_6938_;
                    v___y_6899_ = v___y_6939_;
                    v___y_6900_ = v___y_6940_;
                    state = 32;
                    continue;
                }
            }
            38 => {
                if v_isShared_6950_ == 0 {
                    v___x_6952_ = v___x_6949_;
                    state = 39;
                    continue;
                } else {
                    v_reuseFailAlloc_6953_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6953_, 0, v_a_6947_);
                    v___x_6952_ = v_reuseFailAlloc_6953_;
                    state = 39;
                    continue;
                }
            }
            39 => {
                return v___x_6952_;
            }
            40 => {
                v_usedTheorems_6964_ = crate::leanh::lean_ctor_get(v___y_6961_, 0);
                v___x_6965_ = l_Lean_Syntax_unsetTrailing(v___y_6962_);
                v___x_6966_ = l_Lean_Elab_Tactic_mkSimpOnly(
                    v___x_6965_,
                    v_usedTheorems_6964_,
                    v___y_6416_,
                    v___y_6417_,
                    v___y_6418_,
                    v___y_6419_,
                );
                if crate::leanh::lean_obj_tag(v___x_6966_) == 0 {
                    v_a_6967_ = crate::leanh::lean_ctor_get(v___x_6966_, 0);
                    crate::leanh::lean_inc_n(v_a_6967_, 2);
                    crate::leanh::lean_dec_ref_known(v___x_6966_, 1);
                    v___x_6968_ = l_Lean_Syntax_isOfKind(v_a_6967_, v___x_6480_);
                    crate::leanh::lean_dec(v___x_6480_);
                    if v___x_6968_ == 0 {
                        crate::leanh::lean_inc(v_ref_6476_);
                        crate::leanh::lean_dec(v_a_6967_);
                        crate::leanh::lean_dec(v___y_6963_);
                        crate::leanh::lean_dec(v___x_6402_);
                        crate::leanh::lean_dec(v___x_6400_);
                        crate::leanh::lean_dec_ref(v___x_6397_);
                        crate::leanh::lean_dec_ref(v___f_6396_);
                        crate::leanh::lean_dec(v___x_6394_);
                        crate::leanh::lean_dec(v___x_6393_);
                        crate::leanh::lean_dec(v___x_6391_);
                        crate::leanh::lean_dec_ref(v___x_6390_);
                        crate::leanh::lean_dec_ref(v___x_6389_);
                        crate::leanh::lean_dec_ref(v___x_6388_);
                        v___x_6969_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__22), core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__22_once), _init_l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__22);
                        v___x_6970_ = l_panic___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__9(v___x_6969_, v___y_6412_, v___y_6413_, v___y_6414_, v___y_6415_, v___y_6416_, v___y_6417_, v___y_6418_, v___y_6419_);
                        crate::leanh::lean_dec(v___y_6417_);
                        crate::leanh::lean_dec_ref(v___y_6416_);
                        crate::leanh::lean_dec(v___y_6415_);
                        crate::leanh::lean_dec_ref(v___y_6414_);
                        crate::leanh::lean_dec(v___y_6413_);
                        crate::leanh::lean_dec_ref(v___y_6412_);
                        if crate::leanh::lean_obj_tag(v___x_6970_) == 0 {
                            v_a_6971_ = crate::leanh::lean_ctor_get(v___x_6970_, 0);
                            crate::leanh::lean_inc(v_a_6971_);
                            crate::leanh::lean_dec_ref_known(v___x_6970_, 1);
                            v___y_6426_ = v___y_6961_;
                            v_stx_6427_ = v_a_6971_;
                            v___y_6428_ = v___y_6418_;
                            v_ref_6429_ = v_ref_6476_;
                            v___y_6430_ = v___y_6419_;
                            state = 2;
                            continue;
                        } else {
                            crate::leanh::lean_dec_ref(v___y_6961_);
                            crate::leanh::lean_dec(v_ref_6476_);
                            crate::leanh::lean_dec(v___y_6419_);
                            crate::leanh::lean_dec_ref(v___y_6418_);
                            crate::leanh::lean_dec(v_tk_6387_);
                            v_a_6972_ = crate::leanh::lean_ctor_get(v___x_6970_, 0);
                            v_isSharedCheck_6979_ =
                                (!crate::leanh::lean_is_exclusive(v___x_6970_)) as u8;
                            if v_isSharedCheck_6979_ == 0 {
                                v___x_6974_ = v___x_6970_;
                                v_isShared_6975_ = v_isSharedCheck_6979_;
                                state = 41;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_6972_);
                                crate::leanh::lean_dec(v___x_6970_);
                                v___x_6974_ = crate::leanh::lean_box(0);
                                v_isShared_6975_ = v_isSharedCheck_6979_;
                                state = 41;
                                continue;
                            }
                        }
                    } else {
                        v___x_6980_ = l_Lean_Syntax_getArg(v_a_6967_, v___x_6400_);
                        crate::leanh::lean_inc(v___x_6980_);
                        v___x_6981_ = l_Lean_Syntax_isOfKind(v___x_6980_, v___x_6401_);
                        if v___x_6981_ == 0 {
                            crate::leanh::lean_inc(v_ref_6476_);
                            crate::leanh::lean_dec(v___x_6980_);
                            crate::leanh::lean_dec(v_a_6967_);
                            crate::leanh::lean_dec(v___y_6963_);
                            crate::leanh::lean_dec(v___x_6402_);
                            crate::leanh::lean_dec(v___x_6400_);
                            crate::leanh::lean_dec_ref(v___x_6397_);
                            crate::leanh::lean_dec_ref(v___f_6396_);
                            crate::leanh::lean_dec(v___x_6394_);
                            crate::leanh::lean_dec(v___x_6393_);
                            crate::leanh::lean_dec(v___x_6391_);
                            crate::leanh::lean_dec_ref(v___x_6390_);
                            crate::leanh::lean_dec_ref(v___x_6389_);
                            crate::leanh::lean_dec_ref(v___x_6388_);
                            v___x_6982_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__22), core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__22_once), _init_l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__22);
                            v___x_6983_ = l_panic___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__9(v___x_6982_, v___y_6412_, v___y_6413_, v___y_6414_, v___y_6415_, v___y_6416_, v___y_6417_, v___y_6418_, v___y_6419_);
                            crate::leanh::lean_dec(v___y_6417_);
                            crate::leanh::lean_dec_ref(v___y_6416_);
                            crate::leanh::lean_dec(v___y_6415_);
                            crate::leanh::lean_dec_ref(v___y_6414_);
                            crate::leanh::lean_dec(v___y_6413_);
                            crate::leanh::lean_dec_ref(v___y_6412_);
                            if crate::leanh::lean_obj_tag(v___x_6983_) == 0 {
                                v_a_6984_ = crate::leanh::lean_ctor_get(v___x_6983_, 0);
                                crate::leanh::lean_inc(v_a_6984_);
                                crate::leanh::lean_dec_ref_known(v___x_6983_, 1);
                                v___y_6426_ = v___y_6961_;
                                v_stx_6427_ = v_a_6984_;
                                v___y_6428_ = v___y_6418_;
                                v_ref_6429_ = v_ref_6476_;
                                v___y_6430_ = v___y_6419_;
                                state = 2;
                                continue;
                            } else {
                                crate::leanh::lean_dec_ref(v___y_6961_);
                                crate::leanh::lean_dec(v_ref_6476_);
                                crate::leanh::lean_dec(v___y_6419_);
                                crate::leanh::lean_dec_ref(v___y_6418_);
                                crate::leanh::lean_dec(v_tk_6387_);
                                v_a_6985_ = crate::leanh::lean_ctor_get(v___x_6983_, 0);
                                v_isSharedCheck_6992_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_6983_)) as u8;
                                if v_isSharedCheck_6992_ == 0 {
                                    v___x_6987_ = v___x_6983_;
                                    v_isShared_6988_ = v_isSharedCheck_6992_;
                                    state = 43;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_a_6985_);
                                    crate::leanh::lean_dec(v___x_6983_);
                                    v___x_6987_ = crate::leanh::lean_box(0);
                                    v_isShared_6988_ = v_isSharedCheck_6992_;
                                    state = 43;
                                    continue;
                                }
                            }
                        } else {
                            v___x_6993_ = l_Lean_Syntax_getArg(v_a_6967_, v___x_6402_);
                            crate::leanh::lean_dec(v___x_6402_);
                            v___x_6994_ = l_Lean_Syntax_getArg(v_a_6967_, v___x_6399_);
                            v___x_6995_ = l_Lean_Syntax_isNone(v___x_6994_);
                            if v___x_6995_ == 0 {
                                crate::leanh::lean_inc(v___x_6994_);
                                v___x_6996_ = l_Lean_Syntax_matchesNull(v___x_6994_, v___x_6400_);
                                if v___x_6996_ == 0 {
                                    crate::leanh::lean_inc(v_ref_6476_);
                                    crate::leanh::lean_dec(v___x_6994_);
                                    crate::leanh::lean_dec(v___x_6993_);
                                    crate::leanh::lean_dec(v___x_6980_);
                                    crate::leanh::lean_dec(v_a_6967_);
                                    crate::leanh::lean_dec(v___y_6963_);
                                    crate::leanh::lean_dec(v___x_6400_);
                                    crate::leanh::lean_dec_ref(v___x_6397_);
                                    crate::leanh::lean_dec_ref(v___f_6396_);
                                    crate::leanh::lean_dec(v___x_6394_);
                                    crate::leanh::lean_dec(v___x_6393_);
                                    crate::leanh::lean_dec(v___x_6391_);
                                    crate::leanh::lean_dec_ref(v___x_6390_);
                                    crate::leanh::lean_dec_ref(v___x_6389_);
                                    crate::leanh::lean_dec_ref(v___x_6388_);
                                    v___x_6997_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__22), core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__22_once), _init_l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__22);
                                    v___x_6998_ = l_panic___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__9(v___x_6997_, v___y_6412_, v___y_6413_, v___y_6414_, v___y_6415_, v___y_6416_, v___y_6417_, v___y_6418_, v___y_6419_);
                                    crate::leanh::lean_dec(v___y_6417_);
                                    crate::leanh::lean_dec_ref(v___y_6416_);
                                    crate::leanh::lean_dec(v___y_6415_);
                                    crate::leanh::lean_dec_ref(v___y_6414_);
                                    crate::leanh::lean_dec(v___y_6413_);
                                    crate::leanh::lean_dec_ref(v___y_6412_);
                                    if crate::leanh::lean_obj_tag(v___x_6998_) == 0 {
                                        v_a_6999_ = crate::leanh::lean_ctor_get(v___x_6998_, 0);
                                        crate::leanh::lean_inc(v_a_6999_);
                                        crate::leanh::lean_dec_ref_known(v___x_6998_, 1);
                                        v___y_6426_ = v___y_6961_;
                                        v_stx_6427_ = v_a_6999_;
                                        v___y_6428_ = v___y_6418_;
                                        v_ref_6429_ = v_ref_6476_;
                                        v___y_6430_ = v___y_6419_;
                                        state = 2;
                                        continue;
                                    } else {
                                        crate::leanh::lean_dec_ref(v___y_6961_);
                                        crate::leanh::lean_dec(v_ref_6476_);
                                        crate::leanh::lean_dec(v___y_6419_);
                                        crate::leanh::lean_dec_ref(v___y_6418_);
                                        crate::leanh::lean_dec(v_tk_6387_);
                                        v_a_7000_ = crate::leanh::lean_ctor_get(v___x_6998_, 0);
                                        v_isSharedCheck_7007_ =
                                            (!crate::leanh::lean_is_exclusive(v___x_6998_)) as u8;
                                        if v_isSharedCheck_7007_ == 0 {
                                            v___x_7002_ = v___x_6998_;
                                            v_isShared_7003_ = v_isSharedCheck_7007_;
                                            state = 45;
                                            continue;
                                        } else {
                                            crate::leanh::lean_inc(v_a_7000_);
                                            crate::leanh::lean_dec(v___x_6998_);
                                            v___x_7002_ = crate::leanh::lean_box(0);
                                            v_isShared_7003_ = v_isSharedCheck_7007_;
                                            state = 45;
                                            continue;
                                        }
                                    }
                                } else {
                                    v___x_7008_ = l_Lean_Syntax_getArg(v___x_6994_, v___x_6391_);
                                    crate::leanh::lean_dec(v___x_6994_);
                                    v___x_7009_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                                    crate::leanh::lean_ctor_set(v___x_7009_, 0, v___x_7008_);
                                    v___y_6926_ = v___y_6961_;
                                    v___y_6927_ = v___y_6960_;
                                    v___y_6928_ = v___y_6963_;
                                    v___y_6929_ = v_a_6967_;
                                    v___y_6930_ = v___x_6980_;
                                    v___y_6931_ = v___x_6993_;
                                    v_only_6932_ = v___x_7009_;
                                    v___y_6933_ = v___y_6412_;
                                    v___y_6934_ = v___y_6413_;
                                    v___y_6935_ = v___y_6414_;
                                    v___y_6936_ = v___y_6415_;
                                    v___y_6937_ = v___y_6416_;
                                    v___y_6938_ = v___y_6417_;
                                    v___y_6939_ = v___y_6418_;
                                    v___y_6940_ = v___y_6419_;
                                    state = 37;
                                    continue;
                                }
                            } else {
                                crate::leanh::lean_dec(v___x_6994_);
                                v___x_7010_ = crate::leanh::lean_box(0);
                                v___y_6926_ = v___y_6961_;
                                v___y_6927_ = v___y_6960_;
                                v___y_6928_ = v___y_6963_;
                                v___y_6929_ = v_a_6967_;
                                v___y_6930_ = v___x_6980_;
                                v___y_6931_ = v___x_6993_;
                                v_only_6932_ = v___x_7010_;
                                v___y_6933_ = v___y_6412_;
                                v___y_6934_ = v___y_6413_;
                                v___y_6935_ = v___y_6414_;
                                v___y_6936_ = v___y_6415_;
                                v___y_6937_ = v___y_6416_;
                                v___y_6938_ = v___y_6417_;
                                v___y_6939_ = v___y_6418_;
                                v___y_6940_ = v___y_6419_;
                                state = 37;
                                continue;
                            }
                        }
                    }
                } else {
                    crate::leanh::lean_dec(v___y_6963_);
                    crate::leanh::lean_dec_ref(v___y_6961_);
                    crate::leanh::lean_dec(v___x_6480_);
                    crate::leanh::lean_dec(v___y_6419_);
                    crate::leanh::lean_dec_ref(v___y_6418_);
                    crate::leanh::lean_dec(v___y_6417_);
                    crate::leanh::lean_dec_ref(v___y_6416_);
                    crate::leanh::lean_dec(v___y_6415_);
                    crate::leanh::lean_dec_ref(v___y_6414_);
                    crate::leanh::lean_dec(v___y_6413_);
                    crate::leanh::lean_dec_ref(v___y_6412_);
                    crate::leanh::lean_dec(v___x_6402_);
                    crate::leanh::lean_dec(v___x_6400_);
                    crate::leanh::lean_dec_ref(v___x_6397_);
                    crate::leanh::lean_dec_ref(v___f_6396_);
                    crate::leanh::lean_dec(v___x_6394_);
                    crate::leanh::lean_dec(v___x_6393_);
                    crate::leanh::lean_dec(v___x_6391_);
                    crate::leanh::lean_dec_ref(v___x_6390_);
                    crate::leanh::lean_dec_ref(v___x_6389_);
                    crate::leanh::lean_dec_ref(v___x_6388_);
                    crate::leanh::lean_dec(v_tk_6387_);
                    v_a_7011_ = crate::leanh::lean_ctor_get(v___x_6966_, 0);
                    v_isSharedCheck_7018_ = (!crate::leanh::lean_is_exclusive(v___x_6966_)) as u8;
                    if v_isSharedCheck_7018_ == 0 {
                        v___x_7013_ = v___x_6966_;
                        v_isShared_7014_ = v_isSharedCheck_7018_;
                        state = 47;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_7011_);
                        crate::leanh::lean_dec(v___x_6966_);
                        v___x_7013_ = crate::leanh::lean_box(0);
                        v_isShared_7014_ = v_isSharedCheck_7018_;
                        state = 47;
                        continue;
                    }
                }
            }
            41 => {
                if v_isShared_6975_ == 0 {
                    v___x_6977_ = v___x_6974_;
                    state = 42;
                    continue;
                } else {
                    v_reuseFailAlloc_6978_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6978_, 0, v_a_6972_);
                    v___x_6977_ = v_reuseFailAlloc_6978_;
                    state = 42;
                    continue;
                }
            }
            42 => {
                return v___x_6977_;
            }
            43 => {
                if v_isShared_6988_ == 0 {
                    v___x_6990_ = v___x_6987_;
                    state = 44;
                    continue;
                } else {
                    v_reuseFailAlloc_6991_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6991_, 0, v_a_6985_);
                    v___x_6990_ = v_reuseFailAlloc_6991_;
                    state = 44;
                    continue;
                }
            }
            44 => {
                return v___x_6990_;
            }
            45 => {
                if v_isShared_7003_ == 0 {
                    v___x_7005_ = v___x_7002_;
                    state = 46;
                    continue;
                } else {
                    v_reuseFailAlloc_7006_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7006_, 0, v_a_7000_);
                    v___x_7005_ = v_reuseFailAlloc_7006_;
                    state = 46;
                    continue;
                }
            }
            46 => {
                return v___x_7005_;
            }
            47 => {
                if v_isShared_7014_ == 0 {
                    v___x_7016_ = v___x_7013_;
                    state = 48;
                    continue;
                } else {
                    v_reuseFailAlloc_7017_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7017_, 0, v_a_7011_);
                    v___x_7016_ = v_reuseFailAlloc_7017_;
                    state = 48;
                    continue;
                }
            }
            48 => {
                return v___x_7016_;
            }
            49 => {
                if crate::leanh::lean_obj_tag(v_usingArg_6403_) == 0 {
                    v___y_6960_ = v___y_7021_;
                    v___y_6961_ = v___y_7020_;
                    v___y_6962_ = v___y_7022_;
                    v___y_6963_ = v_usingArg_6403_;
                    state = 40;
                    continue;
                } else {
                    v_val_7023_ = crate::leanh::lean_ctor_get(v_usingArg_6403_, 0);
                    v_isSharedCheck_7031_ =
                        (!crate::leanh::lean_is_exclusive(v_usingArg_6403_)) as u8;
                    if v_isSharedCheck_7031_ == 0 {
                        v___x_7025_ = v_usingArg_6403_;
                        v_isShared_7026_ = v_isSharedCheck_7031_;
                        state = 50;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_val_7023_);
                        crate::leanh::lean_dec(v_usingArg_6403_);
                        v___x_7025_ = crate::leanh::lean_box(0);
                        v_isShared_7026_ = v_isSharedCheck_7031_;
                        state = 50;
                        continue;
                    }
                }
            }
            50 => {
                v___x_7027_ = l_Lean_Syntax_unsetTrailing(v_val_7023_);
                if v_isShared_7026_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_7025_, 0, v___x_7027_);
                    v___x_7029_ = v___x_7025_;
                    state = 51;
                    continue;
                } else {
                    v_reuseFailAlloc_7030_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7030_, 0, v___x_7027_);
                    v___x_7029_ = v_reuseFailAlloc_7030_;
                    state = 51;
                    continue;
                }
            }
            51 => {
                v___y_6960_ = v___y_7021_;
                v___y_6961_ = v___y_7020_;
                v___y_6962_ = v___y_7022_;
                v___y_6963_ = v___x_7029_;
                state = 40;
                continue;
            }
            52 => {
                if v___y_7036_ == 0 {
                    crate::leanh::lean_dec(v___y_7035_);
                    crate::leanh::lean_dec(v___x_6480_);
                    crate::leanh::lean_dec(v___y_6419_);
                    crate::leanh::lean_dec_ref(v___y_6418_);
                    crate::leanh::lean_dec(v___y_6417_);
                    crate::leanh::lean_dec_ref(v___y_6416_);
                    crate::leanh::lean_dec(v___y_6415_);
                    crate::leanh::lean_dec_ref(v___y_6414_);
                    crate::leanh::lean_dec(v___y_6413_);
                    crate::leanh::lean_dec_ref(v___y_6412_);
                    crate::leanh::lean_dec(v_usingArg_6403_);
                    crate::leanh::lean_dec(v___x_6402_);
                    crate::leanh::lean_dec(v___x_6400_);
                    crate::leanh::lean_dec_ref(v___x_6397_);
                    crate::leanh::lean_dec_ref(v___f_6396_);
                    crate::leanh::lean_dec(v___x_6394_);
                    crate::leanh::lean_dec(v___x_6393_);
                    crate::leanh::lean_dec(v___x_6391_);
                    crate::leanh::lean_dec_ref(v___x_6390_);
                    crate::leanh::lean_dec_ref(v___x_6389_);
                    crate::leanh::lean_dec_ref(v___x_6388_);
                    crate::leanh::lean_dec(v_tk_6387_);
                    v___y_6422_ = v___y_7034_;
                    state = 1;
                    continue;
                } else {
                    v___y_7020_ = v___y_7034_;
                    v___y_7021_ = v___y_7033_;
                    v___y_7022_ = v___y_7035_;
                    state = 49;
                    continue;
                }
            }
            53 => {
                v___x_7043_ = l_Lean_Meta_Simp_Context_setFailIfUnchanged(v___y_7042_, v___x_6477_);
                v___x_7044_ = crate::leanh::lean_box((v___x_6392_) as usize);
                v___x_7045_ = crate::leanh::lean_box((v___x_6477_) as usize);
                v___x_7046_ = crate::leanh::lean_box((v_useReducible_6395_) as usize);
                v___x_7047_ = crate::leanh::lean_box((v___x_6405_) as usize);
                crate::leanh::lean_inc(v___x_6400_);
                crate::leanh::lean_inc_ref(v___x_6397_);
                crate::leanh::lean_inc(v_usingArg_6403_);
                crate::leanh::lean_inc(v___x_6391_);
                crate::leanh::lean_inc(v_tk_6387_);
                crate::leanh::lean_inc(v___x_6402_);
                v___f_7048_ = crate::leanh::lean_alloc_closure(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__5___boxed as *mut core::ffi::c_void, 24, 14);
                crate::leanh::lean_closure_set(v___f_7048_, 0, v___x_6402_);
                crate::leanh::lean_closure_set(v___f_7048_, 1, v_tk_6387_);
                crate::leanh::lean_closure_set(v___f_7048_, 2, v___x_6482_);
                crate::leanh::lean_closure_set(v___f_7048_, 3, v___x_6391_);
                crate::leanh::lean_closure_set(v___f_7048_, 4, v___x_7043_);
                crate::leanh::lean_closure_set(v___f_7048_, 5, v___y_7038_);
                crate::leanh::lean_closure_set(v___f_7048_, 6, v___x_7044_);
                crate::leanh::lean_closure_set(v___f_7048_, 7, v_usingArg_6403_);
                crate::leanh::lean_closure_set(v___f_7048_, 8, v___x_7045_);
                crate::leanh::lean_closure_set(v___f_7048_, 9, v___x_6397_);
                crate::leanh::lean_closure_set(v___f_7048_, 10, v___x_7046_);
                crate::leanh::lean_closure_set(v___f_7048_, 11, v___x_7047_);
                crate::leanh::lean_closure_set(v___f_7048_, 12, v___x_6400_);
                crate::leanh::lean_closure_set(v___f_7048_, 13, v_usingTk_x3f_6406_);
                v___x_7049_ = l_Lean_Elab_Tactic_Simp_DischargeWrapper_with___redArg(
                    v___y_7041_,
                    v___f_7048_,
                    v___y_6412_,
                    v___y_6413_,
                    v___y_6414_,
                    v___y_6415_,
                    v___y_6416_,
                    v___y_6417_,
                    v___y_6418_,
                    v___y_6419_,
                );
                crate::leanh::lean_dec(v___y_7041_);
                if crate::leanh::lean_obj_tag(v___x_7049_) == 0 {
                    v_a_7050_ = crate::leanh::lean_ctor_get(v___x_7049_, 0);
                    crate::leanh::lean_inc(v_a_7050_);
                    crate::leanh::lean_dec_ref_known(v___x_7049_, 1);
                    v___x_7051_ = l_Lean_Elab_Tactic_tactic_simp_trace;
                    v___x_7052_ = l_Lean_Option_get___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__10(v_options_6475_, v___x_7051_);
                    if v___x_7052_ == 0 {
                        if crate::leanh::lean_obj_tag(v_squeeze_6407_) == 0 {
                            v___y_7033_ = v___y_7039_;
                            v___y_7034_ = v_a_7050_;
                            v___y_7035_ = v___y_7040_;
                            v___y_7036_ = v___x_7052_;
                            state = 52;
                            continue;
                        } else {
                            v___y_7033_ = v___y_7039_;
                            v___y_7034_ = v_a_7050_;
                            v___y_7035_ = v___y_7040_;
                            v___y_7036_ = v___x_6405_;
                            state = 52;
                            continue;
                        }
                    } else {
                        v___y_7020_ = v_a_7050_;
                        v___y_7021_ = v___y_7039_;
                        v___y_7022_ = v___y_7040_;
                        state = 49;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v___y_7040_);
                    crate::leanh::lean_dec(v___x_6480_);
                    crate::leanh::lean_dec(v___y_6419_);
                    crate::leanh::lean_dec_ref(v___y_6418_);
                    crate::leanh::lean_dec(v___y_6417_);
                    crate::leanh::lean_dec_ref(v___y_6416_);
                    crate::leanh::lean_dec(v___y_6415_);
                    crate::leanh::lean_dec_ref(v___y_6414_);
                    crate::leanh::lean_dec(v___y_6413_);
                    crate::leanh::lean_dec_ref(v___y_6412_);
                    crate::leanh::lean_dec(v_usingArg_6403_);
                    crate::leanh::lean_dec(v___x_6402_);
                    crate::leanh::lean_dec(v___x_6400_);
                    crate::leanh::lean_dec_ref(v___x_6397_);
                    crate::leanh::lean_dec_ref(v___f_6396_);
                    crate::leanh::lean_dec(v___x_6394_);
                    crate::leanh::lean_dec(v___x_6393_);
                    crate::leanh::lean_dec(v___x_6391_);
                    crate::leanh::lean_dec_ref(v___x_6390_);
                    crate::leanh::lean_dec_ref(v___x_6389_);
                    crate::leanh::lean_dec_ref(v___x_6388_);
                    crate::leanh::lean_dec(v_tk_6387_);
                    v_a_7053_ = crate::leanh::lean_ctor_get(v___x_7049_, 0);
                    v_isSharedCheck_7060_ = (!crate::leanh::lean_is_exclusive(v___x_7049_)) as u8;
                    if v_isSharedCheck_7060_ == 0 {
                        v___x_7055_ = v___x_7049_;
                        v_isShared_7056_ = v_isSharedCheck_7060_;
                        state = 54;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_7053_);
                        crate::leanh::lean_dec(v___x_7049_);
                        v___x_7055_ = crate::leanh::lean_box(0);
                        v_isShared_7056_ = v_isSharedCheck_7060_;
                        state = 54;
                        continue;
                    }
                }
            }
            54 => {
                if v_isShared_7056_ == 0 {
                    v___x_7058_ = v___x_7055_;
                    state = 55;
                    continue;
                } else {
                    v_reuseFailAlloc_7059_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7059_, 0, v_a_7053_);
                    v___x_7058_ = v_reuseFailAlloc_7059_;
                    state = 55;
                    continue;
                }
            }
            55 => {
                return v___x_7058_;
            }
            56 => {
                v___x_7065_ = l_Array_append___redArg(v___x_6483_, v___y_7064_);
                crate::leanh::lean_dec_ref(v___y_7064_);
                crate::leanh::lean_inc_n(v___x_6478_, 2);
                v___x_7066_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_7066_, 0, v___x_6478_);
                crate::leanh::lean_ctor_set(v___x_7066_, 1, v___x_6482_);
                crate::leanh::lean_ctor_set(v___x_7066_, 2, v___x_7065_);
                v___x_7067_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_7067_, 0, v___x_6478_);
                crate::leanh::lean_ctor_set(v___x_7067_, 1, v___x_6482_);
                crate::leanh::lean_ctor_set(v___x_7067_, 2, v___x_6483_);
                crate::leanh::lean_inc(v___x_6480_);
                v___x_7068_ = l_Lean_Syntax_node6(
                    v___x_6478_,
                    v___x_6480_,
                    v___x_6481_,
                    v___x_6404_,
                    v___y_7063_,
                    v___y_7062_,
                    v___x_7066_,
                    v___x_7067_,
                );
                v___x_7069_ = 0;
                v___x_7070_ = l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__23;
                v___x_7071_ = crate::leanh::lean_box((v___x_6477_) as usize);
                v___x_7072_ = crate::leanh::lean_box((v___x_7069_) as usize);
                v___x_7073_ = crate::leanh::lean_box((v___x_6477_) as usize);
                crate::leanh::lean_inc(v___x_7068_);
                v___x_7074_ = crate::leanh::lean_alloc_closure(
                    l_Lean_Elab_Tactic_mkSimpContext___boxed as *mut core::ffi::c_void,
                    14,
                    5,
                );
                crate::leanh::lean_closure_set(v___x_7074_, 0, v___x_7068_);
                crate::leanh::lean_closure_set(v___x_7074_, 1, v___x_7071_);
                crate::leanh::lean_closure_set(v___x_7074_, 2, v___x_7072_);
                crate::leanh::lean_closure_set(v___x_7074_, 3, v___x_7073_);
                crate::leanh::lean_closure_set(v___x_7074_, 4, v___x_7070_);
                v___x_7075_ = l_Lean_Elab_Tactic_withMainContext___redArg(
                    v___x_7074_,
                    v___y_6412_,
                    v___y_6413_,
                    v___y_6414_,
                    v___y_6415_,
                    v___y_6416_,
                    v___y_6417_,
                    v___y_6418_,
                    v___y_6419_,
                );
                if crate::leanh::lean_obj_tag(v___x_7075_) == 0 {
                    v_a_7076_ = crate::leanh::lean_ctor_get(v___x_7075_, 0);
                    crate::leanh::lean_inc(v_a_7076_);
                    crate::leanh::lean_dec_ref_known(v___x_7075_, 1);
                    if crate::leanh::lean_obj_tag(v_unfold_6408_) == 0 {
                        v_ctx_7077_ = crate::leanh::lean_ctor_get(v_a_7076_, 0);
                        crate::leanh::lean_inc_ref(v_ctx_7077_);
                        v_simprocs_7078_ = crate::leanh::lean_ctor_get(v_a_7076_, 1);
                        crate::leanh::lean_inc_ref(v_simprocs_7078_);
                        v_dischargeWrapper_7079_ = crate::leanh::lean_ctor_get(v_a_7076_, 2);
                        crate::leanh::lean_inc(v_dischargeWrapper_7079_);
                        crate::leanh::lean_dec(v_a_7076_);
                        v___y_7038_ = v_simprocs_7078_;
                        v___y_7039_ = v___x_6477_;
                        v___y_7040_ = v___x_7068_;
                        v___y_7041_ = v_dischargeWrapper_7079_;
                        v___y_7042_ = v_ctx_7077_;
                        state = 53;
                        continue;
                    } else {
                        if v___x_6405_ == 0 {
                            v_ctx_7080_ = crate::leanh::lean_ctor_get(v_a_7076_, 0);
                            crate::leanh::lean_inc_ref(v_ctx_7080_);
                            v_simprocs_7081_ = crate::leanh::lean_ctor_get(v_a_7076_, 1);
                            crate::leanh::lean_inc_ref(v_simprocs_7081_);
                            v_dischargeWrapper_7082_ = crate::leanh::lean_ctor_get(v_a_7076_, 2);
                            crate::leanh::lean_inc(v_dischargeWrapper_7082_);
                            crate::leanh::lean_dec(v_a_7076_);
                            v___y_7038_ = v_simprocs_7081_;
                            v___y_7039_ = v___x_6405_;
                            v___y_7040_ = v___x_7068_;
                            v___y_7041_ = v_dischargeWrapper_7082_;
                            v___y_7042_ = v_ctx_7080_;
                            state = 53;
                            continue;
                        } else {
                            v_ctx_7083_ = crate::leanh::lean_ctor_get(v_a_7076_, 0);
                            crate::leanh::lean_inc_ref(v_ctx_7083_);
                            v_simprocs_7084_ = crate::leanh::lean_ctor_get(v_a_7076_, 1);
                            crate::leanh::lean_inc_ref(v_simprocs_7084_);
                            v_dischargeWrapper_7085_ = crate::leanh::lean_ctor_get(v_a_7076_, 2);
                            crate::leanh::lean_inc(v_dischargeWrapper_7085_);
                            crate::leanh::lean_dec(v_a_7076_);
                            v___x_7086_ = l_Lean_Meta_Simp_Context_setAutoUnfold(v_ctx_7083_);
                            v___y_7038_ = v_simprocs_7084_;
                            v___y_7039_ = v___x_6405_;
                            v___y_7040_ = v___x_7068_;
                            v___y_7041_ = v_dischargeWrapper_7085_;
                            v___y_7042_ = v___x_7086_;
                            state = 53;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec(v___x_7068_);
                    crate::leanh::lean_dec(v___x_6480_);
                    crate::leanh::lean_dec(v___y_6419_);
                    crate::leanh::lean_dec_ref(v___y_6418_);
                    crate::leanh::lean_dec(v___y_6417_);
                    crate::leanh::lean_dec_ref(v___y_6416_);
                    crate::leanh::lean_dec(v___y_6415_);
                    crate::leanh::lean_dec_ref(v___y_6414_);
                    crate::leanh::lean_dec(v___y_6413_);
                    crate::leanh::lean_dec_ref(v___y_6412_);
                    crate::leanh::lean_dec(v_usingTk_x3f_6406_);
                    crate::leanh::lean_dec(v_usingArg_6403_);
                    crate::leanh::lean_dec(v___x_6402_);
                    crate::leanh::lean_dec(v___x_6400_);
                    crate::leanh::lean_dec_ref(v___x_6397_);
                    crate::leanh::lean_dec_ref(v___f_6396_);
                    crate::leanh::lean_dec(v___x_6394_);
                    crate::leanh::lean_dec(v___x_6393_);
                    crate::leanh::lean_dec(v___x_6391_);
                    crate::leanh::lean_dec_ref(v___x_6390_);
                    crate::leanh::lean_dec_ref(v___x_6389_);
                    crate::leanh::lean_dec_ref(v___x_6388_);
                    crate::leanh::lean_dec(v_tk_6387_);
                    v_a_7087_ = crate::leanh::lean_ctor_get(v___x_7075_, 0);
                    v_isSharedCheck_7094_ = (!crate::leanh::lean_is_exclusive(v___x_7075_)) as u8;
                    if v_isSharedCheck_7094_ == 0 {
                        v___x_7089_ = v___x_7075_;
                        v_isShared_7090_ = v_isSharedCheck_7094_;
                        state = 57;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_7087_);
                        crate::leanh::lean_dec(v___x_7075_);
                        v___x_7089_ = crate::leanh::lean_box(0);
                        v_isShared_7090_ = v_isSharedCheck_7094_;
                        state = 57;
                        continue;
                    }
                }
            }
            57 => {
                if v_isShared_7090_ == 0 {
                    v___x_7092_ = v___x_7089_;
                    state = 58;
                    continue;
                } else {
                    v_reuseFailAlloc_7093_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7093_, 0, v_a_7087_);
                    v___x_7092_ = v_reuseFailAlloc_7093_;
                    state = 58;
                    continue;
                }
            }
            58 => {
                return v___x_7092_;
            }
            59 => {
                v___x_7098_ = l_Array_append___redArg(v___x_6483_, v___y_7097_);
                crate::leanh::lean_dec_ref(v___y_7097_);
                crate::leanh::lean_inc(v___x_6478_);
                v___x_7099_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_7099_, 0, v___x_6478_);
                crate::leanh::lean_ctor_set(v___x_7099_, 1, v___x_6482_);
                crate::leanh::lean_ctor_set(v___x_7099_, 2, v___x_7098_);
                if crate::leanh::lean_obj_tag(v_args_6409_) == 1 {
                    v_val_7100_ = crate::leanh::lean_ctor_get(v_args_6409_, 0);
                    v___x_7101_ = l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__13;
                    crate::leanh::lean_inc_n(v___x_6478_, 3);
                    v___x_7102_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_7102_, 0, v___x_6478_);
                    crate::leanh::lean_ctor_set(v___x_7102_, 1, v___x_7101_);
                    v___x_7103_ = l_Array_append___redArg(v___x_6483_, v_val_7100_);
                    v___x_7104_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_7104_, 0, v___x_6478_);
                    crate::leanh::lean_ctor_set(v___x_7104_, 1, v___x_6482_);
                    crate::leanh::lean_ctor_set(v___x_7104_, 2, v___x_7103_);
                    v___x_7105_ = l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__14;
                    v___x_7106_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_7106_, 0, v___x_6478_);
                    crate::leanh::lean_ctor_set(v___x_7106_, 1, v___x_7105_);
                    v___x_7107_ = l_Array_mkArray3___redArg(v___x_7102_, v___x_7104_, v___x_7106_);
                    v___y_7062_ = v___x_7099_;
                    v___y_7063_ = v___y_7096_;
                    v___y_7064_ = v___x_7107_;
                    state = 56;
                    continue;
                } else {
                    v___x_7108_ = lean_mk_empty_array_with_capacity(v___x_6391_);
                    v___y_7062_ = v___x_7099_;
                    v___y_7063_ = v___y_7096_;
                    v___y_7064_ = v___x_7108_;
                    state = 56;
                    continue;
                }
            }
            60 => {
                v___x_7111_ = l_Array_append___redArg(v___x_6483_, v___y_7110_);
                crate::leanh::lean_dec_ref(v___y_7110_);
                crate::leanh::lean_inc(v___x_6478_);
                v___x_7112_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_7112_, 0, v___x_6478_);
                crate::leanh::lean_ctor_set(v___x_7112_, 1, v___x_6482_);
                crate::leanh::lean_ctor_set(v___x_7112_, 2, v___x_7111_);
                if crate::leanh::lean_obj_tag(v_only_6410_) == 1 {
                    v_val_7113_ = crate::leanh::lean_ctor_get(v_only_6410_, 0);
                    v___x_7114_ = l_Lean_SourceInfo_fromRef(v_val_7113_, v___x_6392_);
                    v___x_7115_ = l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__15;
                    v___x_7116_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_7116_, 0, v___x_7114_);
                    crate::leanh::lean_ctor_set(v___x_7116_, 1, v___x_7115_);
                    v___x_7117_ = l_Array_mkArray1___redArg(v___x_7116_);
                    v___y_7096_ = v___x_7112_;
                    v___y_7097_ = v___x_7117_;
                    state = 59;
                    continue;
                } else {
                    v___x_7118_ = lean_mk_empty_array_with_capacity(v___x_6391_);
                    v___y_7096_ = v___x_7112_;
                    v___y_7097_ = v___x_7118_;
                    state = 59;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___boxed(
    _args: *mut *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_tk_7123_: *mut crate::leanh::LeanObject = *_args.add(0);
    let mut v___x_7124_: *mut crate::leanh::LeanObject = *_args.add(1);
    let mut v___x_7125_: *mut crate::leanh::LeanObject = *_args.add(2);
    let mut v___x_7126_: *mut crate::leanh::LeanObject = *_args.add(3);
    let mut v___x_7127_: *mut crate::leanh::LeanObject = *_args.add(4);
    let mut v___x_7128_: *mut crate::leanh::LeanObject = *_args.add(5);
    let mut v___x_7129_: *mut crate::leanh::LeanObject = *_args.add(6);
    let mut v___x_7130_: *mut crate::leanh::LeanObject = *_args.add(7);
    let mut v_useReducible_7131_: *mut crate::leanh::LeanObject = *_args.add(8);
    let mut v___f_7132_: *mut crate::leanh::LeanObject = *_args.add(9);
    let mut v___x_7133_: *mut crate::leanh::LeanObject = *_args.add(10);
    let mut v___x_7134_: *mut crate::leanh::LeanObject = *_args.add(11);
    let mut v___x_7135_: *mut crate::leanh::LeanObject = *_args.add(12);
    let mut v___x_7136_: *mut crate::leanh::LeanObject = *_args.add(13);
    let mut v___x_7137_: *mut crate::leanh::LeanObject = *_args.add(14);
    let mut v___x_7138_: *mut crate::leanh::LeanObject = *_args.add(15);
    let mut v_usingArg_7139_: *mut crate::leanh::LeanObject = *_args.add(16);
    let mut v___x_7140_: *mut crate::leanh::LeanObject = *_args.add(17);
    let mut v___x_7141_: *mut crate::leanh::LeanObject = *_args.add(18);
    let mut v_usingTk_x3f_7142_: *mut crate::leanh::LeanObject = *_args.add(19);
    let mut v_squeeze_7143_: *mut crate::leanh::LeanObject = *_args.add(20);
    let mut v_unfold_7144_: *mut crate::leanh::LeanObject = *_args.add(21);
    let mut v_args_7145_: *mut crate::leanh::LeanObject = *_args.add(22);
    let mut v_only_7146_: *mut crate::leanh::LeanObject = *_args.add(23);
    let mut v___y_7147_: *mut crate::leanh::LeanObject = *_args.add(24);
    let mut v___y_7148_: *mut crate::leanh::LeanObject = *_args.add(25);
    let mut v___y_7149_: *mut crate::leanh::LeanObject = *_args.add(26);
    let mut v___y_7150_: *mut crate::leanh::LeanObject = *_args.add(27);
    let mut v___y_7151_: *mut crate::leanh::LeanObject = *_args.add(28);
    let mut v___y_7152_: *mut crate::leanh::LeanObject = *_args.add(29);
    let mut v___y_7153_: *mut crate::leanh::LeanObject = *_args.add(30);
    let mut v___y_7154_: *mut crate::leanh::LeanObject = *_args.add(31);
    let mut v___y_7155_: *mut crate::leanh::LeanObject = *_args.add(32);
    let mut v___y_7156_: *mut crate::leanh::LeanObject = *_args.add(33);
    let mut v___x_96894__boxed_7157_: u8 = 0;
    let mut v_useReducible_boxed_7158_: u8 = 0;
    let mut v___x_96905__boxed_7159_: u8 = 0;
    let mut v_res_7160_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_96894__boxed_7157_ = (crate::leanh::lean_unbox(v___x_7128_) as u8);
    v_useReducible_boxed_7158_ = (crate::leanh::lean_unbox(v_useReducible_7131_) as u8);
    v___x_96905__boxed_7159_ = (crate::leanh::lean_unbox(v___x_7141_) as u8);
    v_res_7160_ =
        l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6(
            v_tk_7123_,
            v___x_7124_,
            v___x_7125_,
            v___x_7126_,
            v___x_7127_,
            v___x_96894__boxed_7157_,
            v___x_7129_,
            v___x_7130_,
            v_useReducible_boxed_7158_,
            v___f_7132_,
            v___x_7133_,
            v___x_7134_,
            v___x_7135_,
            v___x_7136_,
            v___x_7137_,
            v___x_7138_,
            v_usingArg_7139_,
            v___x_7140_,
            v___x_96905__boxed_7159_,
            v_usingTk_x3f_7142_,
            v_squeeze_7143_,
            v_unfold_7144_,
            v_args_7145_,
            v_only_7146_,
            v___y_7147_,
            v___y_7148_,
            v___y_7149_,
            v___y_7150_,
            v___y_7151_,
            v___y_7152_,
            v___y_7153_,
            v___y_7154_,
            v___y_7155_,
        );
    crate::leanh::lean_dec(v_only_7146_);
    crate::leanh::lean_dec(v_args_7145_);
    crate::leanh::lean_dec(v_unfold_7144_);
    crate::leanh::lean_dec(v_squeeze_7143_);
    crate::leanh::lean_dec(v___x_7137_);
    crate::leanh::lean_dec(v___x_7135_);
    crate::leanh::lean_dec(v___x_7134_);
    return v_res_7160_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore(
    mut v_useReducible_7187_: u8,
    mut v_stx_7188_: *mut crate::leanh::LeanObject,
    mut v_a_7189_: *mut crate::leanh::LeanObject,
    mut v_a_7190_: *mut crate::leanh::LeanObject,
    mut v_a_7191_: *mut crate::leanh::LeanObject,
    mut v_a_7192_: *mut crate::leanh::LeanObject,
    mut v_a_7193_: *mut crate::leanh::LeanObject,
    mut v_a_7194_: *mut crate::leanh::LeanObject,
    mut v_a_7195_: *mut crate::leanh::LeanObject,
    mut v_a_7196_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_7198_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7199_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7200_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7201_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7202_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7203_: u8 = 0;
    let mut v___x_7204_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_7205_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7206_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tk_7207_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7208_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7210_: u8 = 0;
    let mut v___y_7211_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7212_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7213_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7214_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7215_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7216_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7217_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7218_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7219_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7220_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7221_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7222_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7223_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7224_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7225_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7226_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7227_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7228_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7229_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7230_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7231_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7232_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7233_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7234_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_7235_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7236_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7237_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7239_: u8 = 0;
    let mut v___y_7240_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7241_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7242_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7243_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7244_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7245_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7246_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7247_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7248_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7249_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7250_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7251_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7252_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7253_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7254_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7255_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7256_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7257_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7258_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_usingTk_x3f_7259_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_usingArg_7260_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7261_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7262_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_7263_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7265_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7266_: u8 = 0;
    let mut v___x_7268_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7269_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7270_: u8 = 0;
    let mut v___y_7272_: u8 = 0;
    let mut v___y_7273_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7274_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7275_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7276_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7277_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7278_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7279_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7280_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7281_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7282_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7283_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7284_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7285_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7286_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7287_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7288_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7289_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7290_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7291_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_args_7292_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7293_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7294_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7295_: u8 = 0;
    let mut v___x_7296_: u8 = 0;
    let mut v___x_7297_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_usingTk_x3f_7298_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_usingArg_7299_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7300_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7301_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7302_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7304_: u8 = 0;
    let mut v___y_7305_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7306_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7307_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7308_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7309_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7310_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7311_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7312_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7313_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7314_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7315_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_only_7316_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7317_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7318_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7319_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7320_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7321_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7322_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7323_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7324_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7325_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7326_: u8 = 0;
    let mut v___x_7327_: u8 = 0;
    let mut v___x_7328_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7329_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7330_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7331_: u8 = 0;
    let mut v___x_7332_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7333_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_args_7334_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7335_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7336_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7338_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7339_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7340_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7341_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7342_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7343_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7344_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7345_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7346_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7347_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unfold_7348_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7349_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7350_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7351_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7352_: u8 = 0;
    let mut v___x_7353_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7354_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7355_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7356_: u8 = 0;
    let mut v___x_7357_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7358_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7359_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7360_: u8 = 0;
    let mut v___x_7361_: u8 = 0;
    let mut v___x_7362_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_only_7363_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7364_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7365_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_squeeze_7367_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7368_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7369_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7370_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7371_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7372_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7373_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7374_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7375_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7376_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7377_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7378_: u8 = 0;
    let mut v___x_7379_: u8 = 0;
    let mut v___x_7380_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unfold_7381_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7382_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7383_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7384_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7385_: u8 = 0;
    let mut v___x_7386_: u8 = 0;
    let mut v___x_7387_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_squeeze_7388_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7389_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7390_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_7198_ = l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___closed__0;
                v___x_7199_ = l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___closed__1;
                v___x_7200_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4_spec__7_spec__16___redArg___lam__0___closed__1;
                v___x_7201_ = l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___closed__2;
                v___x_7202_ = l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___closed__3;
                crate::leanh::lean_inc(v_stx_7188_);
                v___x_7203_ = l_Lean_Syntax_isOfKind(v_stx_7188_, v___x_7202_);
                if v___x_7203_ == 0 {
                    crate::leanh::lean_dec(v_stx_7188_);
                    v___x_7204_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__0___redArg();
                    return v___x_7204_;
                } else {
                    v___f_7205_ = l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___closed__4;
                    v___x_7206_ = crate::leanh::lean_unsigned_to_nat(0);
                    v_tk_7207_ = l_Lean_Syntax_getArg(v_stx_7188_, v___x_7206_);
                    v___x_7208_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_7384_ = l_Lean_Syntax_getArg(v_stx_7188_, v___x_7208_);
                    v___x_7385_ = l_Lean_Syntax_isNone(v___x_7384_);
                    if v___x_7385_ == 0 {
                        crate::leanh::lean_inc(v___x_7384_);
                        v___x_7386_ = l_Lean_Syntax_matchesNull(v___x_7384_, v___x_7208_);
                        if v___x_7386_ == 0 {
                            crate::leanh::lean_dec(v___x_7384_);
                            crate::leanh::lean_dec(v_tk_7207_);
                            crate::leanh::lean_dec(v_stx_7188_);
                            v___x_7387_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__0___redArg();
                            return v___x_7387_;
                        } else {
                            v_squeeze_7388_ = l_Lean_Syntax_getArg(v___x_7384_, v___x_7206_);
                            crate::leanh::lean_dec(v___x_7384_);
                            v___x_7389_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_7389_, 0, v_squeeze_7388_);
                            v_squeeze_7367_ = v___x_7389_;
                            v___y_7368_ = v_a_7189_;
                            v___y_7369_ = v_a_7190_;
                            v___y_7370_ = v_a_7191_;
                            v___y_7371_ = v_a_7192_;
                            v___y_7372_ = v_a_7193_;
                            v___y_7373_ = v_a_7194_;
                            v___y_7374_ = v_a_7195_;
                            v___y_7375_ = v_a_7196_;
                            state = 8;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec(v___x_7384_);
                        v___x_7390_ = crate::leanh::lean_box(0);
                        v_squeeze_7367_ = v___x_7390_;
                        v___y_7368_ = v_a_7189_;
                        v___y_7369_ = v_a_7190_;
                        v___y_7370_ = v_a_7191_;
                        v___y_7371_ = v_a_7192_;
                        v___y_7372_ = v_a_7193_;
                        v___y_7373_ = v_a_7194_;
                        v___y_7374_ = v_a_7195_;
                        v___y_7375_ = v_a_7196_;
                        state = 8;
                        continue;
                    }
                }
            }
            1 => {
                v___x_7232_ = crate::leanh::lean_box((v___x_7203_) as usize);
                v___x_7233_ = crate::leanh::lean_box((v_useReducible_7187_) as usize);
                v___x_7234_ = crate::leanh::lean_box((v___y_7210_) as usize);
                crate::leanh::lean_inc(v___y_7214_);
                crate::leanh::lean_inc(v___y_7211_);
                v___f_7235_ = crate::leanh::lean_alloc_closure(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___boxed as *mut core::ffi::c_void, 34, 25);
                crate::leanh::lean_closure_set(v___f_7235_, 0, v_tk_7207_);
                crate::leanh::lean_closure_set(v___f_7235_, 1, v___x_7198_);
                crate::leanh::lean_closure_set(v___f_7235_, 2, v___x_7199_);
                crate::leanh::lean_closure_set(v___f_7235_, 3, v___x_7200_);
                crate::leanh::lean_closure_set(v___f_7235_, 4, v___x_7206_);
                crate::leanh::lean_closure_set(v___f_7235_, 5, v___x_7232_);
                crate::leanh::lean_closure_set(v___f_7235_, 6, v___y_7211_);
                crate::leanh::lean_closure_set(v___f_7235_, 7, v___x_7202_);
                crate::leanh::lean_closure_set(v___f_7235_, 8, v___x_7233_);
                crate::leanh::lean_closure_set(v___f_7235_, 9, v___f_7205_);
                crate::leanh::lean_closure_set(v___f_7235_, 10, v___x_7201_);
                crate::leanh::lean_closure_set(v___f_7235_, 11, v___y_7225_);
                crate::leanh::lean_closure_set(v___f_7235_, 12, v___y_7226_);
                crate::leanh::lean_closure_set(v___f_7235_, 13, v___x_7208_);
                crate::leanh::lean_closure_set(v___f_7235_, 14, v___y_7214_);
                crate::leanh::lean_closure_set(v___f_7235_, 15, v___y_7216_);
                crate::leanh::lean_closure_set(v___f_7235_, 16, v___y_7223_);
                crate::leanh::lean_closure_set(v___f_7235_, 17, v___y_7227_);
                crate::leanh::lean_closure_set(v___f_7235_, 18, v___x_7234_);
                crate::leanh::lean_closure_set(v___f_7235_, 19, v___y_7215_);
                crate::leanh::lean_closure_set(v___f_7235_, 20, v___y_7224_);
                crate::leanh::lean_closure_set(v___f_7235_, 21, v___y_7228_);
                crate::leanh::lean_closure_set(v___f_7235_, 22, v___y_7218_);
                crate::leanh::lean_closure_set(v___f_7235_, 23, v___y_7217_);
                crate::leanh::lean_closure_set(v___f_7235_, 24, v___y_7231_);
                v___x_7236_ = crate::leanh::lean_alloc_closure(
                    l_Lean_Elab_Tactic_withSimpDiagnostics___boxed as *mut core::ffi::c_void,
                    10,
                    1,
                );
                crate::leanh::lean_closure_set(v___x_7236_, 0, v___f_7235_);
                v___x_7237_ = l_Lean_Elab_Tactic_focus___redArg(
                    v___x_7236_,
                    v___y_7221_,
                    v___y_7212_,
                    v___y_7229_,
                    v___y_7220_,
                    v___y_7222_,
                    v___y_7230_,
                    v___y_7219_,
                    v___y_7213_,
                );
                return v___x_7237_;
            }
            2 => {
                v___x_7261_ = l_Lean_Syntax_getOptional_x3f(v___y_7244_);
                crate::leanh::lean_dec(v___y_7244_);
                if crate::leanh::lean_obj_tag(v___x_7261_) == 0 {
                    v___x_7262_ = crate::leanh::lean_box(0);
                    v___y_7210_ = v___y_7239_;
                    v___y_7211_ = v___y_7240_;
                    v___y_7212_ = v___y_7241_;
                    v___y_7213_ = v___y_7242_;
                    v___y_7214_ = v___y_7243_;
                    v___y_7215_ = v_usingTk_x3f_7259_;
                    v___y_7216_ = v___y_7245_;
                    v___y_7217_ = v___y_7246_;
                    v___y_7218_ = v___y_7247_;
                    v___y_7219_ = v___y_7248_;
                    v___y_7220_ = v___y_7249_;
                    v___y_7221_ = v___y_7250_;
                    v___y_7222_ = v___y_7251_;
                    v___y_7223_ = v_usingArg_7260_;
                    v___y_7224_ = v___y_7252_;
                    v___y_7225_ = v___y_7255_;
                    v___y_7226_ = v___y_7254_;
                    v___y_7227_ = v___y_7253_;
                    v___y_7228_ = v___y_7256_;
                    v___y_7229_ = v___y_7257_;
                    v___y_7230_ = v___y_7258_;
                    v___y_7231_ = v___x_7262_;
                    state = 1;
                    continue;
                } else {
                    v_val_7263_ = crate::leanh::lean_ctor_get(v___x_7261_, 0);
                    v_isSharedCheck_7270_ = (!crate::leanh::lean_is_exclusive(v___x_7261_)) as u8;
                    if v_isSharedCheck_7270_ == 0 {
                        v___x_7265_ = v___x_7261_;
                        v_isShared_7266_ = v_isSharedCheck_7270_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_val_7263_);
                        crate::leanh::lean_dec(v___x_7261_);
                        v___x_7265_ = crate::leanh::lean_box(0);
                        v_isShared_7266_ = v_isSharedCheck_7270_;
                        state = 3;
                        continue;
                    }
                }
            }
            3 => {
                if v_isShared_7266_ == 0 {
                    v___x_7268_ = v___x_7265_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_7269_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7269_, 0, v_val_7263_);
                    v___x_7268_ = v_reuseFailAlloc_7269_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___y_7210_ = v___y_7239_;
                v___y_7211_ = v___y_7240_;
                v___y_7212_ = v___y_7241_;
                v___y_7213_ = v___y_7242_;
                v___y_7214_ = v___y_7243_;
                v___y_7215_ = v_usingTk_x3f_7259_;
                v___y_7216_ = v___y_7245_;
                v___y_7217_ = v___y_7246_;
                v___y_7218_ = v___y_7247_;
                v___y_7219_ = v___y_7248_;
                v___y_7220_ = v___y_7249_;
                v___y_7221_ = v___y_7250_;
                v___y_7222_ = v___y_7251_;
                v___y_7223_ = v_usingArg_7260_;
                v___y_7224_ = v___y_7252_;
                v___y_7225_ = v___y_7255_;
                v___y_7226_ = v___y_7254_;
                v___y_7227_ = v___y_7253_;
                v___y_7228_ = v___y_7256_;
                v___y_7229_ = v___y_7257_;
                v___y_7230_ = v___y_7258_;
                v___y_7231_ = v___x_7268_;
                state = 1;
                continue;
            }
            5 => {
                v___x_7293_ = crate::leanh::lean_unsigned_to_nat(4);
                v___x_7294_ = l_Lean_Syntax_getArg(v___y_7291_, v___x_7293_);
                crate::leanh::lean_dec(v___y_7291_);
                v___x_7295_ = l_Lean_Syntax_isNone(v___x_7294_);
                if v___x_7295_ == 0 {
                    crate::leanh::lean_inc(v___x_7294_);
                    v___x_7296_ = l_Lean_Syntax_matchesNull(v___x_7294_, v___y_7280_);
                    crate::leanh::lean_dec(v___y_7280_);
                    if v___x_7296_ == 0 {
                        crate::leanh::lean_dec(v___x_7294_);
                        crate::leanh::lean_dec(v_args_7292_);
                        crate::leanh::lean_dec(v___y_7288_);
                        crate::leanh::lean_dec(v___y_7287_);
                        crate::leanh::lean_dec(v___y_7286_);
                        crate::leanh::lean_dec(v___y_7285_);
                        crate::leanh::lean_dec(v___y_7279_);
                        crate::leanh::lean_dec(v___y_7278_);
                        crate::leanh::lean_dec(v___y_7277_);
                        crate::leanh::lean_dec(v_tk_7207_);
                        v___x_7297_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__0___redArg();
                        return v___x_7297_;
                    } else {
                        v_usingTk_x3f_7298_ = l_Lean_Syntax_getArg(v___x_7294_, v___x_7206_);
                        v_usingArg_7299_ = l_Lean_Syntax_getArg(v___x_7294_, v___x_7208_);
                        crate::leanh::lean_dec(v___x_7294_);
                        v___x_7300_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_7300_, 0, v_usingTk_x3f_7298_);
                        v___x_7301_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_7301_, 0, v_usingArg_7299_);
                        v___y_7239_ = v___y_7272_;
                        v___y_7240_ = v___y_7273_;
                        v___y_7241_ = v___y_7274_;
                        v___y_7242_ = v___y_7275_;
                        v___y_7243_ = v___y_7276_;
                        v___y_7244_ = v___y_7277_;
                        v___y_7245_ = v___y_7278_;
                        v___y_7246_ = v___y_7279_;
                        v___y_7247_ = v_args_7292_;
                        v___y_7248_ = v___y_7281_;
                        v___y_7249_ = v___y_7282_;
                        v___y_7250_ = v___y_7283_;
                        v___y_7251_ = v___y_7284_;
                        v___y_7252_ = v___y_7285_;
                        v___y_7253_ = v___y_7287_;
                        v___y_7254_ = v___y_7286_;
                        v___y_7255_ = v___x_7293_;
                        v___y_7256_ = v___y_7288_;
                        v___y_7257_ = v___y_7289_;
                        v___y_7258_ = v___y_7290_;
                        v_usingTk_x3f_7259_ = v___x_7300_;
                        v_usingArg_7260_ = v___x_7301_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v___x_7294_);
                    crate::leanh::lean_dec(v___y_7280_);
                    v___x_7302_ = crate::leanh::lean_box(0);
                    v___y_7239_ = v___y_7272_;
                    v___y_7240_ = v___y_7273_;
                    v___y_7241_ = v___y_7274_;
                    v___y_7242_ = v___y_7275_;
                    v___y_7243_ = v___y_7276_;
                    v___y_7244_ = v___y_7277_;
                    v___y_7245_ = v___y_7278_;
                    v___y_7246_ = v___y_7279_;
                    v___y_7247_ = v_args_7292_;
                    v___y_7248_ = v___y_7281_;
                    v___y_7249_ = v___y_7282_;
                    v___y_7250_ = v___y_7283_;
                    v___y_7251_ = v___y_7284_;
                    v___y_7252_ = v___y_7285_;
                    v___y_7253_ = v___y_7287_;
                    v___y_7254_ = v___y_7286_;
                    v___y_7255_ = v___x_7293_;
                    v___y_7256_ = v___y_7288_;
                    v___y_7257_ = v___y_7289_;
                    v___y_7258_ = v___y_7290_;
                    v_usingTk_x3f_7259_ = v___x_7302_;
                    v_usingArg_7260_ = v___x_7302_;
                    state = 2;
                    continue;
                }
            }
            6 => {
                v___x_7325_ = l_Lean_Syntax_getArg(v___y_7314_, v___y_7313_);
                crate::leanh::lean_dec(v___y_7313_);
                v___x_7326_ = l_Lean_Syntax_isNone(v___x_7325_);
                if v___x_7326_ == 0 {
                    crate::leanh::lean_inc(v___x_7325_);
                    v___x_7327_ = l_Lean_Syntax_matchesNull(v___x_7325_, v___x_7208_);
                    if v___x_7327_ == 0 {
                        crate::leanh::lean_dec(v___x_7325_);
                        crate::leanh::lean_dec(v_only_7316_);
                        crate::leanh::lean_dec(v___y_7315_);
                        crate::leanh::lean_dec(v___y_7314_);
                        crate::leanh::lean_dec(v___y_7312_);
                        crate::leanh::lean_dec(v___y_7311_);
                        crate::leanh::lean_dec(v___y_7309_);
                        crate::leanh::lean_dec(v___y_7308_);
                        crate::leanh::lean_dec(v___y_7307_);
                        crate::leanh::lean_dec(v___y_7306_);
                        crate::leanh::lean_dec(v_tk_7207_);
                        v___x_7328_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__0___redArg();
                        return v___x_7328_;
                    } else {
                        v___x_7329_ = l_Lean_Syntax_getArg(v___x_7325_, v___x_7206_);
                        crate::leanh::lean_dec(v___x_7325_);
                        v___x_7330_ = l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___closed__5;
                        crate::leanh::lean_inc(v___x_7329_);
                        v___x_7331_ = l_Lean_Syntax_isOfKind(v___x_7329_, v___x_7330_);
                        if v___x_7331_ == 0 {
                            crate::leanh::lean_dec(v___x_7329_);
                            crate::leanh::lean_dec(v_only_7316_);
                            crate::leanh::lean_dec(v___y_7315_);
                            crate::leanh::lean_dec(v___y_7314_);
                            crate::leanh::lean_dec(v___y_7312_);
                            crate::leanh::lean_dec(v___y_7311_);
                            crate::leanh::lean_dec(v___y_7309_);
                            crate::leanh::lean_dec(v___y_7308_);
                            crate::leanh::lean_dec(v___y_7307_);
                            crate::leanh::lean_dec(v___y_7306_);
                            crate::leanh::lean_dec(v_tk_7207_);
                            v___x_7332_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__0___redArg();
                            return v___x_7332_;
                        } else {
                            v___x_7333_ = l_Lean_Syntax_getArg(v___x_7329_, v___x_7208_);
                            crate::leanh::lean_dec(v___x_7329_);
                            v_args_7334_ = l_Lean_Syntax_getArgs(v___x_7333_);
                            crate::leanh::lean_dec(v___x_7333_);
                            v___x_7335_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_7335_, 0, v_args_7334_);
                            v___y_7272_ = v___y_7304_;
                            v___y_7273_ = v___y_7305_;
                            v___y_7274_ = v___y_7318_;
                            v___y_7275_ = v___y_7324_;
                            v___y_7276_ = v___y_7310_;
                            v___y_7277_ = v___y_7312_;
                            v___y_7278_ = v___y_7311_;
                            v___y_7279_ = v_only_7316_;
                            v___y_7280_ = v___y_7315_;
                            v___y_7281_ = v___y_7323_;
                            v___y_7282_ = v___y_7320_;
                            v___y_7283_ = v___y_7317_;
                            v___y_7284_ = v___y_7321_;
                            v___y_7285_ = v___y_7306_;
                            v___y_7286_ = v___y_7308_;
                            v___y_7287_ = v___y_7307_;
                            v___y_7288_ = v___y_7309_;
                            v___y_7289_ = v___y_7319_;
                            v___y_7290_ = v___y_7322_;
                            v___y_7291_ = v___y_7314_;
                            v_args_7292_ = v___x_7335_;
                            state = 5;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec(v___x_7325_);
                    v___x_7336_ = crate::leanh::lean_box(0);
                    v___y_7272_ = v___y_7304_;
                    v___y_7273_ = v___y_7305_;
                    v___y_7274_ = v___y_7318_;
                    v___y_7275_ = v___y_7324_;
                    v___y_7276_ = v___y_7310_;
                    v___y_7277_ = v___y_7312_;
                    v___y_7278_ = v___y_7311_;
                    v___y_7279_ = v_only_7316_;
                    v___y_7280_ = v___y_7315_;
                    v___y_7281_ = v___y_7323_;
                    v___y_7282_ = v___y_7320_;
                    v___y_7283_ = v___y_7317_;
                    v___y_7284_ = v___y_7321_;
                    v___y_7285_ = v___y_7306_;
                    v___y_7286_ = v___y_7308_;
                    v___y_7287_ = v___y_7307_;
                    v___y_7288_ = v___y_7309_;
                    v___y_7289_ = v___y_7319_;
                    v___y_7290_ = v___y_7322_;
                    v___y_7291_ = v___y_7314_;
                    v_args_7292_ = v___x_7336_;
                    state = 5;
                    continue;
                }
            }
            7 => {
                v___x_7349_ = crate::leanh::lean_unsigned_to_nat(3);
                v___x_7350_ = l_Lean_Syntax_getArg(v_stx_7188_, v___x_7349_);
                crate::leanh::lean_dec(v_stx_7188_);
                v___x_7351_ = l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___closed__7;
                crate::leanh::lean_inc(v___x_7350_);
                v___x_7352_ = l_Lean_Syntax_isOfKind(v___x_7350_, v___x_7351_);
                if v___x_7352_ == 0 {
                    crate::leanh::lean_dec(v___x_7350_);
                    crate::leanh::lean_dec(v_unfold_7348_);
                    crate::leanh::lean_dec(v___y_7347_);
                    crate::leanh::lean_dec(v___y_7340_);
                    crate::leanh::lean_dec(v_tk_7207_);
                    v___x_7353_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__0___redArg();
                    return v___x_7353_;
                } else {
                    v___x_7354_ = l_Lean_Syntax_getArg(v___x_7350_, v___x_7206_);
                    v___x_7355_ = l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___closed__9;
                    crate::leanh::lean_inc(v___x_7354_);
                    v___x_7356_ = l_Lean_Syntax_isOfKind(v___x_7354_, v___x_7355_);
                    if v___x_7356_ == 0 {
                        crate::leanh::lean_dec(v___x_7354_);
                        crate::leanh::lean_dec(v___x_7350_);
                        crate::leanh::lean_dec(v_unfold_7348_);
                        crate::leanh::lean_dec(v___y_7347_);
                        crate::leanh::lean_dec(v___y_7340_);
                        crate::leanh::lean_dec(v_tk_7207_);
                        v___x_7357_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__0___redArg();
                        return v___x_7357_;
                    } else {
                        v___x_7358_ = l_Lean_Syntax_getArg(v___x_7350_, v___x_7208_);
                        v___x_7359_ = l_Lean_Syntax_getArg(v___x_7350_, v___y_7347_);
                        v___x_7360_ = l_Lean_Syntax_isNone(v___x_7359_);
                        if v___x_7360_ == 0 {
                            crate::leanh::lean_inc(v___x_7359_);
                            v___x_7361_ = l_Lean_Syntax_matchesNull(v___x_7359_, v___x_7208_);
                            if v___x_7361_ == 0 {
                                crate::leanh::lean_dec(v___x_7359_);
                                crate::leanh::lean_dec(v___x_7358_);
                                crate::leanh::lean_dec(v___x_7354_);
                                crate::leanh::lean_dec(v___x_7350_);
                                crate::leanh::lean_dec(v_unfold_7348_);
                                crate::leanh::lean_dec(v___y_7347_);
                                crate::leanh::lean_dec(v___y_7340_);
                                crate::leanh::lean_dec(v_tk_7207_);
                                v___x_7362_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__0___redArg();
                                return v___x_7362_;
                            } else {
                                v_only_7363_ = l_Lean_Syntax_getArg(v___x_7359_, v___x_7206_);
                                crate::leanh::lean_dec(v___x_7359_);
                                v___x_7364_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                                crate::leanh::lean_ctor_set(v___x_7364_, 0, v_only_7363_);
                                crate::leanh::lean_inc(v___y_7347_);
                                v___y_7304_ = v___x_7356_;
                                v___y_7305_ = v___x_7351_;
                                v___y_7306_ = v___y_7340_;
                                v___y_7307_ = v___x_7354_;
                                v___y_7308_ = v___x_7349_;
                                v___y_7309_ = v_unfold_7348_;
                                v___y_7310_ = v___x_7355_;
                                v___y_7311_ = v___y_7347_;
                                v___y_7312_ = v___x_7358_;
                                v___y_7313_ = v___x_7349_;
                                v___y_7314_ = v___x_7350_;
                                v___y_7315_ = v___y_7347_;
                                v_only_7316_ = v___x_7364_;
                                v___y_7317_ = v___y_7346_;
                                v___y_7318_ = v___y_7342_;
                                v___y_7319_ = v___y_7345_;
                                v___y_7320_ = v___y_7339_;
                                v___y_7321_ = v___y_7344_;
                                v___y_7322_ = v___y_7338_;
                                v___y_7323_ = v___y_7341_;
                                v___y_7324_ = v___y_7343_;
                                state = 6;
                                continue;
                            }
                        } else {
                            crate::leanh::lean_dec(v___x_7359_);
                            v___x_7365_ = crate::leanh::lean_box(0);
                            crate::leanh::lean_inc(v___y_7347_);
                            v___y_7304_ = v___x_7356_;
                            v___y_7305_ = v___x_7351_;
                            v___y_7306_ = v___y_7340_;
                            v___y_7307_ = v___x_7354_;
                            v___y_7308_ = v___x_7349_;
                            v___y_7309_ = v_unfold_7348_;
                            v___y_7310_ = v___x_7355_;
                            v___y_7311_ = v___y_7347_;
                            v___y_7312_ = v___x_7358_;
                            v___y_7313_ = v___x_7349_;
                            v___y_7314_ = v___x_7350_;
                            v___y_7315_ = v___y_7347_;
                            v_only_7316_ = v___x_7365_;
                            v___y_7317_ = v___y_7346_;
                            v___y_7318_ = v___y_7342_;
                            v___y_7319_ = v___y_7345_;
                            v___y_7320_ = v___y_7339_;
                            v___y_7321_ = v___y_7344_;
                            v___y_7322_ = v___y_7338_;
                            v___y_7323_ = v___y_7341_;
                            v___y_7324_ = v___y_7343_;
                            state = 6;
                            continue;
                        }
                    }
                }
            }
            8 => {
                v___x_7376_ = crate::leanh::lean_unsigned_to_nat(2);
                v___x_7377_ = l_Lean_Syntax_getArg(v_stx_7188_, v___x_7376_);
                v___x_7378_ = l_Lean_Syntax_isNone(v___x_7377_);
                if v___x_7378_ == 0 {
                    crate::leanh::lean_inc(v___x_7377_);
                    v___x_7379_ = l_Lean_Syntax_matchesNull(v___x_7377_, v___x_7208_);
                    if v___x_7379_ == 0 {
                        crate::leanh::lean_dec(v___x_7377_);
                        crate::leanh::lean_dec(v_squeeze_7367_);
                        crate::leanh::lean_dec(v_tk_7207_);
                        crate::leanh::lean_dec(v_stx_7188_);
                        v___x_7380_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__0___redArg();
                        return v___x_7380_;
                    } else {
                        v_unfold_7381_ = l_Lean_Syntax_getArg(v___x_7377_, v___x_7206_);
                        crate::leanh::lean_dec(v___x_7377_);
                        v___x_7382_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_7382_, 0, v_unfold_7381_);
                        v___y_7338_ = v___y_7373_;
                        v___y_7339_ = v___y_7371_;
                        v___y_7340_ = v_squeeze_7367_;
                        v___y_7341_ = v___y_7374_;
                        v___y_7342_ = v___y_7369_;
                        v___y_7343_ = v___y_7375_;
                        v___y_7344_ = v___y_7372_;
                        v___y_7345_ = v___y_7370_;
                        v___y_7346_ = v___y_7368_;
                        v___y_7347_ = v___x_7376_;
                        v_unfold_7348_ = v___x_7382_;
                        state = 7;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v___x_7377_);
                    v___x_7383_ = crate::leanh::lean_box(0);
                    v___y_7338_ = v___y_7373_;
                    v___y_7339_ = v___y_7371_;
                    v___y_7340_ = v_squeeze_7367_;
                    v___y_7341_ = v___y_7374_;
                    v___y_7342_ = v___y_7369_;
                    v___y_7343_ = v___y_7375_;
                    v___y_7344_ = v___y_7372_;
                    v___y_7345_ = v___y_7370_;
                    v___y_7346_ = v___y_7368_;
                    v___y_7347_ = v___x_7376_;
                    v_unfold_7348_ = v___x_7383_;
                    state = 7;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___boxed(
    mut v_useReducible_7391_: *mut crate::leanh::LeanObject,
    mut v_stx_7392_: *mut crate::leanh::LeanObject,
    mut v_a_7393_: *mut crate::leanh::LeanObject,
    mut v_a_7394_: *mut crate::leanh::LeanObject,
    mut v_a_7395_: *mut crate::leanh::LeanObject,
    mut v_a_7396_: *mut crate::leanh::LeanObject,
    mut v_a_7397_: *mut crate::leanh::LeanObject,
    mut v_a_7398_: *mut crate::leanh::LeanObject,
    mut v_a_7399_: *mut crate::leanh::LeanObject,
    mut v_a_7400_: *mut crate::leanh::LeanObject,
    mut v_a_7401_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_useReducible_boxed_7402_: u8 = 0;
    let mut v_res_7403_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_useReducible_boxed_7402_ = (crate::leanh::lean_unbox(v_useReducible_7391_) as u8);
    v_res_7403_ = l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore(
        v_useReducible_boxed_7402_,
        v_stx_7392_,
        v_a_7393_,
        v_a_7394_,
        v_a_7395_,
        v_a_7396_,
        v_a_7397_,
        v_a_7398_,
        v_a_7399_,
        v_a_7400_,
    );
    crate::leanh::lean_dec(v_a_7400_);
    crate::leanh::lean_dec_ref(v_a_7399_);
    crate::leanh::lean_dec(v_a_7398_);
    crate::leanh::lean_dec_ref(v_a_7397_);
    crate::leanh::lean_dec(v_a_7396_);
    crate::leanh::lean_dec_ref(v_a_7395_);
    crate::leanh::lean_dec(v_a_7394_);
    crate::leanh::lean_dec_ref(v_a_7393_);
    return v_res_7403_;
}
pub unsafe fn l_Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__2(
    mut v_mvarId_7404_: *mut crate::leanh::LeanObject,
    mut v_val_7405_: *mut crate::leanh::LeanObject,
    mut v___y_7406_: *mut crate::leanh::LeanObject,
    mut v___y_7407_: *mut crate::leanh::LeanObject,
    mut v___y_7408_: *mut crate::leanh::LeanObject,
    mut v___y_7409_: *mut crate::leanh::LeanObject,
    mut v___y_7410_: *mut crate::leanh::LeanObject,
    mut v___y_7411_: *mut crate::leanh::LeanObject,
    mut v___y_7412_: *mut crate::leanh::LeanObject,
    mut v___y_7413_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_7415_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_7415_ = l_Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__2___redArg(v_mvarId_7404_, v_val_7405_, v___y_7411_);
    return v___x_7415_;
}
pub unsafe fn l_Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__2___boxed(
    mut v_mvarId_7416_: *mut crate::leanh::LeanObject,
    mut v_val_7417_: *mut crate::leanh::LeanObject,
    mut v___y_7418_: *mut crate::leanh::LeanObject,
    mut v___y_7419_: *mut crate::leanh::LeanObject,
    mut v___y_7420_: *mut crate::leanh::LeanObject,
    mut v___y_7421_: *mut crate::leanh::LeanObject,
    mut v___y_7422_: *mut crate::leanh::LeanObject,
    mut v___y_7423_: *mut crate::leanh::LeanObject,
    mut v___y_7424_: *mut crate::leanh::LeanObject,
    mut v___y_7425_: *mut crate::leanh::LeanObject,
    mut v___y_7426_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_7427_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_7427_ = l_Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__2(v_mvarId_7416_, v_val_7417_, v___y_7418_, v___y_7419_, v___y_7420_, v___y_7421_, v___y_7422_, v___y_7423_, v___y_7424_, v___y_7425_);
    crate::leanh::lean_dec(v___y_7425_);
    crate::leanh::lean_dec_ref(v___y_7424_);
    crate::leanh::lean_dec(v___y_7423_);
    crate::leanh::lean_dec_ref(v___y_7422_);
    crate::leanh::lean_dec(v___y_7421_);
    crate::leanh::lean_dec_ref(v___y_7420_);
    crate::leanh::lean_dec(v___y_7419_);
    crate::leanh::lean_dec_ref(v___y_7418_);
    return v_res_7427_;
}
pub unsafe fn l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__3_spec__5(
    mut v_o_7428_: *mut crate::leanh::LeanObject,
    mut v___y_7429_: *mut crate::leanh::LeanObject,
    mut v___y_7430_: *mut crate::leanh::LeanObject,
    mut v___y_7431_: *mut crate::leanh::LeanObject,
    mut v___y_7432_: *mut crate::leanh::LeanObject,
    mut v___y_7433_: *mut crate::leanh::LeanObject,
    mut v___y_7434_: *mut crate::leanh::LeanObject,
    mut v___y_7435_: *mut crate::leanh::LeanObject,
    mut v___y_7436_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_7438_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_7438_ = l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__3_spec__5___redArg(v_o_7428_, v___y_7436_);
    return v___x_7438_;
}
pub unsafe fn l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__3_spec__5___boxed(
    mut v_o_7439_: *mut crate::leanh::LeanObject,
    mut v___y_7440_: *mut crate::leanh::LeanObject,
    mut v___y_7441_: *mut crate::leanh::LeanObject,
    mut v___y_7442_: *mut crate::leanh::LeanObject,
    mut v___y_7443_: *mut crate::leanh::LeanObject,
    mut v___y_7444_: *mut crate::leanh::LeanObject,
    mut v___y_7445_: *mut crate::leanh::LeanObject,
    mut v___y_7446_: *mut crate::leanh::LeanObject,
    mut v___y_7447_: *mut crate::leanh::LeanObject,
    mut v___y_7448_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_7449_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_7449_ = l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__3_spec__5(v_o_7439_, v___y_7440_, v___y_7441_, v___y_7442_, v___y_7443_, v___y_7444_, v___y_7445_, v___y_7446_, v___y_7447_);
    crate::leanh::lean_dec(v___y_7447_);
    crate::leanh::lean_dec_ref(v___y_7446_);
    crate::leanh::lean_dec(v___y_7445_);
    crate::leanh::lean_dec_ref(v___y_7444_);
    crate::leanh::lean_dec(v___y_7443_);
    crate::leanh::lean_dec_ref(v___y_7442_);
    crate::leanh::lean_dec(v___y_7441_);
    crate::leanh::lean_dec_ref(v___y_7440_);
    return v_res_7449_;
}
pub unsafe fn l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__6(
    mut v_00_u03b1_7450_: *mut crate::leanh::LeanObject,
    mut v_msg_7451_: *mut crate::leanh::LeanObject,
    mut v___y_7452_: *mut crate::leanh::LeanObject,
    mut v___y_7453_: *mut crate::leanh::LeanObject,
    mut v___y_7454_: *mut crate::leanh::LeanObject,
    mut v___y_7455_: *mut crate::leanh::LeanObject,
    mut v___y_7456_: *mut crate::leanh::LeanObject,
    mut v___y_7457_: *mut crate::leanh::LeanObject,
    mut v___y_7458_: *mut crate::leanh::LeanObject,
    mut v___y_7459_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_7461_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_7461_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__6___redArg(v_msg_7451_, v___y_7456_, v___y_7457_, v___y_7458_, v___y_7459_);
    return v___x_7461_;
}
pub unsafe fn l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__6___boxed(
    mut v_00_u03b1_7462_: *mut crate::leanh::LeanObject,
    mut v_msg_7463_: *mut crate::leanh::LeanObject,
    mut v___y_7464_: *mut crate::leanh::LeanObject,
    mut v___y_7465_: *mut crate::leanh::LeanObject,
    mut v___y_7466_: *mut crate::leanh::LeanObject,
    mut v___y_7467_: *mut crate::leanh::LeanObject,
    mut v___y_7468_: *mut crate::leanh::LeanObject,
    mut v___y_7469_: *mut crate::leanh::LeanObject,
    mut v___y_7470_: *mut crate::leanh::LeanObject,
    mut v___y_7471_: *mut crate::leanh::LeanObject,
    mut v___y_7472_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_7473_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_7473_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__6(v_00_u03b1_7462_, v_msg_7463_, v___y_7464_, v___y_7465_, v___y_7466_, v___y_7467_, v___y_7468_, v___y_7469_, v___y_7470_, v___y_7471_);
    crate::leanh::lean_dec(v___y_7471_);
    crate::leanh::lean_dec_ref(v___y_7470_);
    crate::leanh::lean_dec(v___y_7469_);
    crate::leanh::lean_dec_ref(v___y_7468_);
    crate::leanh::lean_dec(v___y_7467_);
    crate::leanh::lean_dec_ref(v___y_7466_);
    crate::leanh::lean_dec(v___y_7465_);
    crate::leanh::lean_dec_ref(v___y_7464_);
    return v_res_7473_;
}
pub unsafe fn l_Lean_Elab_withInfoTreeContext___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__8(
    mut v_00_u03b1_7474_: *mut crate::leanh::LeanObject,
    mut v_x_7475_: *mut crate::leanh::LeanObject,
    mut v_mkInfoTree_7476_: *mut crate::leanh::LeanObject,
    mut v___y_7477_: *mut crate::leanh::LeanObject,
    mut v___y_7478_: *mut crate::leanh::LeanObject,
    mut v___y_7479_: *mut crate::leanh::LeanObject,
    mut v___y_7480_: *mut crate::leanh::LeanObject,
    mut v___y_7481_: *mut crate::leanh::LeanObject,
    mut v___y_7482_: *mut crate::leanh::LeanObject,
    mut v___y_7483_: *mut crate::leanh::LeanObject,
    mut v___y_7484_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_7486_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_7486_ = l_Lean_Elab_withInfoTreeContext___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__8___redArg(v_x_7475_, v_mkInfoTree_7476_, v___y_7477_, v___y_7478_, v___y_7479_, v___y_7480_, v___y_7481_, v___y_7482_, v___y_7483_, v___y_7484_);
    return v___x_7486_;
}
pub unsafe fn l_Lean_Elab_withInfoTreeContext___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__8___boxed(
    mut v_00_u03b1_7487_: *mut crate::leanh::LeanObject,
    mut v_x_7488_: *mut crate::leanh::LeanObject,
    mut v_mkInfoTree_7489_: *mut crate::leanh::LeanObject,
    mut v___y_7490_: *mut crate::leanh::LeanObject,
    mut v___y_7491_: *mut crate::leanh::LeanObject,
    mut v___y_7492_: *mut crate::leanh::LeanObject,
    mut v___y_7493_: *mut crate::leanh::LeanObject,
    mut v___y_7494_: *mut crate::leanh::LeanObject,
    mut v___y_7495_: *mut crate::leanh::LeanObject,
    mut v___y_7496_: *mut crate::leanh::LeanObject,
    mut v___y_7497_: *mut crate::leanh::LeanObject,
    mut v___y_7498_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_7499_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_7499_ = l_Lean_Elab_withInfoTreeContext___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__8(v_00_u03b1_7487_, v_x_7488_, v_mkInfoTree_7489_, v___y_7490_, v___y_7491_, v___y_7492_, v___y_7493_, v___y_7494_, v___y_7495_, v___y_7496_, v___y_7497_);
    crate::leanh::lean_dec(v___y_7497_);
    crate::leanh::lean_dec_ref(v___y_7496_);
    crate::leanh::lean_dec(v___y_7495_);
    crate::leanh::lean_dec_ref(v___y_7494_);
    crate::leanh::lean_dec(v___y_7493_);
    crate::leanh::lean_dec_ref(v___y_7492_);
    crate::leanh::lean_dec(v___y_7491_);
    crate::leanh::lean_dec_ref(v___y_7490_);
    return v_res_7499_;
}
pub unsafe fn l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__2_spec__3(
    mut v_00_u03b2_7500_: *mut crate::leanh::LeanObject,
    mut v_x_7501_: *mut crate::leanh::LeanObject,
    mut v_x_7502_: *mut crate::leanh::LeanObject,
    mut v_x_7503_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_7504_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_7504_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__2_spec__3___redArg(v_x_7501_, v_x_7502_, v_x_7503_);
    return v___x_7504_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__6(
    mut v_00_u03b2_7505_: *mut crate::leanh::LeanObject,
    mut v_m_7506_: *mut crate::leanh::LeanObject,
    mut v_a_7507_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_7508_: u8 = 0;
    v___x_7508_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__6___redArg(v_m_7506_, v_a_7507_);
    return v___x_7508_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__6___boxed(
    mut v_00_u03b2_7509_: *mut crate::leanh::LeanObject,
    mut v_m_7510_: *mut crate::leanh::LeanObject,
    mut v_a_7511_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_7512_: u8 = 0;
    let mut v_r_7513_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_7512_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__6(v_00_u03b2_7509_, v_m_7510_, v_a_7511_);
    crate::leanh::lean_dec_ref(v_a_7511_);
    crate::leanh::lean_dec_ref(v_m_7510_);
    v_r_7513_ = crate::leanh::lean_box((v_res_7512_) as usize);
    return v_r_7513_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__7(
    mut v_00_u03b2_7514_: *mut crate::leanh::LeanObject,
    mut v_m_7515_: *mut crate::leanh::LeanObject,
    mut v_a_7516_: *mut crate::leanh::LeanObject,
    mut v_b_7517_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_7518_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_7518_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__7___redArg(v_m_7515_, v_a_7516_, v_b_7517_);
    return v___x_7518_;
}
pub unsafe fn l_Lean_getExprMVarAssignment_x3f___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__8_spec__18(
    mut v_mvarId_7519_: *mut crate::leanh::LeanObject,
    mut v___y_7520_: *mut crate::leanh::LeanObject,
    mut v___y_7521_: *mut crate::leanh::LeanObject,
    mut v___y_7522_: *mut crate::leanh::LeanObject,
    mut v___y_7523_: *mut crate::leanh::LeanObject,
    mut v___y_7524_: *mut crate::leanh::LeanObject,
    mut v___y_7525_: *mut crate::leanh::LeanObject,
    mut v___y_7526_: *mut crate::leanh::LeanObject,
    mut v___y_7527_: *mut crate::leanh::LeanObject,
    mut v___y_7528_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_7530_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_7530_ = l_Lean_getExprMVarAssignment_x3f___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__8_spec__18___redArg(v_mvarId_7519_, v___y_7520_, v___y_7526_);
    return v___x_7530_;
}
pub unsafe fn l_Lean_getExprMVarAssignment_x3f___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__8_spec__18___boxed(
    mut v_mvarId_7531_: *mut crate::leanh::LeanObject,
    mut v___y_7532_: *mut crate::leanh::LeanObject,
    mut v___y_7533_: *mut crate::leanh::LeanObject,
    mut v___y_7534_: *mut crate::leanh::LeanObject,
    mut v___y_7535_: *mut crate::leanh::LeanObject,
    mut v___y_7536_: *mut crate::leanh::LeanObject,
    mut v___y_7537_: *mut crate::leanh::LeanObject,
    mut v___y_7538_: *mut crate::leanh::LeanObject,
    mut v___y_7539_: *mut crate::leanh::LeanObject,
    mut v___y_7540_: *mut crate::leanh::LeanObject,
    mut v___y_7541_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_7542_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_7542_ = l_Lean_getExprMVarAssignment_x3f___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__8_spec__18(v_mvarId_7531_, v___y_7532_, v___y_7533_, v___y_7534_, v___y_7535_, v___y_7536_, v___y_7537_, v___y_7538_, v___y_7539_, v___y_7540_);
    crate::leanh::lean_dec(v___y_7540_);
    crate::leanh::lean_dec_ref(v___y_7539_);
    crate::leanh::lean_dec(v___y_7538_);
    crate::leanh::lean_dec_ref(v___y_7537_);
    crate::leanh::lean_dec(v___y_7536_);
    crate::leanh::lean_dec_ref(v___y_7535_);
    crate::leanh::lean_dec(v___y_7534_);
    crate::leanh::lean_dec_ref(v___y_7533_);
    crate::leanh::lean_dec(v_mvarId_7531_);
    return v_res_7542_;
}
pub unsafe fn l_Lean_getDelayedMVarAssignment_x3f___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__8_spec__19(
    mut v_mvarId_7543_: *mut crate::leanh::LeanObject,
    mut v___y_7544_: *mut crate::leanh::LeanObject,
    mut v___y_7545_: *mut crate::leanh::LeanObject,
    mut v___y_7546_: *mut crate::leanh::LeanObject,
    mut v___y_7547_: *mut crate::leanh::LeanObject,
    mut v___y_7548_: *mut crate::leanh::LeanObject,
    mut v___y_7549_: *mut crate::leanh::LeanObject,
    mut v___y_7550_: *mut crate::leanh::LeanObject,
    mut v___y_7551_: *mut crate::leanh::LeanObject,
    mut v___y_7552_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_7554_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_7554_ = l_Lean_getDelayedMVarAssignment_x3f___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__8_spec__19___redArg(v_mvarId_7543_, v___y_7544_, v___y_7550_);
    return v___x_7554_;
}
pub unsafe fn l_Lean_getDelayedMVarAssignment_x3f___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__8_spec__19___boxed(
    mut v_mvarId_7555_: *mut crate::leanh::LeanObject,
    mut v___y_7556_: *mut crate::leanh::LeanObject,
    mut v___y_7557_: *mut crate::leanh::LeanObject,
    mut v___y_7558_: *mut crate::leanh::LeanObject,
    mut v___y_7559_: *mut crate::leanh::LeanObject,
    mut v___y_7560_: *mut crate::leanh::LeanObject,
    mut v___y_7561_: *mut crate::leanh::LeanObject,
    mut v___y_7562_: *mut crate::leanh::LeanObject,
    mut v___y_7563_: *mut crate::leanh::LeanObject,
    mut v___y_7564_: *mut crate::leanh::LeanObject,
    mut v___y_7565_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_7566_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_7566_ = l_Lean_getDelayedMVarAssignment_x3f___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visitMVar___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__8_spec__19(v_mvarId_7555_, v___y_7556_, v___y_7557_, v___y_7558_, v___y_7559_, v___y_7560_, v___y_7561_, v___y_7562_, v___y_7563_, v___y_7564_);
    crate::leanh::lean_dec(v___y_7564_);
    crate::leanh::lean_dec_ref(v___y_7563_);
    crate::leanh::lean_dec(v___y_7562_);
    crate::leanh::lean_dec_ref(v___y_7561_);
    crate::leanh::lean_dec(v___y_7560_);
    crate::leanh::lean_dec_ref(v___y_7559_);
    crate::leanh::lean_dec(v___y_7558_);
    crate::leanh::lean_dec_ref(v___y_7557_);
    crate::leanh::lean_dec(v_mvarId_7555_);
    return v_res_7566_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__2_spec__3_spec__11(
    mut v_00_u03b2_7567_: *mut crate::leanh::LeanObject,
    mut v_x_7568_: *mut crate::leanh::LeanObject,
    mut v_x_7569_: usize,
    mut v_x_7570_: usize,
    mut v_x_7571_: *mut crate::leanh::LeanObject,
    mut v_x_7572_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_7573_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_7573_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__2_spec__3_spec__11___redArg(v_x_7568_, v_x_7569_, v_x_7570_, v_x_7571_, v_x_7572_);
    return v___x_7573_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__2_spec__3_spec__11___boxed(
    mut v_00_u03b2_7574_: *mut crate::leanh::LeanObject,
    mut v_x_7575_: *mut crate::leanh::LeanObject,
    mut v_x_7576_: *mut crate::leanh::LeanObject,
    mut v_x_7577_: *mut crate::leanh::LeanObject,
    mut v_x_7578_: *mut crate::leanh::LeanObject,
    mut v_x_7579_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_99109__boxed_7580_: usize = 0;
    let mut v_x_99110__boxed_7581_: usize = 0;
    let mut v_res_7582_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_99109__boxed_7580_ = crate::leanh::lean_unbox_usize(v_x_7576_);
    crate::leanh::lean_dec(v_x_7576_);
    v_x_99110__boxed_7581_ = crate::leanh::lean_unbox_usize(v_x_7577_);
    crate::leanh::lean_dec(v_x_7577_);
    v_res_7582_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__2_spec__3_spec__11(v_00_u03b2_7574_, v_x_7575_, v_x_99109__boxed_7580_, v_x_99110__boxed_7581_, v_x_7578_, v_x_7579_);
    return v_res_7582_;
}
pub unsafe fn l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4_spec__7_spec__16(
    mut v_ref_7583_: *mut crate::leanh::LeanObject,
    mut v_msgData_7584_: *mut crate::leanh::LeanObject,
    mut v_severity_7585_: u8,
    mut v_isSilent_7586_: u8,
    mut v___y_7587_: *mut crate::leanh::LeanObject,
    mut v___y_7588_: *mut crate::leanh::LeanObject,
    mut v___y_7589_: *mut crate::leanh::LeanObject,
    mut v___y_7590_: *mut crate::leanh::LeanObject,
    mut v___y_7591_: *mut crate::leanh::LeanObject,
    mut v___y_7592_: *mut crate::leanh::LeanObject,
    mut v___y_7593_: *mut crate::leanh::LeanObject,
    mut v___y_7594_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_7596_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_7596_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4_spec__7_spec__16___redArg(v_ref_7583_, v_msgData_7584_, v_severity_7585_, v_isSilent_7586_, v___y_7591_, v___y_7592_, v___y_7593_, v___y_7594_);
    return v___x_7596_;
}
pub unsafe fn l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4_spec__7_spec__16___boxed(
    mut v_ref_7597_: *mut crate::leanh::LeanObject,
    mut v_msgData_7598_: *mut crate::leanh::LeanObject,
    mut v_severity_7599_: *mut crate::leanh::LeanObject,
    mut v_isSilent_7600_: *mut crate::leanh::LeanObject,
    mut v___y_7601_: *mut crate::leanh::LeanObject,
    mut v___y_7602_: *mut crate::leanh::LeanObject,
    mut v___y_7603_: *mut crate::leanh::LeanObject,
    mut v___y_7604_: *mut crate::leanh::LeanObject,
    mut v___y_7605_: *mut crate::leanh::LeanObject,
    mut v___y_7606_: *mut crate::leanh::LeanObject,
    mut v___y_7607_: *mut crate::leanh::LeanObject,
    mut v___y_7608_: *mut crate::leanh::LeanObject,
    mut v___y_7609_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_severity_boxed_7610_: u8 = 0;
    let mut v_isSilent_boxed_7611_: u8 = 0;
    let mut v_res_7612_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_severity_boxed_7610_ = (crate::leanh::lean_unbox(v_severity_7599_) as u8);
    v_isSilent_boxed_7611_ = (crate::leanh::lean_unbox(v_isSilent_7600_) as u8);
    v_res_7612_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__4_spec__7_spec__16(v_ref_7597_, v_msgData_7598_, v_severity_boxed_7610_, v_isSilent_boxed_7611_, v___y_7601_, v___y_7602_, v___y_7603_, v___y_7604_, v___y_7605_, v___y_7606_, v___y_7607_, v___y_7608_);
    crate::leanh::lean_dec(v___y_7608_);
    crate::leanh::lean_dec_ref(v___y_7607_);
    crate::leanh::lean_dec(v___y_7606_);
    crate::leanh::lean_dec_ref(v___y_7605_);
    crate::leanh::lean_dec(v___y_7604_);
    crate::leanh::lean_dec_ref(v___y_7603_);
    crate::leanh::lean_dec(v___y_7602_);
    crate::leanh::lean_dec_ref(v___y_7601_);
    crate::leanh::lean_dec(v_ref_7597_);
    return v_res_7612_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__6_spec__14(
    mut v_00_u03b2_7613_: *mut crate::leanh::LeanObject,
    mut v_a_7614_: *mut crate::leanh::LeanObject,
    mut v_x_7615_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_7616_: u8 = 0;
    v___x_7616_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__6_spec__14___redArg(v_a_7614_, v_x_7615_);
    return v___x_7616_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__6_spec__14___boxed(
    mut v_00_u03b2_7617_: *mut crate::leanh::LeanObject,
    mut v_a_7618_: *mut crate::leanh::LeanObject,
    mut v_x_7619_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_7620_: u8 = 0;
    let mut v_r_7621_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_7620_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__6_spec__14(v_00_u03b2_7617_, v_a_7618_, v_x_7619_);
    crate::leanh::lean_dec(v_x_7619_);
    crate::leanh::lean_dec_ref(v_a_7618_);
    v_r_7621_ = crate::leanh::lean_box((v_res_7620_) as usize);
    return v_r_7621_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__7_spec__16(
    mut v_00_u03b2_7622_: *mut crate::leanh::LeanObject,
    mut v_data_7623_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_7624_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_7624_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__7_spec__16___redArg(v_data_7623_);
    return v___x_7624_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__2_spec__3_spec__11_spec__22(
    mut v_00_u03b2_7625_: *mut crate::leanh::LeanObject,
    mut v_n_7626_: *mut crate::leanh::LeanObject,
    mut v_k_7627_: *mut crate::leanh::LeanObject,
    mut v_v_7628_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_7629_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_7629_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__2_spec__3_spec__11_spec__22___redArg(v_n_7626_, v_k_7627_, v_v_7628_);
    return v___x_7629_;
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__2_spec__3_spec__11_spec__23(
    mut v_00_u03b2_7630_: *mut crate::leanh::LeanObject,
    mut v_depth_7631_: usize,
    mut v_keys_7632_: *mut crate::leanh::LeanObject,
    mut v_vals_7633_: *mut crate::leanh::LeanObject,
    mut v_heq_7634_: *mut crate::leanh::LeanObject,
    mut v_i_7635_: *mut crate::leanh::LeanObject,
    mut v_entries_7636_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_7637_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_7637_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__2_spec__3_spec__11_spec__23___redArg(v_depth_7631_, v_keys_7632_, v_vals_7633_, v_i_7635_, v_entries_7636_);
    return v___x_7637_;
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__2_spec__3_spec__11_spec__23___boxed(
    mut v_00_u03b2_7638_: *mut crate::leanh::LeanObject,
    mut v_depth_7639_: *mut crate::leanh::LeanObject,
    mut v_keys_7640_: *mut crate::leanh::LeanObject,
    mut v_vals_7641_: *mut crate::leanh::LeanObject,
    mut v_heq_7642_: *mut crate::leanh::LeanObject,
    mut v_i_7643_: *mut crate::leanh::LeanObject,
    mut v_entries_7644_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_depth_boxed_7645_: usize = 0;
    let mut v_res_7646_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_depth_boxed_7645_ = crate::leanh::lean_unbox_usize(v_depth_7639_);
    crate::leanh::lean_dec(v_depth_7639_);
    v_res_7646_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__2_spec__3_spec__11_spec__23(v_00_u03b2_7638_, v_depth_boxed_7645_, v_keys_7640_, v_vals_7641_, v_heq_7642_, v_i_7643_, v_entries_7644_);
    crate::leanh::lean_dec_ref(v_vals_7641_);
    crate::leanh::lean_dec_ref(v_keys_7640_);
    return v_res_7646_;
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__7_spec__16_spec__19(
    mut v_00_u03b2_7647_: *mut crate::leanh::LeanObject,
    mut v_i_7648_: *mut crate::leanh::LeanObject,
    mut v_source_7649_: *mut crate::leanh::LeanObject,
    mut v_target_7650_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_7651_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_7651_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__7_spec__16_spec__19___redArg(v_i_7648_, v_source_7649_, v_target_7650_);
    return v___x_7651_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__2_spec__3_spec__11_spec__22_spec__25(
    mut v_00_u03b2_7652_: *mut crate::leanh::LeanObject,
    mut v_x_7653_: *mut crate::leanh::LeanObject,
    mut v_x_7654_: *mut crate::leanh::LeanObject,
    mut v_x_7655_: *mut crate::leanh::LeanObject,
    mut v_x_7656_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_7657_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_7657_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__2_spec__3_spec__11_spec__22_spec__25___redArg(v_x_7653_, v_x_7654_, v_x_7655_, v_x_7656_);
    return v___x_7657_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__7_spec__16_spec__19_spec__25(
    mut v_00_u03b2_7658_: *mut crate::leanh::LeanObject,
    mut v_x_7659_: *mut crate::leanh::LeanObject,
    mut v_x_7660_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_7661_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_7661_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00__private_Lean_Util_OccursCheck_0__Lean_occursCheck_visit___at___00Lean_occursCheck___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__1_spec__1_spec__7_spec__16_spec__19_spec__25___redArg(v_x_7659_, v_x_7660_);
    return v___x_7661_;
}
pub unsafe fn l_Lean_Elab_Tactic_Simpa_evalSimpa(
    mut v_a_7662_: *mut crate::leanh::LeanObject,
    mut v_a_7663_: *mut crate::leanh::LeanObject,
    mut v_a_7664_: *mut crate::leanh::LeanObject,
    mut v_a_7665_: *mut crate::leanh::LeanObject,
    mut v_a_7666_: *mut crate::leanh::LeanObject,
    mut v_a_7667_: *mut crate::leanh::LeanObject,
    mut v_a_7668_: *mut crate::leanh::LeanObject,
    mut v_a_7669_: *mut crate::leanh::LeanObject,
    mut v_a_7670_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_7672_: u8 = 0;
    let mut v___x_7673_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_7672_ = 1;
    v___x_7673_ = l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore(
        v___x_7672_,
        v_a_7662_,
        v_a_7663_,
        v_a_7664_,
        v_a_7665_,
        v_a_7666_,
        v_a_7667_,
        v_a_7668_,
        v_a_7669_,
        v_a_7670_,
    );
    return v___x_7673_;
}
pub unsafe fn l_Lean_Elab_Tactic_Simpa_evalSimpa___boxed(
    mut v_a_7674_: *mut crate::leanh::LeanObject,
    mut v_a_7675_: *mut crate::leanh::LeanObject,
    mut v_a_7676_: *mut crate::leanh::LeanObject,
    mut v_a_7677_: *mut crate::leanh::LeanObject,
    mut v_a_7678_: *mut crate::leanh::LeanObject,
    mut v_a_7679_: *mut crate::leanh::LeanObject,
    mut v_a_7680_: *mut crate::leanh::LeanObject,
    mut v_a_7681_: *mut crate::leanh::LeanObject,
    mut v_a_7682_: *mut crate::leanh::LeanObject,
    mut v_a_7683_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_7684_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_7684_ = l_Lean_Elab_Tactic_Simpa_evalSimpa(
        v_a_7674_, v_a_7675_, v_a_7676_, v_a_7677_, v_a_7678_, v_a_7679_, v_a_7680_, v_a_7681_,
        v_a_7682_,
    );
    crate::leanh::lean_dec(v_a_7682_);
    crate::leanh::lean_dec_ref(v_a_7681_);
    crate::leanh::lean_dec(v_a_7680_);
    crate::leanh::lean_dec_ref(v_a_7679_);
    crate::leanh::lean_dec(v_a_7678_);
    crate::leanh::lean_dec_ref(v_a_7677_);
    crate::leanh::lean_dec(v_a_7676_);
    crate::leanh::lean_dec_ref(v_a_7675_);
    return v_res_7684_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpa___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpa__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_7694_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7695_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7696_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7697_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7698_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_7694_ = l_Lean_Elab_Tactic_tacticElabAttribute;
    v___x_7695_ =
        l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___closed__3;
    v___x_7696_ = l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpa___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpa__1___closed__2;
    v___x_7697_ = crate::leanh::lean_alloc_closure(
        l_Lean_Elab_Tactic_Simpa_evalSimpa___boxed as *mut core::ffi::c_void,
        10,
        0,
    );
    v___x_7698_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(
        v___x_7694_,
        v___x_7695_,
        v___x_7696_,
        v___x_7697_,
    );
    return v___x_7698_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpa___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpa__1___boxed(
    mut v_a_7699_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_7700_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_7700_ = l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpa___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpa__1();
    return v_res_7700_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpa___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpa_declRange__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_7727_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7728_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7729_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_7727_ = l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpa___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpa__1___closed__2;
    v___x_7728_ = l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpa___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpa_declRange__3___closed__6;
    v___x_7729_ = l_Lean_addBuiltinDeclarationRanges(v___x_7727_, v___x_7728_);
    return v___x_7729_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpa___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpa_declRange__3___boxed(
    mut v_a_7730_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_7731_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_7731_ = l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpa___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpa_declRange__3();
    return v_res_7731_;
}
pub unsafe fn l_Lean_Elab_Tactic_Simpa_evalSimpaUsingBang___lam__0(
    mut v_x_7734_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_7735_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_7735_ = l_Lean_Elab_Tactic_Simpa_evalSimpaUsingBang___lam__0___closed__0;
    return v___x_7735_;
}
pub unsafe fn l_Lean_Elab_Tactic_Simpa_evalSimpaUsingBang___lam__0___boxed(
    mut v_x_7736_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_7737_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_7737_ = l_Lean_Elab_Tactic_Simpa_evalSimpaUsingBang___lam__0(v_x_7736_);
    crate::leanh::lean_dec(v_x_7736_);
    return v_res_7737_;
}
pub unsafe fn l_Lean_Elab_Tactic_Simpa_evalSimpaUsingBang(
    mut v_stx_7749_: *mut crate::leanh::LeanObject,
    mut v_a_7750_: *mut crate::leanh::LeanObject,
    mut v_a_7751_: *mut crate::leanh::LeanObject,
    mut v_a_7752_: *mut crate::leanh::LeanObject,
    mut v_a_7753_: *mut crate::leanh::LeanObject,
    mut v_a_7754_: *mut crate::leanh::LeanObject,
    mut v_a_7755_: *mut crate::leanh::LeanObject,
    mut v_a_7756_: *mut crate::leanh::LeanObject,
    mut v_a_7757_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_7760_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7761_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7762_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7763_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7764_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7765_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7766_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7767_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7768_: u8 = 0;
    let mut v___y_7769_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7770_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7771_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7772_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7773_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7774_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7775_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7776_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7777_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7778_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7779_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7780_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7781_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7782_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7783_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7784_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7785_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7786_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7787_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7788_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7789_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7790_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7791_: u8 = 0;
    let mut v___x_7792_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7793_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7795_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7796_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7797_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7798_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7799_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7800_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7801_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7802_: u8 = 0;
    let mut v___y_7803_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7804_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7805_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7806_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7807_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7808_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7809_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7810_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7811_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7812_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7813_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7814_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7815_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7816_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7817_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7818_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_7819_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7820_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7821_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7822_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7823_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7824_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7825_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7826_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7827_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7828_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7829_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7831_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7832_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7833_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7834_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7835_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7836_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7837_: u8 = 0;
    let mut v___y_7838_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7839_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7840_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7841_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7842_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7843_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7844_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7845_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7846_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7847_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7848_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7849_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7850_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7851_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7852_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7853_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7854_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_7855_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7856_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7857_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7858_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7859_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7860_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7862_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7863_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7864_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7865_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7866_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7867_: u8 = 0;
    let mut v___y_7868_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7869_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7870_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7871_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7872_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7873_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7874_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7875_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7876_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7877_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7878_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7879_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7880_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7881_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7882_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7883_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7884_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7885_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7886_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_7887_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7888_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7889_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7891_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7892_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7893_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7894_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7895_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7896_: u8 = 0;
    let mut v___y_7897_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7898_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7899_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7900_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7901_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7902_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7903_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7904_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7905_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7906_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7907_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7908_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7909_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7910_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7911_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7912_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7913_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_7914_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7915_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7916_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7917_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7918_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7919_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tk_7920_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7922_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7923_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7924_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7925_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7926_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7927_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7928_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7929_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7930_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7931_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7932_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7933_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7934_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7935_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7936_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_7937_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7938_: u8 = 0;
    let mut v___x_7939_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7940_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7941_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7942_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7943_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7944_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7945_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_7946_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7947_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7948_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7949_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7950_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7951_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7953_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7954_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7955_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7956_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7957_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7958_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_args_7959_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7960_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7961_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7962_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7963_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7964_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7965_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7966_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7967_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7968_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7969_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7970_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7971_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_7972_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7974_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7975_: u8 = 0;
    let mut v___x_7977_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7978_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7979_: u8 = 0;
    let mut v___x_7980_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7982_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7983_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7984_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7985_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7986_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7987_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_only_7988_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7989_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7990_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7991_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7992_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7993_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7994_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7995_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7996_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7997_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7998_: u8 = 0;
    let mut v___x_7999_: u8 = 0;
    let mut v___x_8000_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8001_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8002_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8003_: u8 = 0;
    let mut v___x_8004_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8005_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_args_8006_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8007_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8008_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_8010_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_8011_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unfold_8012_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_8013_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_8014_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_8015_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_8016_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_8017_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_8018_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_8019_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_8020_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8021_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8022_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8023_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8024_: u8 = 0;
    let mut v___x_8025_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8026_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8027_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8028_: u8 = 0;
    let mut v___x_8029_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8030_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8031_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8032_: u8 = 0;
    let mut v___x_8033_: u8 = 0;
    let mut v___x_8034_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_only_8035_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8036_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8037_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_squeeze_8039_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_8040_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_8041_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_8042_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_8043_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_8044_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_8045_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_8046_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_8047_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8048_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8049_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8050_: u8 = 0;
    let mut v___x_8051_: u8 = 0;
    let mut v___x_8052_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unfold_8053_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8054_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8055_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8056_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8057_: u8 = 0;
    let mut v___x_8058_: u8 = 0;
    let mut v___x_8059_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_squeeze_8060_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8061_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8062_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_7790_ = l_Lean_Elab_Tactic_Simpa_evalSimpaUsingBang___closed__0;
                crate::leanh::lean_inc(v_stx_7749_);
                v___x_7791_ = l_Lean_Syntax_isOfKind(v_stx_7749_, v___x_7790_);
                if v___x_7791_ == 0 {
                    crate::leanh::lean_dec(v_stx_7749_);
                    v___x_7792_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__0___redArg();
                    return v___x_7792_;
                } else {
                    v___x_7793_ = crate::leanh::lean_unsigned_to_nat(0);
                    v_tk_7920_ = l_Lean_Syntax_getArg(v_stx_7749_, v___x_7793_);
                    v___x_7980_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_8056_ = l_Lean_Syntax_getArg(v_stx_7749_, v___x_7980_);
                    v___x_8057_ = l_Lean_Syntax_isNone(v___x_8056_);
                    if v___x_8057_ == 0 {
                        crate::leanh::lean_inc(v___x_8056_);
                        v___x_8058_ = l_Lean_Syntax_matchesNull(v___x_8056_, v___x_7980_);
                        if v___x_8058_ == 0 {
                            crate::leanh::lean_dec(v___x_8056_);
                            crate::leanh::lean_dec(v_tk_7920_);
                            crate::leanh::lean_dec(v_stx_7749_);
                            v___x_8059_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__0___redArg();
                            return v___x_8059_;
                        } else {
                            v_squeeze_8060_ = l_Lean_Syntax_getArg(v___x_8056_, v___x_7793_);
                            crate::leanh::lean_dec(v___x_8056_);
                            v___x_8061_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_8061_, 0, v_squeeze_8060_);
                            v_squeeze_8039_ = v___x_8061_;
                            v___y_8040_ = v_a_7750_;
                            v___y_8041_ = v_a_7751_;
                            v___y_8042_ = v_a_7752_;
                            v___y_8043_ = v_a_7753_;
                            v___y_8044_ = v_a_7754_;
                            v___y_8045_ = v_a_7755_;
                            v___y_8046_ = v_a_7756_;
                            v___y_8047_ = v_a_7757_;
                            state = 12;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec(v___x_8056_);
                        v___x_8062_ = crate::leanh::lean_box(0);
                        v_squeeze_8039_ = v___x_8062_;
                        v___y_8040_ = v_a_7750_;
                        v___y_8041_ = v_a_7751_;
                        v___y_8042_ = v_a_7752_;
                        v___y_8043_ = v_a_7753_;
                        v___y_8044_ = v_a_7754_;
                        v___y_8045_ = v_a_7755_;
                        v___y_8046_ = v_a_7756_;
                        v___y_8047_ = v_a_7757_;
                        state = 12;
                        continue;
                    }
                }
            }
            1 => {
                crate::leanh::lean_inc_ref(v___y_7778_);
                v___x_7782_ = l_Array_append___redArg(v___y_7778_, v___y_7781_);
                crate::leanh::lean_dec_ref(v___y_7781_);
                crate::leanh::lean_inc_n(v___y_7775_, 2);
                crate::leanh::lean_inc_n(v___y_7771_, 4);
                v___x_7783_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_7783_, 0, v___y_7771_);
                crate::leanh::lean_ctor_set(v___x_7783_, 1, v___y_7775_);
                crate::leanh::lean_ctor_set(v___x_7783_, 2, v___x_7782_);
                v___x_7784_ = l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__11;
                v___x_7785_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_7785_, 0, v___y_7771_);
                crate::leanh::lean_ctor_set(v___x_7785_, 1, v___x_7784_);
                v___x_7786_ =
                    l_Lean_Syntax_node2(v___y_7771_, v___y_7775_, v___x_7785_, v___y_7763_);
                crate::leanh::lean_inc(v___y_7774_);
                v___x_7787_ = l_Lean_Syntax_node5(
                    v___y_7771_,
                    v___y_7774_,
                    v___y_7779_,
                    v___y_7760_,
                    v___y_7762_,
                    v___x_7783_,
                    v___x_7786_,
                );
                crate::leanh::lean_inc(v___y_7764_);
                v___x_7788_ = l_Lean_Syntax_node4(
                    v___y_7771_,
                    v___y_7764_,
                    v___y_7766_,
                    v___y_7769_,
                    v___y_7767_,
                    v___x_7787_,
                );
                v___x_7789_ =
                    l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore(
                        v___y_7768_,
                        v___x_7788_,
                        v___y_7773_,
                        v___y_7777_,
                        v___y_7772_,
                        v___y_7770_,
                        v___y_7780_,
                        v___y_7765_,
                        v___y_7761_,
                        v___y_7776_,
                    );
                return v___x_7789_;
            }
            2 => {
                crate::leanh::lean_inc_ref(v___y_7814_);
                v___x_7817_ = l_Array_append___redArg(v___y_7814_, v___y_7816_);
                crate::leanh::lean_dec_ref(v___y_7816_);
                crate::leanh::lean_inc(v___y_7810_);
                crate::leanh::lean_inc(v___y_7804_);
                v___x_7818_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_7818_, 0, v___y_7804_);
                crate::leanh::lean_ctor_set(v___x_7818_, 1, v___y_7810_);
                crate::leanh::lean_ctor_set(v___x_7818_, 2, v___x_7817_);
                if crate::leanh::lean_obj_tag(v___y_7806_) == 1 {
                    v_val_7819_ = crate::leanh::lean_ctor_get(v___y_7806_, 0);
                    crate::leanh::lean_inc(v_val_7819_);
                    crate::leanh::lean_dec_ref_known(v___y_7806_, 1);
                    v___x_7820_ = l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___closed__5;
                    v___x_7821_ = l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__13;
                    crate::leanh::lean_inc_n(v___y_7804_, 4);
                    v___x_7822_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_7822_, 0, v___y_7804_);
                    crate::leanh::lean_ctor_set(v___x_7822_, 1, v___x_7821_);
                    crate::leanh::lean_inc_ref(v___y_7814_);
                    v___x_7823_ = l_Array_append___redArg(v___y_7814_, v_val_7819_);
                    crate::leanh::lean_dec(v_val_7819_);
                    crate::leanh::lean_inc(v___y_7810_);
                    v___x_7824_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_7824_, 0, v___y_7804_);
                    crate::leanh::lean_ctor_set(v___x_7824_, 1, v___y_7810_);
                    crate::leanh::lean_ctor_set(v___x_7824_, 2, v___x_7823_);
                    v___x_7825_ = l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__14;
                    v___x_7826_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_7826_, 0, v___y_7804_);
                    crate::leanh::lean_ctor_set(v___x_7826_, 1, v___x_7825_);
                    v___x_7827_ = l_Lean_Syntax_node3(
                        v___y_7804_,
                        v___x_7820_,
                        v___x_7822_,
                        v___x_7824_,
                        v___x_7826_,
                    );
                    v___x_7828_ = l_Array_mkArray1___redArg(v___x_7827_);
                    v___y_7760_ = v___y_7795_;
                    v___y_7761_ = v___y_7796_;
                    v___y_7762_ = v___x_7818_;
                    v___y_7763_ = v___y_7797_;
                    v___y_7764_ = v___y_7798_;
                    v___y_7765_ = v___y_7799_;
                    v___y_7766_ = v___y_7800_;
                    v___y_7767_ = v___y_7801_;
                    v___y_7768_ = v___y_7802_;
                    v___y_7769_ = v___y_7803_;
                    v___y_7770_ = v___y_7805_;
                    v___y_7771_ = v___y_7804_;
                    v___y_7772_ = v___y_7808_;
                    v___y_7773_ = v___y_7807_;
                    v___y_7774_ = v___y_7809_;
                    v___y_7775_ = v___y_7810_;
                    v___y_7776_ = v___y_7813_;
                    v___y_7777_ = v___y_7812_;
                    v___y_7778_ = v___y_7814_;
                    v___y_7779_ = v___y_7811_;
                    v___y_7780_ = v___y_7815_;
                    v___y_7781_ = v___x_7828_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_dec(v___y_7806_);
                    v___x_7829_ = l_Lean_Elab_Tactic_Simpa_evalSimpaUsingBang___lam__0___closed__0;
                    v___y_7760_ = v___y_7795_;
                    v___y_7761_ = v___y_7796_;
                    v___y_7762_ = v___x_7818_;
                    v___y_7763_ = v___y_7797_;
                    v___y_7764_ = v___y_7798_;
                    v___y_7765_ = v___y_7799_;
                    v___y_7766_ = v___y_7800_;
                    v___y_7767_ = v___y_7801_;
                    v___y_7768_ = v___y_7802_;
                    v___y_7769_ = v___y_7803_;
                    v___y_7770_ = v___y_7805_;
                    v___y_7771_ = v___y_7804_;
                    v___y_7772_ = v___y_7808_;
                    v___y_7773_ = v___y_7807_;
                    v___y_7774_ = v___y_7809_;
                    v___y_7775_ = v___y_7810_;
                    v___y_7776_ = v___y_7813_;
                    v___y_7777_ = v___y_7812_;
                    v___y_7778_ = v___y_7814_;
                    v___y_7779_ = v___y_7811_;
                    v___y_7780_ = v___y_7815_;
                    v___y_7781_ = v___x_7829_;
                    state = 1;
                    continue;
                }
            }
            3 => {
                crate::leanh::lean_inc_ref(v___y_7849_);
                v___x_7853_ = l_Array_append___redArg(v___y_7849_, v___y_7852_);
                crate::leanh::lean_dec_ref(v___y_7852_);
                crate::leanh::lean_inc(v___y_7845_);
                crate::leanh::lean_inc(v___y_7839_);
                v___x_7854_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_7854_, 0, v___y_7839_);
                crate::leanh::lean_ctor_set(v___x_7854_, 1, v___y_7845_);
                crate::leanh::lean_ctor_set(v___x_7854_, 2, v___x_7853_);
                if crate::leanh::lean_obj_tag(v___y_7850_) == 1 {
                    v_val_7855_ = crate::leanh::lean_ctor_get(v___y_7850_, 0);
                    crate::leanh::lean_inc(v_val_7855_);
                    crate::leanh::lean_dec_ref_known(v___y_7850_, 1);
                    v___x_7856_ = l_Lean_SourceInfo_fromRef(v_val_7855_, v___x_7791_);
                    crate::leanh::lean_dec(v_val_7855_);
                    v___x_7857_ = l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__15;
                    v___x_7858_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_7858_, 0, v___x_7856_);
                    crate::leanh::lean_ctor_set(v___x_7858_, 1, v___x_7857_);
                    v___x_7859_ = l_Array_mkArray1___redArg(v___x_7858_);
                    v___y_7795_ = v___x_7854_;
                    v___y_7796_ = v___y_7831_;
                    v___y_7797_ = v___y_7832_;
                    v___y_7798_ = v___y_7833_;
                    v___y_7799_ = v___y_7834_;
                    v___y_7800_ = v___y_7835_;
                    v___y_7801_ = v___y_7836_;
                    v___y_7802_ = v___y_7837_;
                    v___y_7803_ = v___y_7838_;
                    v___y_7804_ = v___y_7839_;
                    v___y_7805_ = v___y_7840_;
                    v___y_7806_ = v___y_7843_;
                    v___y_7807_ = v___y_7842_;
                    v___y_7808_ = v___y_7841_;
                    v___y_7809_ = v___y_7844_;
                    v___y_7810_ = v___y_7845_;
                    v___y_7811_ = v___y_7848_;
                    v___y_7812_ = v___y_7847_;
                    v___y_7813_ = v___y_7846_;
                    v___y_7814_ = v___y_7849_;
                    v___y_7815_ = v___y_7851_;
                    v___y_7816_ = v___x_7859_;
                    state = 2;
                    continue;
                } else {
                    v___x_7860_ = l_Lean_Elab_Tactic_Simpa_evalSimpaUsingBang___lam__0(v___y_7850_);
                    crate::leanh::lean_dec(v___y_7850_);
                    v___y_7795_ = v___x_7854_;
                    v___y_7796_ = v___y_7831_;
                    v___y_7797_ = v___y_7832_;
                    v___y_7798_ = v___y_7833_;
                    v___y_7799_ = v___y_7834_;
                    v___y_7800_ = v___y_7835_;
                    v___y_7801_ = v___y_7836_;
                    v___y_7802_ = v___y_7837_;
                    v___y_7803_ = v___y_7838_;
                    v___y_7804_ = v___y_7839_;
                    v___y_7805_ = v___y_7840_;
                    v___y_7806_ = v___y_7843_;
                    v___y_7807_ = v___y_7842_;
                    v___y_7808_ = v___y_7841_;
                    v___y_7809_ = v___y_7844_;
                    v___y_7810_ = v___y_7845_;
                    v___y_7811_ = v___y_7848_;
                    v___y_7812_ = v___y_7847_;
                    v___y_7813_ = v___y_7846_;
                    v___y_7814_ = v___y_7849_;
                    v___y_7815_ = v___y_7851_;
                    v___y_7816_ = v___x_7860_;
                    state = 2;
                    continue;
                }
            }
            4 => {
                crate::leanh::lean_inc_ref(v___y_7879_);
                v___x_7883_ = l_Array_append___redArg(v___y_7879_, v___y_7882_);
                crate::leanh::lean_dec_ref(v___y_7882_);
                crate::leanh::lean_inc(v___y_7875_);
                crate::leanh::lean_inc(v___y_7870_);
                v___x_7884_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_7884_, 0, v___y_7870_);
                crate::leanh::lean_ctor_set(v___x_7884_, 1, v___y_7875_);
                crate::leanh::lean_ctor_set(v___x_7884_, 2, v___x_7883_);
                v___x_7885_ = l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___closed__7;
                if crate::leanh::lean_obj_tag(v___y_7868_) == 0 {
                    v___x_7886_ = l_Lean_Elab_Tactic_Simpa_evalSimpaUsingBang___lam__0___closed__0;
                    v___y_7831_ = v___y_7862_;
                    v___y_7832_ = v___y_7863_;
                    v___y_7833_ = v___y_7864_;
                    v___y_7834_ = v___y_7865_;
                    v___y_7835_ = v___y_7866_;
                    v___y_7836_ = v___x_7884_;
                    v___y_7837_ = v___y_7867_;
                    v___y_7838_ = v___y_7869_;
                    v___y_7839_ = v___y_7870_;
                    v___y_7840_ = v___y_7871_;
                    v___y_7841_ = v___y_7873_;
                    v___y_7842_ = v___y_7874_;
                    v___y_7843_ = v___y_7872_;
                    v___y_7844_ = v___x_7885_;
                    v___y_7845_ = v___y_7875_;
                    v___y_7846_ = v___y_7878_;
                    v___y_7847_ = v___y_7877_;
                    v___y_7848_ = v___y_7876_;
                    v___y_7849_ = v___y_7879_;
                    v___y_7850_ = v___y_7880_;
                    v___y_7851_ = v___y_7881_;
                    v___y_7852_ = v___x_7886_;
                    state = 3;
                    continue;
                } else {
                    v_val_7887_ = crate::leanh::lean_ctor_get(v___y_7868_, 0);
                    crate::leanh::lean_inc(v_val_7887_);
                    crate::leanh::lean_dec_ref_known(v___y_7868_, 1);
                    v___x_7888_ = l_Lean_Elab_Tactic_Simpa_evalSimpaUsingBang___lam__0___closed__0;
                    v___x_7889_ = lean_array_push(v___x_7888_, v_val_7887_);
                    v___y_7831_ = v___y_7862_;
                    v___y_7832_ = v___y_7863_;
                    v___y_7833_ = v___y_7864_;
                    v___y_7834_ = v___y_7865_;
                    v___y_7835_ = v___y_7866_;
                    v___y_7836_ = v___x_7884_;
                    v___y_7837_ = v___y_7867_;
                    v___y_7838_ = v___y_7869_;
                    v___y_7839_ = v___y_7870_;
                    v___y_7840_ = v___y_7871_;
                    v___y_7841_ = v___y_7873_;
                    v___y_7842_ = v___y_7874_;
                    v___y_7843_ = v___y_7872_;
                    v___y_7844_ = v___x_7885_;
                    v___y_7845_ = v___y_7875_;
                    v___y_7846_ = v___y_7878_;
                    v___y_7847_ = v___y_7877_;
                    v___y_7848_ = v___y_7876_;
                    v___y_7849_ = v___y_7879_;
                    v___y_7850_ = v___y_7880_;
                    v___y_7851_ = v___y_7881_;
                    v___y_7852_ = v___x_7889_;
                    state = 3;
                    continue;
                }
            }
            5 => {
                crate::leanh::lean_inc_ref(v___y_7908_);
                v___x_7912_ = l_Array_append___redArg(v___y_7908_, v___y_7911_);
                crate::leanh::lean_dec_ref(v___y_7911_);
                crate::leanh::lean_inc(v___y_7904_);
                crate::leanh::lean_inc(v___y_7898_);
                v___x_7913_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_7913_, 0, v___y_7898_);
                crate::leanh::lean_ctor_set(v___x_7913_, 1, v___y_7904_);
                crate::leanh::lean_ctor_set(v___x_7913_, 2, v___x_7912_);
                if crate::leanh::lean_obj_tag(v___y_7900_) == 1 {
                    v_val_7914_ = crate::leanh::lean_ctor_get(v___y_7900_, 0);
                    crate::leanh::lean_inc(v_val_7914_);
                    crate::leanh::lean_dec_ref_known(v___y_7900_, 1);
                    v___x_7915_ = l_Lean_SourceInfo_fromRef(v_val_7914_, v___x_7791_);
                    crate::leanh::lean_dec(v_val_7914_);
                    v___x_7916_ = l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__19;
                    v___x_7917_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_7917_, 0, v___x_7915_);
                    crate::leanh::lean_ctor_set(v___x_7917_, 1, v___x_7916_);
                    v___x_7918_ = l_Array_mkArray1___redArg(v___x_7917_);
                    v___y_7862_ = v___y_7891_;
                    v___y_7863_ = v___y_7892_;
                    v___y_7864_ = v___y_7893_;
                    v___y_7865_ = v___y_7894_;
                    v___y_7866_ = v___y_7895_;
                    v___y_7867_ = v___y_7896_;
                    v___y_7868_ = v___y_7897_;
                    v___y_7869_ = v___x_7913_;
                    v___y_7870_ = v___y_7898_;
                    v___y_7871_ = v___y_7899_;
                    v___y_7872_ = v___y_7902_;
                    v___y_7873_ = v___y_7903_;
                    v___y_7874_ = v___y_7901_;
                    v___y_7875_ = v___y_7904_;
                    v___y_7876_ = v___y_7907_;
                    v___y_7877_ = v___y_7906_;
                    v___y_7878_ = v___y_7905_;
                    v___y_7879_ = v___y_7908_;
                    v___y_7880_ = v___y_7909_;
                    v___y_7881_ = v___y_7910_;
                    v___y_7882_ = v___x_7918_;
                    state = 4;
                    continue;
                } else {
                    v___x_7919_ = l_Lean_Elab_Tactic_Simpa_evalSimpaUsingBang___lam__0(v___y_7900_);
                    crate::leanh::lean_dec(v___y_7900_);
                    v___y_7862_ = v___y_7891_;
                    v___y_7863_ = v___y_7892_;
                    v___y_7864_ = v___y_7893_;
                    v___y_7865_ = v___y_7894_;
                    v___y_7866_ = v___y_7895_;
                    v___y_7867_ = v___y_7896_;
                    v___y_7868_ = v___y_7897_;
                    v___y_7869_ = v___x_7913_;
                    v___y_7870_ = v___y_7898_;
                    v___y_7871_ = v___y_7899_;
                    v___y_7872_ = v___y_7902_;
                    v___y_7873_ = v___y_7903_;
                    v___y_7874_ = v___y_7901_;
                    v___y_7875_ = v___y_7904_;
                    v___y_7876_ = v___y_7907_;
                    v___y_7877_ = v___y_7906_;
                    v___y_7878_ = v___y_7905_;
                    v___y_7879_ = v___y_7908_;
                    v___y_7880_ = v___y_7909_;
                    v___y_7881_ = v___y_7910_;
                    v___y_7882_ = v___x_7919_;
                    state = 4;
                    continue;
                }
            }
            6 => {
                v_ref_7937_ = crate::leanh::lean_ctor_get(v___y_7922_, 5);
                v___x_7938_ = 0;
                v___x_7939_ = l_Lean_SourceInfo_fromRef(v_ref_7937_, v___x_7938_);
                v___x_7940_ = l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___closed__2;
                v___x_7941_ = l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___closed__3;
                v___x_7942_ = l_Lean_SourceInfo_fromRef(v_tk_7920_, v___x_7791_);
                crate::leanh::lean_dec(v_tk_7920_);
                v___x_7943_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_7943_, 0, v___x_7942_);
                crate::leanh::lean_ctor_set(v___x_7943_, 1, v___x_7940_);
                v___x_7944_ = l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__9;
                v___x_7945_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__10), core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__10_once), _init_l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___lam__6___closed__10);
                if crate::leanh::lean_obj_tag(v___y_7930_) == 1 {
                    v_val_7946_ = crate::leanh::lean_ctor_get(v___y_7930_, 0);
                    crate::leanh::lean_inc(v_val_7946_);
                    crate::leanh::lean_dec_ref_known(v___y_7930_, 1);
                    v___x_7947_ = l_Lean_SourceInfo_fromRef(v_val_7946_, v___x_7791_);
                    crate::leanh::lean_dec(v_val_7946_);
                    v___x_7948_ = l_Lean_Elab_Tactic_Simpa_evalSimpaUsingBang___closed__1;
                    v___x_7949_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_7949_, 0, v___x_7947_);
                    crate::leanh::lean_ctor_set(v___x_7949_, 1, v___x_7948_);
                    v___x_7950_ = l_Array_mkArray1___redArg(v___x_7949_);
                    v___y_7891_ = v___y_7922_;
                    v___y_7892_ = v___y_7923_;
                    v___y_7893_ = v___x_7941_;
                    v___y_7894_ = v___y_7924_;
                    v___y_7895_ = v___x_7943_;
                    v___y_7896_ = v___x_7938_;
                    v___y_7897_ = v___y_7936_;
                    v___y_7898_ = v___x_7939_;
                    v___y_7899_ = v___y_7925_;
                    v___y_7900_ = v___y_7926_;
                    v___y_7901_ = v___y_7927_;
                    v___y_7902_ = v___y_7928_;
                    v___y_7903_ = v___y_7929_;
                    v___y_7904_ = v___x_7944_;
                    v___y_7905_ = v___y_7931_;
                    v___y_7906_ = v___y_7932_;
                    v___y_7907_ = v___y_7933_;
                    v___y_7908_ = v___x_7945_;
                    v___y_7909_ = v___y_7934_;
                    v___y_7910_ = v___y_7935_;
                    v___y_7911_ = v___x_7950_;
                    state = 5;
                    continue;
                } else {
                    v___x_7951_ = l_Lean_Elab_Tactic_Simpa_evalSimpaUsingBang___lam__0(v___y_7930_);
                    crate::leanh::lean_dec(v___y_7930_);
                    v___y_7891_ = v___y_7922_;
                    v___y_7892_ = v___y_7923_;
                    v___y_7893_ = v___x_7941_;
                    v___y_7894_ = v___y_7924_;
                    v___y_7895_ = v___x_7943_;
                    v___y_7896_ = v___x_7938_;
                    v___y_7897_ = v___y_7936_;
                    v___y_7898_ = v___x_7939_;
                    v___y_7899_ = v___y_7925_;
                    v___y_7900_ = v___y_7926_;
                    v___y_7901_ = v___y_7927_;
                    v___y_7902_ = v___y_7928_;
                    v___y_7903_ = v___y_7929_;
                    v___y_7904_ = v___x_7944_;
                    v___y_7905_ = v___y_7931_;
                    v___y_7906_ = v___y_7932_;
                    v___y_7907_ = v___y_7933_;
                    v___y_7908_ = v___x_7945_;
                    v___y_7909_ = v___y_7934_;
                    v___y_7910_ = v___y_7935_;
                    v___y_7911_ = v___x_7951_;
                    state = 5;
                    continue;
                }
            }
            7 => {
                v___x_7968_ = crate::leanh::lean_unsigned_to_nat(5);
                v___x_7969_ = l_Lean_Syntax_getArg(v___y_7954_, v___x_7968_);
                crate::leanh::lean_dec(v___y_7954_);
                v___x_7970_ = l_Lean_Syntax_getOptional_x3f(v___y_7956_);
                crate::leanh::lean_dec(v___y_7956_);
                if crate::leanh::lean_obj_tag(v___x_7970_) == 0 {
                    v___x_7971_ = crate::leanh::lean_box(0);
                    v___y_7922_ = v___y_7966_;
                    v___y_7923_ = v___x_7969_;
                    v___y_7924_ = v___y_7965_;
                    v___y_7925_ = v___y_7963_;
                    v___y_7926_ = v___y_7953_;
                    v___y_7927_ = v___y_7960_;
                    v___y_7928_ = v_args_7959_;
                    v___y_7929_ = v___y_7962_;
                    v___y_7930_ = v___y_7955_;
                    v___y_7931_ = v___y_7967_;
                    v___y_7932_ = v___y_7961_;
                    v___y_7933_ = v___y_7957_;
                    v___y_7934_ = v___y_7958_;
                    v___y_7935_ = v___y_7964_;
                    v___y_7936_ = v___x_7971_;
                    state = 6;
                    continue;
                } else {
                    v_val_7972_ = crate::leanh::lean_ctor_get(v___x_7970_, 0);
                    v_isSharedCheck_7979_ = (!crate::leanh::lean_is_exclusive(v___x_7970_)) as u8;
                    if v_isSharedCheck_7979_ == 0 {
                        v___x_7974_ = v___x_7970_;
                        v_isShared_7975_ = v_isSharedCheck_7979_;
                        state = 8;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_val_7972_);
                        crate::leanh::lean_dec(v___x_7970_);
                        v___x_7974_ = crate::leanh::lean_box(0);
                        v_isShared_7975_ = v_isSharedCheck_7979_;
                        state = 8;
                        continue;
                    }
                }
            }
            8 => {
                if v_isShared_7975_ == 0 {
                    v___x_7977_ = v___x_7974_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_7978_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7978_, 0, v_val_7972_);
                    v___x_7977_ = v_reuseFailAlloc_7978_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                v___y_7922_ = v___y_7966_;
                v___y_7923_ = v___x_7969_;
                v___y_7924_ = v___y_7965_;
                v___y_7925_ = v___y_7963_;
                v___y_7926_ = v___y_7953_;
                v___y_7927_ = v___y_7960_;
                v___y_7928_ = v_args_7959_;
                v___y_7929_ = v___y_7962_;
                v___y_7930_ = v___y_7955_;
                v___y_7931_ = v___y_7967_;
                v___y_7932_ = v___y_7961_;
                v___y_7933_ = v___y_7957_;
                v___y_7934_ = v___y_7958_;
                v___y_7935_ = v___y_7964_;
                v___y_7936_ = v___x_7977_;
                state = 6;
                continue;
            }
            10 => {
                v___x_7997_ = l_Lean_Syntax_getArg(v___y_7983_, v___y_7985_);
                v___x_7998_ = l_Lean_Syntax_isNone(v___x_7997_);
                if v___x_7998_ == 0 {
                    crate::leanh::lean_inc(v___x_7997_);
                    v___x_7999_ = l_Lean_Syntax_matchesNull(v___x_7997_, v___x_7980_);
                    if v___x_7999_ == 0 {
                        crate::leanh::lean_dec(v___x_7997_);
                        crate::leanh::lean_dec(v_only_7988_);
                        crate::leanh::lean_dec(v___y_7987_);
                        crate::leanh::lean_dec(v___y_7986_);
                        crate::leanh::lean_dec(v___y_7984_);
                        crate::leanh::lean_dec(v___y_7983_);
                        crate::leanh::lean_dec(v___y_7982_);
                        crate::leanh::lean_dec(v_tk_7920_);
                        v___x_8000_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__0___redArg();
                        return v___x_8000_;
                    } else {
                        v___x_8001_ = l_Lean_Syntax_getArg(v___x_7997_, v___x_7793_);
                        crate::leanh::lean_dec(v___x_7997_);
                        v___x_8002_ = l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___closed__5;
                        crate::leanh::lean_inc(v___x_8001_);
                        v___x_8003_ = l_Lean_Syntax_isOfKind(v___x_8001_, v___x_8002_);
                        if v___x_8003_ == 0 {
                            crate::leanh::lean_dec(v___x_8001_);
                            crate::leanh::lean_dec(v_only_7988_);
                            crate::leanh::lean_dec(v___y_7987_);
                            crate::leanh::lean_dec(v___y_7986_);
                            crate::leanh::lean_dec(v___y_7984_);
                            crate::leanh::lean_dec(v___y_7983_);
                            crate::leanh::lean_dec(v___y_7982_);
                            crate::leanh::lean_dec(v_tk_7920_);
                            v___x_8004_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__0___redArg();
                            return v___x_8004_;
                        } else {
                            v___x_8005_ = l_Lean_Syntax_getArg(v___x_8001_, v___x_7980_);
                            crate::leanh::lean_dec(v___x_8001_);
                            v_args_8006_ = l_Lean_Syntax_getArgs(v___x_8005_);
                            crate::leanh::lean_dec(v___x_8005_);
                            v___x_8007_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_8007_, 0, v_args_8006_);
                            v___y_7953_ = v___y_7982_;
                            v___y_7954_ = v___y_7983_;
                            v___y_7955_ = v___y_7984_;
                            v___y_7956_ = v___y_7987_;
                            v___y_7957_ = v___y_7986_;
                            v___y_7958_ = v_only_7988_;
                            v_args_7959_ = v___x_8007_;
                            v___y_7960_ = v___y_7989_;
                            v___y_7961_ = v___y_7990_;
                            v___y_7962_ = v___y_7991_;
                            v___y_7963_ = v___y_7992_;
                            v___y_7964_ = v___y_7993_;
                            v___y_7965_ = v___y_7994_;
                            v___y_7966_ = v___y_7995_;
                            v___y_7967_ = v___y_7996_;
                            state = 7;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec(v___x_7997_);
                    v___x_8008_ = crate::leanh::lean_box(0);
                    v___y_7953_ = v___y_7982_;
                    v___y_7954_ = v___y_7983_;
                    v___y_7955_ = v___y_7984_;
                    v___y_7956_ = v___y_7987_;
                    v___y_7957_ = v___y_7986_;
                    v___y_7958_ = v_only_7988_;
                    v_args_7959_ = v___x_8008_;
                    v___y_7960_ = v___y_7989_;
                    v___y_7961_ = v___y_7990_;
                    v___y_7962_ = v___y_7991_;
                    v___y_7963_ = v___y_7992_;
                    v___y_7964_ = v___y_7993_;
                    v___y_7965_ = v___y_7994_;
                    v___y_7966_ = v___y_7995_;
                    v___y_7967_ = v___y_7996_;
                    state = 7;
                    continue;
                }
            }
            11 => {
                v___x_8021_ = crate::leanh::lean_unsigned_to_nat(3);
                v___x_8022_ = l_Lean_Syntax_getArg(v_stx_7749_, v___x_8021_);
                crate::leanh::lean_dec(v_stx_7749_);
                v___x_8023_ = l_Lean_Elab_Tactic_Simpa_evalSimpaUsingBang___closed__2;
                crate::leanh::lean_inc(v___x_8022_);
                v___x_8024_ = l_Lean_Syntax_isOfKind(v___x_8022_, v___x_8023_);
                if v___x_8024_ == 0 {
                    crate::leanh::lean_dec(v___x_8022_);
                    crate::leanh::lean_dec(v_unfold_8012_);
                    crate::leanh::lean_dec(v___y_8011_);
                    crate::leanh::lean_dec(v_tk_7920_);
                    v___x_8025_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__0___redArg();
                    return v___x_8025_;
                } else {
                    v___x_8026_ = l_Lean_Syntax_getArg(v___x_8022_, v___x_7793_);
                    v___x_8027_ = l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore___closed__9;
                    crate::leanh::lean_inc(v___x_8026_);
                    v___x_8028_ = l_Lean_Syntax_isOfKind(v___x_8026_, v___x_8027_);
                    if v___x_8028_ == 0 {
                        crate::leanh::lean_dec(v___x_8026_);
                        crate::leanh::lean_dec(v___x_8022_);
                        crate::leanh::lean_dec(v_unfold_8012_);
                        crate::leanh::lean_dec(v___y_8011_);
                        crate::leanh::lean_dec(v_tk_7920_);
                        v___x_8029_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__0___redArg();
                        return v___x_8029_;
                    } else {
                        v___x_8030_ = l_Lean_Syntax_getArg(v___x_8022_, v___x_7980_);
                        v___x_8031_ = l_Lean_Syntax_getArg(v___x_8022_, v___y_8010_);
                        v___x_8032_ = l_Lean_Syntax_isNone(v___x_8031_);
                        if v___x_8032_ == 0 {
                            crate::leanh::lean_inc(v___x_8031_);
                            v___x_8033_ = l_Lean_Syntax_matchesNull(v___x_8031_, v___x_7980_);
                            if v___x_8033_ == 0 {
                                crate::leanh::lean_dec(v___x_8031_);
                                crate::leanh::lean_dec(v___x_8030_);
                                crate::leanh::lean_dec(v___x_8026_);
                                crate::leanh::lean_dec(v___x_8022_);
                                crate::leanh::lean_dec(v_unfold_8012_);
                                crate::leanh::lean_dec(v___y_8011_);
                                crate::leanh::lean_dec(v_tk_7920_);
                                v___x_8034_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__0___redArg();
                                return v___x_8034_;
                            } else {
                                v_only_8035_ = l_Lean_Syntax_getArg(v___x_8031_, v___x_7793_);
                                crate::leanh::lean_dec(v___x_8031_);
                                v___x_8036_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                                crate::leanh::lean_ctor_set(v___x_8036_, 0, v_only_8035_);
                                v___y_7982_ = v_unfold_8012_;
                                v___y_7983_ = v___x_8022_;
                                v___y_7984_ = v___y_8011_;
                                v___y_7985_ = v___x_8021_;
                                v___y_7986_ = v___x_8026_;
                                v___y_7987_ = v___x_8030_;
                                v_only_7988_ = v___x_8036_;
                                v___y_7989_ = v___y_8013_;
                                v___y_7990_ = v___y_8014_;
                                v___y_7991_ = v___y_8015_;
                                v___y_7992_ = v___y_8016_;
                                v___y_7993_ = v___y_8017_;
                                v___y_7994_ = v___y_8018_;
                                v___y_7995_ = v___y_8019_;
                                v___y_7996_ = v___y_8020_;
                                state = 10;
                                continue;
                            }
                        } else {
                            crate::leanh::lean_dec(v___x_8031_);
                            v___x_8037_ = crate::leanh::lean_box(0);
                            v___y_7982_ = v_unfold_8012_;
                            v___y_7983_ = v___x_8022_;
                            v___y_7984_ = v___y_8011_;
                            v___y_7985_ = v___x_8021_;
                            v___y_7986_ = v___x_8026_;
                            v___y_7987_ = v___x_8030_;
                            v_only_7988_ = v___x_8037_;
                            v___y_7989_ = v___y_8013_;
                            v___y_7990_ = v___y_8014_;
                            v___y_7991_ = v___y_8015_;
                            v___y_7992_ = v___y_8016_;
                            v___y_7993_ = v___y_8017_;
                            v___y_7994_ = v___y_8018_;
                            v___y_7995_ = v___y_8019_;
                            v___y_7996_ = v___y_8020_;
                            state = 10;
                            continue;
                        }
                    }
                }
            }
            12 => {
                v___x_8048_ = crate::leanh::lean_unsigned_to_nat(2);
                v___x_8049_ = l_Lean_Syntax_getArg(v_stx_7749_, v___x_8048_);
                v___x_8050_ = l_Lean_Syntax_isNone(v___x_8049_);
                if v___x_8050_ == 0 {
                    crate::leanh::lean_inc(v___x_8049_);
                    v___x_8051_ = l_Lean_Syntax_matchesNull(v___x_8049_, v___x_7980_);
                    if v___x_8051_ == 0 {
                        crate::leanh::lean_dec(v___x_8049_);
                        crate::leanh::lean_dec(v_squeeze_8039_);
                        crate::leanh::lean_dec(v_tk_7920_);
                        crate::leanh::lean_dec(v_stx_7749_);
                        v___x_8052_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaCore_spec__0___redArg();
                        return v___x_8052_;
                    } else {
                        v_unfold_8053_ = l_Lean_Syntax_getArg(v___x_8049_, v___x_7793_);
                        crate::leanh::lean_dec(v___x_8049_);
                        v___x_8054_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_8054_, 0, v_unfold_8053_);
                        v___y_8010_ = v___x_8048_;
                        v___y_8011_ = v_squeeze_8039_;
                        v_unfold_8012_ = v___x_8054_;
                        v___y_8013_ = v___y_8040_;
                        v___y_8014_ = v___y_8041_;
                        v___y_8015_ = v___y_8042_;
                        v___y_8016_ = v___y_8043_;
                        v___y_8017_ = v___y_8044_;
                        v___y_8018_ = v___y_8045_;
                        v___y_8019_ = v___y_8046_;
                        v___y_8020_ = v___y_8047_;
                        state = 11;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v___x_8049_);
                    v___x_8055_ = crate::leanh::lean_box(0);
                    v___y_8010_ = v___x_8048_;
                    v___y_8011_ = v_squeeze_8039_;
                    v_unfold_8012_ = v___x_8055_;
                    v___y_8013_ = v___y_8040_;
                    v___y_8014_ = v___y_8041_;
                    v___y_8015_ = v___y_8042_;
                    v___y_8016_ = v___y_8043_;
                    v___y_8017_ = v___y_8044_;
                    v___y_8018_ = v___y_8045_;
                    v___y_8019_ = v___y_8046_;
                    v___y_8020_ = v___y_8047_;
                    state = 11;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_Tactic_Simpa_evalSimpaUsingBang___boxed(
    mut v_stx_8063_: *mut crate::leanh::LeanObject,
    mut v_a_8064_: *mut crate::leanh::LeanObject,
    mut v_a_8065_: *mut crate::leanh::LeanObject,
    mut v_a_8066_: *mut crate::leanh::LeanObject,
    mut v_a_8067_: *mut crate::leanh::LeanObject,
    mut v_a_8068_: *mut crate::leanh::LeanObject,
    mut v_a_8069_: *mut crate::leanh::LeanObject,
    mut v_a_8070_: *mut crate::leanh::LeanObject,
    mut v_a_8071_: *mut crate::leanh::LeanObject,
    mut v_a_8072_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_8073_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_8073_ = l_Lean_Elab_Tactic_Simpa_evalSimpaUsingBang(
        v_stx_8063_,
        v_a_8064_,
        v_a_8065_,
        v_a_8066_,
        v_a_8067_,
        v_a_8068_,
        v_a_8069_,
        v_a_8070_,
        v_a_8071_,
    );
    crate::leanh::lean_dec(v_a_8071_);
    crate::leanh::lean_dec_ref(v_a_8070_);
    crate::leanh::lean_dec(v_a_8069_);
    crate::leanh::lean_dec_ref(v_a_8068_);
    crate::leanh::lean_dec(v_a_8067_);
    crate::leanh::lean_dec_ref(v_a_8066_);
    crate::leanh::lean_dec(v_a_8065_);
    crate::leanh::lean_dec_ref(v_a_8064_);
    return v_res_8073_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaUsingBang___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpaUsingBang__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_8082_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8083_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8084_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8085_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8086_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_8082_ = l_Lean_Elab_Tactic_tacticElabAttribute;
    v___x_8083_ = l_Lean_Elab_Tactic_Simpa_evalSimpaUsingBang___closed__0;
    v___x_8084_ = l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaUsingBang___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpaUsingBang__1___closed__1;
    v___x_8085_ = crate::leanh::lean_alloc_closure(
        l_Lean_Elab_Tactic_Simpa_evalSimpaUsingBang___boxed as *mut core::ffi::c_void,
        10,
        0,
    );
    v___x_8086_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(
        v___x_8082_,
        v___x_8083_,
        v___x_8084_,
        v___x_8085_,
    );
    return v___x_8086_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaUsingBang___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpaUsingBang__1___boxed(
    mut v_a_8087_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_8088_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_8088_ = l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaUsingBang___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpaUsingBang__1();
    return v_res_8088_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Elab_Tactic_Simpa(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Meta_Tactic_TryThis(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_Tactic_Simp(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_App(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = l___private_Lean_Elab_Tactic_Simpa_0__initFn_00___x40_Lean_Elab_Tactic_Simpa_363244304____hygCtx___hyg_4_();
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    l_linter_unnecessarySimpa = crate::leanh::lean_io_result_get_value(res);
    crate::leanh::lean_mark_persistent(l_linter_unnecessarySimpa);
    crate::leanh::lean_dec_ref(res);
    res = l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpa___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpa__1();
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpa___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpa_declRange__3();
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = l___private_Lean_Elab_Tactic_Simpa_0__Lean_Elab_Tactic_Simpa_evalSimpaUsingBang___regBuiltin_Lean_Elab_Tactic_Simpa_evalSimpaUsingBang__1();
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Elab_Tactic_Simpa(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Elab_Tactic_Simpa(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Meta_Tactic_TryThis(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Elab_Tactic_Simp(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Elab_App(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_Tactic_Simpa(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Elab_Tactic_Simpa(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Lean_Elab_Tactic_Simpa(builtin);
}
