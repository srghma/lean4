// Lean compiler output
// Module: Lean.Meta.Tactic.Grind.Intro
// Imports: Init.Grind.Lemmas Lean.Meta.Tactic.Grind.Action Lean.Meta.Tactic.Apply Lean.Meta.Tactic.Grind.Util Lean.Meta.Tactic.Grind.CasesMatch Lean.Meta.Tactic.Grind.Injection Lean.Meta.Tactic.Grind.Core Lean.Meta.Tactic.Grind.RevertAll Init.Grind.Util
use crate::ffi::{
    lean_array_fget, lean_array_fget_borrowed, lean_array_fset, lean_array_get,
    lean_array_get_borrowed, lean_array_get_size, lean_array_push, lean_array_to_list,
    lean_expr_instantiate1, lean_grind_preprocess, lean_mk_empty_array_with_capacity, lean_name_eq,
    lean_nat_add, lean_nat_dec_eq, lean_nat_dec_le, lean_nat_dec_lt, lean_nat_sub, lean_st_mk_ref,
    lean_st_ref_get, lean_st_ref_set, lean_st_ref_take, lean_string_utf8_byte_size,
    lean_string_utf8_extract, lean_string_utf8_get_fast, lean_string_utf8_next_fast,
    lean_uint32_dec_eq, lean_uint64_of_nat, lean_uint64_to_usize, lean_usize_add,
    lean_usize_dec_le, lean_usize_land, lean_usize_mul, lean_usize_shift_left,
    lean_usize_shift_right, lean_usize_sub, lean_usize_to_nat, lean_whnf,
};
use crate::r#gen::Init::Data::Array::Basic::l_List_foldl___at___00Array_appendList_spec__0___redArg;
use crate::r#gen::Init::Data::List::Basic::l_List_reverse___redArg;
use crate::r#gen::Init::Data::Queue::l_Std_Queue_dequeue_x3f___redArg;
use crate::r#gen::Init::Data::String::Slice::l_String_Slice_isNat;
use crate::r#gen::Init::Grind::Lemmas::{
    initialize_Init_Grind_Lemmas, runtime_initialize_Init_Grind_Lemmas,
};
use crate::r#gen::Init::Grind::Util::{
    initialize_Init_Grind_Util, runtime_initialize_Init_Grind_Util,
};
use crate::r#gen::Init::Meta::Defs::lean_name_append_index_after;
use crate::r#gen::Init::Prelude::{
    l_Lean_Name_hasMacroScopes, l_Lean_Name_num___override, l_Lean_Name_str___override,
    l_Lean_replaceRef, lean_erase_macro_scopes,
};
use crate::r#gen::Lean::CoreM::l_Lean_Core_mkFreshUserName;
use crate::r#gen::Lean::Data::Name::l_Lean_Name_isAnonymous;
use crate::r#gen::Lean::Data::Options::l_Lean_Options_empty;
use crate::r#gen::Lean::Data::PersistentHashMap::{
    l_Lean_PersistentHashMap_getCollisionNodeSize___redArg,
    l_Lean_PersistentHashMap_mkCollisionNode___redArg, l_Lean_PersistentHashMap_mkEmptyEntries,
    l_Lean_PersistentHashMap_mkEmptyEntriesArray,
};
use crate::r#gen::Lean::Declaration::l_Lean_InductiveVal_numCtors;
use crate::r#gen::Lean::Environment::{
    l_Lean_Environment_contains, l_Lean_Environment_find_x3f,
    l_Lean_Environment_getModuleIdxFor_x3f, l_Lean_Environment_header,
    l_Lean_Environment_setExporting, l_Lean_EnvironmentHeader_moduleNames,
};
use crate::r#gen::Lean::Exception::l_Lean_unknownIdentifierMessageTag;
use crate::r#gen::Lean::Expr::{
    l_Lean_Expr_appFnCleanup___redArg, l_Lean_Expr_bindingBody_x21, l_Lean_Expr_bindingDomain_x21,
    l_Lean_Expr_bindingInfo_x21, l_Lean_Expr_bindingName_x21, l_Lean_Expr_cleanupAnnotations,
    l_Lean_Expr_getAppFn, l_Lean_Expr_isApp, l_Lean_Expr_isArrow, l_Lean_Expr_isConstOf,
    l_Lean_Expr_isFalse, l_Lean_Expr_isForall, l_Lean_Expr_isLet, l_Lean_Expr_mvarId_x21,
    l_Lean_instBEqMVarId_beq, l_Lean_instHashableMVarId_hash, l_Lean_mkApp4, l_Lean_mkAppN,
    l_Lean_mkConst, l_Lean_mkFVar, l_Lean_mkLambda,
};
use crate::r#gen::Lean::LocalContext::{
    l_Lean_LocalContext_lastDecl, l_Lean_LocalContext_mkLocalDecl, l_Lean_LocalDecl_type,
    l_Lean_LocalDecl_value,
};
use crate::r#gen::Lean::Message::{
    l_Lean_MessageData_note, l_Lean_MessageData_ofConstName, l_Lean_MessageData_ofName,
    l_Lean_stringToMessageData,
};
use crate::r#gen::Lean::Meta::Basic::{
    l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp, l_Lean_FVarId_getDecl___redArg,
    l_Lean_FVarId_getType___redArg, l_Lean_MVarId_getDecl, l_Lean_Meta_isClass_x3f,
    l_Lean_Meta_mkFreshExprMVarAt, l_Lean_Meta_mkLambdaFVars,
};
use crate::r#gen::Lean::Meta::InferType::{l_Lean_Meta_getLevel, l_Lean_Meta_isProp};
use crate::r#gen::Lean::Meta::Sym::Canon::l_Lean_Meta_Sym_canon;
use crate::r#gen::Lean::Meta::Sym::SymM::l_Lean_Meta_Sym_shareCommon___redArg;
use crate::r#gen::Lean::Meta::Tactic::Apply::{
    initialize_Lean_Meta_Tactic_Apply, l_Lean_MVarId_exfalso,
    runtime_initialize_Lean_Meta_Tactic_Apply,
};
use crate::r#gen::Lean::Meta::Tactic::Assert::l_Lean_MVarId_assert;
use crate::r#gen::Lean::Meta::Tactic::Grind::Action::{
    initialize_Lean_Meta_Tactic_Grind_Action, l_Lean_Meta_Grind_Action_andThen,
    l_Lean_Meta_Grind_Action_group___redArg, l_Lean_Meta_Grind_Action_loop___boxed,
    l_Lean_Meta_Grind_Action_loop___redArg, l_Lean_Meta_Grind_Action_ungroup___boxed,
    runtime_initialize_Lean_Meta_Tactic_Grind_Action,
};
use crate::r#gen::Lean::Meta::Tactic::Grind::Cases::l_Lean_Meta_Grind_cases;
use crate::r#gen::Lean::Meta::Tactic::Grind::CasesMatch::{
    initialize_Lean_Meta_Tactic_Grind_CasesMatch, l_Lean_Meta_Grind_isMatchCondCandidate,
    runtime_initialize_Lean_Meta_Tactic_Grind_CasesMatch,
};
use crate::r#gen::Lean::Meta::Tactic::Grind::Core::{
    initialize_Lean_Meta_Tactic_Grind_Core, l_Lean_Meta_Grind_add, l_Lean_Meta_Grind_addHypothesis,
    l_Lean_Meta_Grind_addNewEq, runtime_initialize_Lean_Meta_Tactic_Grind_Core,
};
use crate::r#gen::Lean::Meta::Tactic::Grind::Injection::{
    initialize_Lean_Meta_Tactic_Grind_Injection, l_Lean_Meta_Grind_injection_x3f,
    runtime_initialize_Lean_Meta_Tactic_Grind_Injection,
};
use crate::r#gen::Lean::Meta::Tactic::Grind::RevertAll::{
    initialize_Lean_Meta_Tactic_Grind_RevertAll, l_Lean_Meta_Grind_getOriginalName_x3f,
    runtime_initialize_Lean_Meta_Tactic_Grind_RevertAll,
};
use crate::r#gen::Lean::Meta::Tactic::Grind::Types::{
    l_Lean_Meta_Grind_Solvers_mkActionCore, l_Lean_Meta_Grind_cheapCasesOnly___redArg,
    l_Lean_Meta_Grind_getConfig___redArg, l_Lean_Meta_Grind_instInhabitedGoal_default,
    l_Lean_Meta_Grind_isEagerSplit___redArg, l_Lean_Meta_Grind_saveCases___redArg,
};
use crate::r#gen::Lean::Meta::Tactic::Grind::Util::{
    initialize_Lean_Meta_Tactic_Grind_Util, l_Lean_MVarId_byContra_x3f,
    l_Lean_Meta_Grind_markAsPreMatchCond, runtime_initialize_Lean_Meta_Tactic_Grind_Util,
};
use crate::r#gen::Lean::Meta::Tactic::Intro::l_Lean_MVarId_intro;
use crate::r#gen::Lean::Meta::Tactic::Simp::Types::l_Lean_Meta_Simp_Result_getProof;
use crate::r#gen::Lean::Meta::Tactic::Util::{
    l_Lean_MVarId_getTag, l_Lean_MVarId_getType, l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar,
};
use crate::r#gen::Lean::Meta::WHNF::l_Lean_Meta_expandLet;
use crate::r#gen::Lean::PrivateName::l_Lean_isPrivateName;
static mut l_Lean_Meta_Grind_instInhabitedIntroResult_default___closed__0_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Grind_instInhabitedIntroResult_default___closed__0:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static mut l_Lean_Meta_Grind_instInhabitedIntroResult_default: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_instInhabitedIntroResult: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isAlreadyNorm_x3f___closed__0_value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [76, 101, 97, 110, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isAlreadyNorm_x3f___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isAlreadyNorm_x3f___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isAlreadyNorm_x3f___closed__1_value: crate::leanh::LeanStringObject<6> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [71, 114, 105, 110, 100, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isAlreadyNorm_x3f___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isAlreadyNorm_x3f___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isAlreadyNorm_x3f___closed__2_value: crate::leanh::LeanStringObject<12> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 12, m_capacity: 12, m_length: 11, m_data: [97, 108, 114, 101, 97, 100, 121, 78, 111, 114, 109, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isAlreadyNorm_x3f___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isAlreadyNorm_x3f___closed__2_value) as *mut crate::leanh::LeanObject;
static l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isAlreadyNorm_x3f___closed__3_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isAlreadyNorm_x3f___closed__0_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isAlreadyNorm_x3f___closed__3_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isAlreadyNorm_x3f___closed__3_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isAlreadyNorm_x3f___closed__1_value) as *mut crate::leanh::LeanObject,13563742693681136756 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isAlreadyNorm_x3f___closed__3_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isAlreadyNorm_x3f___closed__3_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isAlreadyNorm_x3f___closed__2_value) as *mut crate::leanh::LeanObject,17640825121910087155 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isAlreadyNorm_x3f___closed__3: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isAlreadyNorm_x3f___closed__3_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkBaseName___closed__0_value: crate::leanh::LeanStringObject<2> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [120, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkBaseName___closed__0:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkBaseName___closed__0_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkBaseName___closed__1_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkBaseName___closed__0_value) as *mut crate::leanh::LeanObject,13655884332201764339 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkBaseName___closed__1:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkBaseName___closed__1_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkBaseName___closed__2_value: crate::leanh::LeanStringObject<2> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [104, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkBaseName___closed__2:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkBaseName___closed__2_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkBaseName___closed__3_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkBaseName___closed__2_value) as *mut crate::leanh::LeanObject,8738205681931236784 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkBaseName___closed__3:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkBaseName___closed__3_value
) as *mut crate::leanh::LeanObject;
static mut l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__1_spec__2___redArg___closed__0_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__1_spec__2___redArg___closed__0: usize = 0;
static mut l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__1_spec__2___redArg___closed__1_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__1_spec__2___redArg___closed__1: usize = 0;
static mut l_Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__1___redArg___closed__0_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__1___redArg___closed__0: u64 = 0;
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__0_spec__0___redArg___closed__0_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__0_spec__0___redArg___closed__0: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName___closed__0_value: crate::leanh::LeanStringObject<2> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [97, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName___closed__0:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName___closed__0_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName___closed__1_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName___closed__0_value) as *mut crate::leanh::LeanObject,7839396180116328695 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName___closed__1:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName___closed__1_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_intro1___closed__0_value:
    crate::leanh::LeanStringObject<40> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 40,
    m_capacity: 40,
    m_length: 39,
    m_data: [
        96, 103, 114, 105, 110, 100, 96, 32, 105, 110, 116, 101, 114, 110, 97, 108, 32, 101, 114,
        114, 111, 114, 44, 32, 98, 105, 110, 100, 101, 114, 32, 101, 120, 112, 101, 99, 116, 101,
        100, 0,
    ],
};
static mut l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_intro1___closed__0:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_intro1___closed__0_value
) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_intro1___closed__1_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_intro1___closed__1:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lam__4___closed__0_value: crate::leanh::LeanStringObject<14> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 14, m_capacity: 14, m_length: 13, m_data: [105, 110, 116, 114, 111, 95, 119, 105, 116, 104, 95, 101, 113, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lam__4___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lam__4___closed__0_value) as *mut crate::leanh::LeanObject;
static l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lam__4___closed__1_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isAlreadyNorm_x3f___closed__0_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lam__4___closed__1_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lam__4___closed__1_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isAlreadyNorm_x3f___closed__1_value) as *mut crate::leanh::LeanObject,13563742693681136756 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lam__4___closed__1_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lam__4___closed__1_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lam__4___closed__0_value) as *mut crate::leanh::LeanObject,13220042744452896961 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lam__4___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lam__4___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lam__3___closed__0_value: crate::leanh::LeanStringObject<15> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 15, m_capacity: 15, m_length: 14, m_data: [105, 110, 116, 114, 111, 95, 119, 105, 116, 104, 95, 101, 113, 39, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lam__3___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lam__3___closed__0_value) as *mut crate::leanh::LeanObject;
static l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lam__3___closed__1_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isAlreadyNorm_x3f___closed__0_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lam__3___closed__1_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lam__3___closed__1_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isAlreadyNorm_x3f___closed__1_value) as *mut crate::leanh::LeanObject,13563742693681136756 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lam__3___closed__1_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lam__3___closed__1_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lam__3___closed__0_value) as *mut crate::leanh::LeanObject,228924277063512984 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lam__3___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lam__3___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lam__5___closed__0_value: crate::leanh::LeanArrayObject<0> = crate::leanh::LeanArrayObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 246 }, m_size: 0, m_capacity: 0, m_data: [] };
static mut l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lam__5___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lam__5___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lam__5___closed__2_value: crate::leanh::LeanStringObject<9> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [109, 112, 114, 95, 112, 114, 111, 112, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lam__5___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lam__5___closed__2_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lam__5___closed__1_value: crate::leanh::LeanStringObject<3> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [69, 113, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lam__5___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lam__5___closed__1_value) as *mut crate::leanh::LeanObject;
static l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lam__5___closed__3_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lam__5___closed__1_value) as *mut crate::leanh::LeanObject,16122875713692181903 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lam__5___closed__3_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lam__5___closed__3_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lam__5___closed__2_value) as *mut crate::leanh::LeanObject,15841710565803995561 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lam__5___closed__3: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lam__5___closed__3_value) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lam__5___closed__4_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lam__5___closed__4: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__0_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__0: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__1_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__1: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__2_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__2: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__3_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__3: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__4_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__4: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__5_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__5: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__6_value: crate::leanh::LeanStringObject<24> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 24, m_capacity: 24, m_length: 23, m_data: [65, 32, 112, 114, 105, 118, 97, 116, 101, 32, 100, 101, 99, 108, 97, 114, 97, 116, 105, 111, 110, 32, 96, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__6: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__6_value) as *mut crate::leanh::LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__7_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__7: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__8_value: crate::leanh::LeanStringObject<79> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 79, m_capacity: 79, m_length: 78, m_data: [96, 32, 40, 102, 114, 111, 109, 32, 116, 104, 101, 32, 99, 117, 114, 114, 101, 110, 116, 32, 109, 111, 100, 117, 108, 101, 41, 32, 101, 120, 105, 115, 116, 115, 32, 98, 117, 116, 32, 119, 111, 117, 108, 100, 32, 110, 101, 101, 100, 32, 116, 111, 32, 98, 101, 32, 112, 117, 98, 108, 105, 99, 32, 116, 111, 32, 97, 99, 99, 101, 115, 115, 32, 104, 101, 114, 101, 46, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__8: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__8_value) as *mut crate::leanh::LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__9_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__9: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__10_value: crate::leanh::LeanStringObject<23> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 23, m_capacity: 23, m_length: 22, m_data: [65, 32, 112, 117, 98, 108, 105, 99, 32, 100, 101, 99, 108, 97, 114, 97, 116, 105, 111, 110, 32, 96, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__10: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__10_value) as *mut crate::leanh::LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__11_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__11: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__12_value: crate::leanh::LeanStringObject<68> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 68, m_capacity: 68, m_length: 67, m_data: [96, 32, 101, 120, 105, 115, 116, 115, 32, 98, 117, 116, 32, 105, 115, 32, 105, 109, 112, 111, 114, 116, 101, 100, 32, 112, 114, 105, 118, 97, 116, 101, 108, 121, 59, 32, 99, 111, 110, 115, 105, 100, 101, 114, 32, 97, 100, 100, 105, 110, 103, 32, 96, 112, 117, 98, 108, 105, 99, 32, 105, 109, 112, 111, 114, 116, 32, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__12: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__12_value) as *mut crate::leanh::LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__13_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__13: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__14_value: crate::leanh::LeanStringObject<3> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [96, 46, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__14: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__14_value) as *mut crate::leanh::LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__15_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__15: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__16_value: crate::leanh::LeanStringObject<10> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [96, 32, 40, 102, 114, 111, 109, 32, 96, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__16: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__16_value) as *mut crate::leanh::LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__17_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__17: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__18_value: crate::leanh::LeanStringObject<54> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 54, m_capacity: 54, m_length: 53, m_data: [96, 41, 32, 101, 120, 105, 115, 116, 115, 32, 98, 117, 116, 32, 119, 111, 117, 108, 100, 32, 110, 101, 101, 100, 32, 116, 111, 32, 98, 101, 32, 112, 117, 98, 108, 105, 99, 32, 116, 111, 32, 97, 99, 99, 101, 115, 115, 32, 104, 101, 114, 101, 46, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__18: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__18_value) as *mut crate::leanh::LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__19_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__19: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1___redArg___closed__0_value: crate::leanh::LeanStringObject<19> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 19, m_capacity: 19, m_length: 18, m_data: [85, 110, 107, 110, 111, 119, 110, 32, 99, 111, 110, 115, 116, 97, 110, 116, 32, 96, 0]};
static mut l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1___redArg___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1___redArg___closed__0_value) as *mut crate::leanh::LeanObject;
static mut l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1___redArg___closed__1_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1___redArg___closed__1: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1___redArg___closed__2_value: crate::leanh::LeanStringObject<2> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [96, 0]};
static mut l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1___redArg___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1___redArg___closed__2_value) as *mut crate::leanh::LeanObject;
static mut l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1___redArg___closed__3_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1___redArg___closed__3: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_Action_applyCases_x3f___lam__0___closed__0_value: crate::leanh::LeanArrayObject<0> = crate::leanh::LeanArrayObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 246 }, m_size: 0, m_capacity: 0, m_data: [] };
static mut l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_Action_applyCases_x3f___lam__0___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_Action_applyCases_x3f___lam__0___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_Action_applyCases_x3f___lam__0___closed__1_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_Action_applyCases_x3f___lam__0___closed__0_value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_Action_applyCases_x3f___lam__0___closed__0_value) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_Action_applyCases_x3f___lam__0___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_Action_applyCases_x3f___lam__0___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Grind_Action_intro___closed__0_value: crate::leanh::LeanCtorObject<1> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 0,
        },
        m_objs: [(((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject],
    };
static mut l_Lean_Meta_Grind_Action_intro___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Action_intro___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_Action_hugeNumber:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Meta_Grind_Action_intros___closed__0_value: crate::leanh::LeanClosureObject<0> =
    crate::leanh::LeanClosureObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Lean_Meta_Grind_Action_intros___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 13,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Meta_Grind_Action_intros___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Action_intros___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Grind_Action_intros___closed__1_value: crate::leanh::LeanClosureObject<0> =
    crate::leanh::LeanClosureObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Lean_Meta_Grind_Action_ungroup___boxed as *const core::ffi::c_void,
        m_arity: 13,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Meta_Grind_Action_intros___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Action_intros___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_Action_assertAt___lam__0___closed__0_value: crate::leanh::LeanStringObject<3> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [109, 112, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_Action_assertAt___lam__0___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_Action_assertAt___lam__0___closed__0_value) as *mut crate::leanh::LeanObject;
static l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_Action_assertAt___lam__0___closed__1_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lam__5___closed__1_value) as *mut crate::leanh::LeanObject,16122875713692181903 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_Action_assertAt___lam__0___closed__1_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_Action_assertAt___lam__0___closed__1_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_Action_assertAt___lam__0___closed__0_value) as *mut crate::leanh::LeanObject,5647098122476602039 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_Action_assertAt___lam__0___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_Action_assertAt___lam__0___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_Action_assertAt___lam__0___closed__2_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_Action_assertAt___lam__0___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_Action_assertAt___lam__0___closed__2_value) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_Action_assertAt___lam__0___closed__3_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_Action_assertAt___lam__0___closed__3: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Meta_Grind_Solvers_mkAction___closed__0_value: crate::leanh::LeanClosureObject<
    0,
> = crate::leanh::LeanClosureObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_Meta_Grind_Solvers_mkAction___lam__0___boxed as *const core::ffi::c_void,
    m_arity: 13,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Meta_Grind_Solvers_mkAction___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Solvers_mkAction___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_IntroResult_ctorIdx(
    mut v_x_4289_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    match crate::leanh::lean_obj_tag(v_x_4289_) {
        0 => {
            let mut v___x_4290_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_4290_ = crate::leanh::lean_unsigned_to_nat(0);
            return v___x_4290_;
        }
        1 => {
            let mut v___x_4291_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_4291_ = crate::leanh::lean_unsigned_to_nat(1);
            return v___x_4291_;
        }
        2 => {
            let mut v___x_4292_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_4292_ = crate::leanh::lean_unsigned_to_nat(2);
            return v___x_4292_;
        }
        _ => {
            let mut v___x_4293_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_4293_ = crate::leanh::lean_unsigned_to_nat(3);
            return v___x_4293_;
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_IntroResult_ctorIdx___boxed(
    mut v_x_4294_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4295_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4295_ =
        l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_IntroResult_ctorIdx(v_x_4294_);
    crate::leanh::lean_dec_ref(v_x_4294_);
    return v_res_4295_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_IntroResult_ctorElim___redArg(
    mut v_t_4296_: *mut crate::leanh::LeanObject,
    mut v_k_4297_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    match crate::leanh::lean_obj_tag(v_t_4296_) {
        1 => {
            let mut v_fvarId_4298_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_goal_4299_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_4300_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v_fvarId_4298_ = crate::leanh::lean_ctor_get(v_t_4296_, 0);
            crate::leanh::lean_inc(v_fvarId_4298_);
            v_goal_4299_ = crate::leanh::lean_ctor_get(v_t_4296_, 1);
            crate::leanh::lean_inc_ref(v_goal_4299_);
            crate::leanh::lean_dec_ref_known(v_t_4296_, 2);
            v___x_4300_ = crate::leanh::lean_apply_2(v_k_4297_, v_fvarId_4298_, v_goal_4299_);
            return v___x_4300_;
        }
        3 => {
            let mut v_fvarId_4301_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_goal_4302_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_4303_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v_fvarId_4301_ = crate::leanh::lean_ctor_get(v_t_4296_, 0);
            crate::leanh::lean_inc(v_fvarId_4301_);
            v_goal_4302_ = crate::leanh::lean_ctor_get(v_t_4296_, 1);
            crate::leanh::lean_inc_ref(v_goal_4302_);
            crate::leanh::lean_dec_ref_known(v_t_4296_, 2);
            v___x_4303_ = crate::leanh::lean_apply_2(v_k_4297_, v_fvarId_4301_, v_goal_4302_);
            return v___x_4303_;
        }
        _ => {
            let mut v_goal_4304_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_4305_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v_goal_4304_ = crate::leanh::lean_ctor_get(v_t_4296_, 0);
            crate::leanh::lean_inc_ref(v_goal_4304_);
            crate::leanh::lean_dec_ref(v_t_4296_);
            v___x_4305_ = crate::leanh::lean_apply_1(v_k_4297_, v_goal_4304_);
            return v___x_4305_;
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_IntroResult_ctorElim(
    mut v_motive_4306_: *mut crate::leanh::LeanObject,
    mut v_ctorIdx_4307_: *mut crate::leanh::LeanObject,
    mut v_t_4308_: *mut crate::leanh::LeanObject,
    mut v_h_4309_: *mut crate::leanh::LeanObject,
    mut v_k_4310_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4311_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4311_ =
        l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_IntroResult_ctorElim___redArg(
            v_t_4308_, v_k_4310_,
        );
    return v___x_4311_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_IntroResult_ctorElim___boxed(
    mut v_motive_4312_: *mut crate::leanh::LeanObject,
    mut v_ctorIdx_4313_: *mut crate::leanh::LeanObject,
    mut v_t_4314_: *mut crate::leanh::LeanObject,
    mut v_h_4315_: *mut crate::leanh::LeanObject,
    mut v_k_4316_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4317_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4317_ = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_IntroResult_ctorElim(
        v_motive_4312_,
        v_ctorIdx_4313_,
        v_t_4314_,
        v_h_4315_,
        v_k_4316_,
    );
    crate::leanh::lean_dec(v_ctorIdx_4313_);
    return v_res_4317_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_IntroResult_done_elim___redArg(
    mut v_t_4318_: *mut crate::leanh::LeanObject,
    mut v_done_4319_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4320_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4320_ =
        l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_IntroResult_ctorElim___redArg(
            v_t_4318_,
            v_done_4319_,
        );
    return v___x_4320_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_IntroResult_done_elim(
    mut v_motive_4321_: *mut crate::leanh::LeanObject,
    mut v_t_4322_: *mut crate::leanh::LeanObject,
    mut v_h_4323_: *mut crate::leanh::LeanObject,
    mut v_done_4324_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4325_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4325_ =
        l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_IntroResult_ctorElim___redArg(
            v_t_4322_,
            v_done_4324_,
        );
    return v___x_4325_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_IntroResult_newHyp_elim___redArg(
    mut v_t_4326_: *mut crate::leanh::LeanObject,
    mut v_newHyp_4327_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4328_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4328_ =
        l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_IntroResult_ctorElim___redArg(
            v_t_4326_,
            v_newHyp_4327_,
        );
    return v___x_4328_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_IntroResult_newHyp_elim(
    mut v_motive_4329_: *mut crate::leanh::LeanObject,
    mut v_t_4330_: *mut crate::leanh::LeanObject,
    mut v_h_4331_: *mut crate::leanh::LeanObject,
    mut v_newHyp_4332_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4333_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4333_ =
        l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_IntroResult_ctorElim___redArg(
            v_t_4330_,
            v_newHyp_4332_,
        );
    return v___x_4333_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_IntroResult_newDepHyp_elim___redArg(
    mut v_t_4334_: *mut crate::leanh::LeanObject,
    mut v_newDepHyp_4335_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4336_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4336_ =
        l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_IntroResult_ctorElim___redArg(
            v_t_4334_,
            v_newDepHyp_4335_,
        );
    return v___x_4336_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_IntroResult_newDepHyp_elim(
    mut v_motive_4337_: *mut crate::leanh::LeanObject,
    mut v_t_4338_: *mut crate::leanh::LeanObject,
    mut v_h_4339_: *mut crate::leanh::LeanObject,
    mut v_newDepHyp_4340_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4341_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4341_ =
        l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_IntroResult_ctorElim___redArg(
            v_t_4338_,
            v_newDepHyp_4340_,
        );
    return v___x_4341_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_IntroResult_newLocal_elim___redArg(
    mut v_t_4342_: *mut crate::leanh::LeanObject,
    mut v_newLocal_4343_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4344_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4344_ =
        l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_IntroResult_ctorElim___redArg(
            v_t_4342_,
            v_newLocal_4343_,
        );
    return v___x_4344_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_IntroResult_newLocal_elim(
    mut v_motive_4345_: *mut crate::leanh::LeanObject,
    mut v_t_4346_: *mut crate::leanh::LeanObject,
    mut v_h_4347_: *mut crate::leanh::LeanObject,
    mut v_newLocal_4348_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4349_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4349_ =
        l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_IntroResult_ctorElim___redArg(
            v_t_4346_,
            v_newLocal_4348_,
        );
    return v___x_4349_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_instInhabitedIntroResult_default___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4350_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4351_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4350_ = l_Lean_Meta_Grind_instInhabitedGoal_default;
    v___x_4351_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_4351_, 0, v___x_4350_);
    return v___x_4351_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_instInhabitedIntroResult_default()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4352_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4352_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Grind_instInhabitedIntroResult_default___closed__0),
        core::ptr::addr_of_mut!(
            l_Lean_Meta_Grind_instInhabitedIntroResult_default___closed__0_once
        ),
        _init_l_Lean_Meta_Grind_instInhabitedIntroResult_default___closed__0,
    );
    return v___x_4352_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_instInhabitedIntroResult()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4353_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4353_ = l_Lean_Meta_Grind_instInhabitedIntroResult_default;
    return v___x_4353_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isAlreadyNorm_x3f(
    mut v_e_4361_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4362_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4363_: u8 = 0;
    v___x_4362_ = l_Lean_Expr_cleanupAnnotations(v_e_4361_);
    v___x_4363_ = l_Lean_Expr_isApp(v___x_4362_);
    if v___x_4363_ == 0 {
        let mut v___x_4364_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec_ref(v___x_4362_);
        v___x_4364_ = crate::leanh::lean_box(0);
        return v___x_4364_;
    } else {
        let mut v_arg_4365_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4366_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4367_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4368_: u8 = 0;
        v_arg_4365_ = crate::leanh::lean_ctor_get(v___x_4362_, 1);
        crate::leanh::lean_inc_ref(v_arg_4365_);
        v___x_4366_ = l_Lean_Expr_appFnCleanup___redArg(v___x_4362_);
        v___x_4367_ = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isAlreadyNorm_x3f___closed__3;
        v___x_4368_ = l_Lean_Expr_isConstOf(v___x_4366_, v___x_4367_);
        crate::leanh::lean_dec_ref(v___x_4366_);
        if v___x_4368_ == 0 {
            let mut v___x_4369_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec_ref(v_arg_4365_);
            v___x_4369_ = crate::leanh::lean_box(0);
            return v___x_4369_;
        } else {
            let mut v___x_4370_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_4370_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
            crate::leanh::lean_ctor_set(v___x_4370_, 0, v_arg_4365_);
            return v___x_4370_;
        }
    }
}
pub unsafe fn l_Lean_Meta_Grind_preprocessHypothesis(
    mut v_e_4371_: *mut crate::leanh::LeanObject,
    mut v_a_4372_: *mut crate::leanh::LeanObject,
    mut v_a_4373_: *mut crate::leanh::LeanObject,
    mut v_a_4374_: *mut crate::leanh::LeanObject,
    mut v_a_4375_: *mut crate::leanh::LeanObject,
    mut v_a_4376_: *mut crate::leanh::LeanObject,
    mut v_a_4377_: *mut crate::leanh::LeanObject,
    mut v_a_4378_: *mut crate::leanh::LeanObject,
    mut v_a_4379_: *mut crate::leanh::LeanObject,
    mut v_a_4380_: *mut crate::leanh::LeanObject,
    mut v_a_4381_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4383_: u8 = 0;
    let mut v___x_4384_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_4385_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4386_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4387_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4388_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4389_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4391_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4392_: u8 = 0;
    let mut v___x_4393_: u8 = 0;
    let mut v___x_4394_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4395_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4397_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4398_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4399_: u8 = 0;
    let mut v_a_4400_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4402_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4403_: u8 = 0;
    let mut v___x_4405_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4406_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4407_: u8 = 0;
    let mut v_a_4408_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4410_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4411_: u8 = 0;
    let mut v___x_4413_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4414_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4415_: u8 = 0;
    let mut v___x_4416_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4417_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4418_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                crate::leanh::lean_inc_ref(v_e_4371_);
                v___x_4383_ = l_Lean_Meta_Grind_isMatchCondCandidate(v_e_4371_);
                if v___x_4383_ == 0 {
                    crate::leanh::lean_inc_ref(v_e_4371_);
                    v___x_4384_ = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isAlreadyNorm_x3f(v_e_4371_);
                    if crate::leanh::lean_obj_tag(v___x_4384_) == 1 {
                        crate::leanh::lean_dec_ref(v_e_4371_);
                        v_val_4385_ = crate::leanh::lean_ctor_get(v___x_4384_, 0);
                        crate::leanh::lean_inc(v_val_4385_);
                        crate::leanh::lean_dec_ref_known(v___x_4384_, 1);
                        v___x_4386_ = l_Lean_Meta_Sym_canon(
                            v_val_4385_,
                            v_a_4376_,
                            v_a_4377_,
                            v_a_4378_,
                            v_a_4379_,
                            v_a_4380_,
                            v_a_4381_,
                        );
                        if crate::leanh::lean_obj_tag(v___x_4386_) == 0 {
                            v_a_4387_ = crate::leanh::lean_ctor_get(v___x_4386_, 0);
                            crate::leanh::lean_inc(v_a_4387_);
                            crate::leanh::lean_dec_ref_known(v___x_4386_, 1);
                            v___x_4388_ =
                                l_Lean_Meta_Sym_shareCommon___redArg(v_a_4387_, v_a_4377_);
                            if crate::leanh::lean_obj_tag(v___x_4388_) == 0 {
                                v_a_4389_ = crate::leanh::lean_ctor_get(v___x_4388_, 0);
                                v_isSharedCheck_4399_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_4388_)) as u8;
                                if v_isSharedCheck_4399_ == 0 {
                                    v___x_4391_ = v___x_4388_;
                                    v_isShared_4392_ = v_isSharedCheck_4399_;
                                    state = 1;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_a_4389_);
                                    crate::leanh::lean_dec(v___x_4388_);
                                    v___x_4391_ = crate::leanh::lean_box(0);
                                    v_isShared_4392_ = v_isSharedCheck_4399_;
                                    state = 1;
                                    continue;
                                }
                            } else {
                                v_a_4400_ = crate::leanh::lean_ctor_get(v___x_4388_, 0);
                                v_isSharedCheck_4407_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_4388_)) as u8;
                                if v_isSharedCheck_4407_ == 0 {
                                    v___x_4402_ = v___x_4388_;
                                    v_isShared_4403_ = v_isSharedCheck_4407_;
                                    state = 3;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_a_4400_);
                                    crate::leanh::lean_dec(v___x_4388_);
                                    v___x_4402_ = crate::leanh::lean_box(0);
                                    v_isShared_4403_ = v_isSharedCheck_4407_;
                                    state = 3;
                                    continue;
                                }
                            }
                        } else {
                            v_a_4408_ = crate::leanh::lean_ctor_get(v___x_4386_, 0);
                            v_isSharedCheck_4415_ =
                                (!crate::leanh::lean_is_exclusive(v___x_4386_)) as u8;
                            if v_isSharedCheck_4415_ == 0 {
                                v___x_4410_ = v___x_4386_;
                                v_isShared_4411_ = v_isSharedCheck_4415_;
                                state = 5;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_4408_);
                                crate::leanh::lean_dec(v___x_4386_);
                                v___x_4410_ = crate::leanh::lean_box(0);
                                v_isShared_4411_ = v_isSharedCheck_4415_;
                                state = 5;
                                continue;
                            }
                        }
                    } else {
                        crate::leanh::lean_dec(v___x_4384_);
                        crate::leanh::lean_inc(v_a_4381_);
                        crate::leanh::lean_inc_ref(v_a_4380_);
                        crate::leanh::lean_inc(v_a_4379_);
                        crate::leanh::lean_inc_ref(v_a_4378_);
                        crate::leanh::lean_inc(v_a_4377_);
                        crate::leanh::lean_inc_ref(v_a_4376_);
                        crate::leanh::lean_inc(v_a_4375_);
                        crate::leanh::lean_inc_ref(v_a_4374_);
                        crate::leanh::lean_inc(v_a_4373_);
                        crate::leanh::lean_inc(v_a_4372_);
                        v___x_4416_ = lean_grind_preprocess(
                            v_e_4371_, v_a_4372_, v_a_4373_, v_a_4374_, v_a_4375_, v_a_4376_,
                            v_a_4377_, v_a_4378_, v_a_4379_, v_a_4380_, v_a_4381_,
                        );
                        return v___x_4416_;
                    }
                } else {
                    v___x_4417_ = l_Lean_Meta_Grind_markAsPreMatchCond(v_e_4371_);
                    crate::leanh::lean_inc(v_a_4381_);
                    crate::leanh::lean_inc_ref(v_a_4380_);
                    crate::leanh::lean_inc(v_a_4379_);
                    crate::leanh::lean_inc_ref(v_a_4378_);
                    crate::leanh::lean_inc(v_a_4377_);
                    crate::leanh::lean_inc_ref(v_a_4376_);
                    crate::leanh::lean_inc(v_a_4375_);
                    crate::leanh::lean_inc_ref(v_a_4374_);
                    crate::leanh::lean_inc(v_a_4373_);
                    crate::leanh::lean_inc(v_a_4372_);
                    v___x_4418_ = lean_grind_preprocess(
                        v___x_4417_,
                        v_a_4372_,
                        v_a_4373_,
                        v_a_4374_,
                        v_a_4375_,
                        v_a_4376_,
                        v_a_4377_,
                        v_a_4378_,
                        v_a_4379_,
                        v_a_4380_,
                        v_a_4381_,
                    );
                    return v___x_4418_;
                }
            }
            1 => {
                v___x_4393_ = 1;
                v___x_4394_ = crate::leanh::lean_box(0);
                v___x_4395_ = crate::leanh::lean_alloc_ctor(0, 2, (1) as u32);
                crate::leanh::lean_ctor_set(v___x_4395_, 0, v_a_4389_);
                crate::leanh::lean_ctor_set(v___x_4395_, 1, v___x_4394_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_4395_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2) as u32,
                    v___x_4393_,
                );
                if v_isShared_4392_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4391_, 0, v___x_4395_);
                    v___x_4397_ = v___x_4391_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4398_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4398_, 0, v___x_4395_);
                    v___x_4397_ = v_reuseFailAlloc_4398_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_4397_;
            }
            3 => {
                if v_isShared_4403_ == 0 {
                    v___x_4405_ = v___x_4402_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4406_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4406_, 0, v_a_4400_);
                    v___x_4405_ = v_reuseFailAlloc_4406_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_4405_;
            }
            5 => {
                if v_isShared_4411_ == 0 {
                    v___x_4413_ = v___x_4410_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_4414_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4414_, 0, v_a_4408_);
                    v___x_4413_ = v_reuseFailAlloc_4414_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_4413_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Grind_preprocessHypothesis___boxed(
    mut v_e_4419_: *mut crate::leanh::LeanObject,
    mut v_a_4420_: *mut crate::leanh::LeanObject,
    mut v_a_4421_: *mut crate::leanh::LeanObject,
    mut v_a_4422_: *mut crate::leanh::LeanObject,
    mut v_a_4423_: *mut crate::leanh::LeanObject,
    mut v_a_4424_: *mut crate::leanh::LeanObject,
    mut v_a_4425_: *mut crate::leanh::LeanObject,
    mut v_a_4426_: *mut crate::leanh::LeanObject,
    mut v_a_4427_: *mut crate::leanh::LeanObject,
    mut v_a_4428_: *mut crate::leanh::LeanObject,
    mut v_a_4429_: *mut crate::leanh::LeanObject,
    mut v_a_4430_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4431_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4431_ = l_Lean_Meta_Grind_preprocessHypothesis(
        v_e_4419_, v_a_4420_, v_a_4421_, v_a_4422_, v_a_4423_, v_a_4424_, v_a_4425_, v_a_4426_,
        v_a_4427_, v_a_4428_, v_a_4429_,
    );
    crate::leanh::lean_dec(v_a_4429_);
    crate::leanh::lean_dec_ref(v_a_4428_);
    crate::leanh::lean_dec(v_a_4427_);
    crate::leanh::lean_dec_ref(v_a_4426_);
    crate::leanh::lean_dec(v_a_4425_);
    crate::leanh::lean_dec_ref(v_a_4424_);
    crate::leanh::lean_dec(v_a_4423_);
    crate::leanh::lean_dec_ref(v_a_4422_);
    crate::leanh::lean_dec(v_a_4421_);
    crate::leanh::lean_dec(v_a_4420_);
    return v_res_4431_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkBaseName_spec__0___redArg(
    mut v___x_4432_: *mut crate::leanh::LeanObject,
    mut v_str_4433_: *mut crate::leanh::LeanObject,
    mut v_a_4434_: *mut crate::leanh::LeanObject,
    mut v_b_4435_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_startInclusive_4436_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_endExclusive_4437_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4438_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4439_: u8 = 0;
    let mut v___x_4440_: u32 = 0;
    let mut v___x_4441_: u32 = 0;
    let mut v___x_4442_: u8 = 0;
    let mut v___x_4443_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4444_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4446_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_startInclusive_4436_ = crate::leanh::lean_ctor_get(v___x_4432_, 1);
                v_endExclusive_4437_ = crate::leanh::lean_ctor_get(v___x_4432_, 2);
                v___x_4438_ = lean_nat_sub(v_endExclusive_4437_, v_startInclusive_4436_);
                v___x_4439_ = lean_nat_dec_eq(v_a_4434_, v___x_4438_);
                crate::leanh::lean_dec(v___x_4438_);
                if v___x_4439_ == 0 {
                    v___x_4440_ = lean_string_utf8_get_fast(v_str_4433_, v_a_4434_);
                    v___x_4441_ = 95;
                    v___x_4442_ = lean_uint32_dec_eq(v___x_4440_, v___x_4441_);
                    if v___x_4442_ == 0 {
                        v___x_4443_ = crate::leanh::lean_box(0);
                        v___x_4444_ = lean_string_utf8_next_fast(v_str_4433_, v_a_4434_);
                        crate::leanh::lean_dec(v_a_4434_);
                        v_a_4434_ = v___x_4444_;
                        v_b_4435_ = v___x_4443_;
                        state = 0;
                        continue;
                    } else {
                        v___x_4446_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_4446_, 0, v_a_4434_);
                        return v___x_4446_;
                    }
                } else {
                    crate::leanh::lean_dec(v_a_4434_);
                    crate::leanh::lean_inc(v_b_4435_);
                    return v_b_4435_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkBaseName_spec__0___redArg___boxed(
    mut v___x_4447_: *mut crate::leanh::LeanObject,
    mut v_str_4448_: *mut crate::leanh::LeanObject,
    mut v_a_4449_: *mut crate::leanh::LeanObject,
    mut v_b_4450_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4451_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4451_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkBaseName_spec__0___redArg(v___x_4447_, v_str_4448_, v_a_4449_, v_b_4450_);
    crate::leanh::lean_dec(v_b_4450_);
    crate::leanh::lean_dec_ref(v_str_4448_);
    crate::leanh::lean_dec_ref(v___x_4447_);
    return v_res_4451_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkBaseName(
    mut v_name_4458_: *mut crate::leanh::LeanObject,
    mut v_type_4459_: *mut crate::leanh::LeanObject,
    mut v_a_4460_: *mut crate::leanh::LeanObject,
    mut v_a_4461_: *mut crate::leanh::LeanObject,
    mut v_a_4462_: *mut crate::leanh::LeanObject,
    mut v_a_4463_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_4466_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4467_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4468_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4469_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4470_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4471_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4473_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4474_: u8 = 0;
    let mut v___x_4475_: u8 = 0;
    let mut v___x_4476_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4478_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4479_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4480_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4482_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4483_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4484_: u8 = 0;
    let mut v_a_4485_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4487_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4488_: u8 = 0;
    let mut v___x_4490_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4491_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4492_: u8 = 0;
    let mut v_str_4493_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4495_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4496_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4497_: u8 = 0;
    let mut v___x_4498_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_suffix_4499_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4500_: u8 = 0;
    let mut v___x_4501_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4502_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4503_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4504_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4505_: u8 = 0;
    let mut v___x_4506_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4507_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4508_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4509_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4510_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4511_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4512_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_searcher_4513_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4514_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4515_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4516_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4517_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_4518_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_name_4458_) == 1 {
                    v_str_4493_ = crate::leanh::lean_ctor_get(v_name_4458_, 1);
                    crate::leanh::lean_inc_ref_n(v_str_4493_, 2);
                    crate::leanh::lean_dec_ref_known(v_name_4458_, 2);
                    v_searcher_4513_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___x_4514_ = lean_string_utf8_byte_size(v_str_4493_);
                    v___x_4515_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_4515_, 0, v_str_4493_);
                    crate::leanh::lean_ctor_set(v___x_4515_, 1, v_searcher_4513_);
                    crate::leanh::lean_ctor_set(v___x_4515_, 2, v___x_4514_);
                    v___x_4516_ = crate::leanh::lean_box(0);
                    v___x_4517_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkBaseName_spec__0___redArg(v___x_4515_, v_str_4493_, v_searcher_4513_, v___x_4516_);
                    crate::leanh::lean_dec_ref_known(v___x_4515_, 3);
                    if crate::leanh::lean_obj_tag(v___x_4517_) == 0 {
                        v___y_4495_ = v___x_4514_;
                        state = 7;
                        continue;
                    } else {
                        v_val_4518_ = crate::leanh::lean_ctor_get(v___x_4517_, 0);
                        crate::leanh::lean_inc(v_val_4518_);
                        crate::leanh::lean_dec_ref_known(v___x_4517_, 1);
                        v___y_4495_ = v_val_4518_;
                        state = 7;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_name_4458_);
                    v___y_4466_ = v_a_4460_;
                    v___y_4467_ = v_a_4461_;
                    v___y_4468_ = v_a_4462_;
                    v___y_4469_ = v_a_4463_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_4470_ = l_Lean_Meta_isProp(
                    v_type_4459_,
                    v___y_4466_,
                    v___y_4467_,
                    v___y_4468_,
                    v___y_4469_,
                );
                if crate::leanh::lean_obj_tag(v___x_4470_) == 0 {
                    v_a_4471_ = crate::leanh::lean_ctor_get(v___x_4470_, 0);
                    v_isSharedCheck_4484_ = (!crate::leanh::lean_is_exclusive(v___x_4470_)) as u8;
                    if v_isSharedCheck_4484_ == 0 {
                        v___x_4473_ = v___x_4470_;
                        v_isShared_4474_ = v_isSharedCheck_4484_;
                        state = 2;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4471_);
                        crate::leanh::lean_dec(v___x_4470_);
                        v___x_4473_ = crate::leanh::lean_box(0);
                        v_isShared_4474_ = v_isSharedCheck_4484_;
                        state = 2;
                        continue;
                    }
                } else {
                    v_a_4485_ = crate::leanh::lean_ctor_get(v___x_4470_, 0);
                    v_isSharedCheck_4492_ = (!crate::leanh::lean_is_exclusive(v___x_4470_)) as u8;
                    if v_isSharedCheck_4492_ == 0 {
                        v___x_4487_ = v___x_4470_;
                        v_isShared_4488_ = v_isSharedCheck_4492_;
                        state = 5;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4485_);
                        crate::leanh::lean_dec(v___x_4470_);
                        v___x_4487_ = crate::leanh::lean_box(0);
                        v_isShared_4488_ = v_isSharedCheck_4492_;
                        state = 5;
                        continue;
                    }
                }
            }
            2 => {
                v___x_4475_ = (crate::leanh::lean_unbox(v_a_4471_) as u8);
                crate::leanh::lean_dec(v_a_4471_);
                if v___x_4475_ == 0 {
                    v___x_4476_ = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkBaseName___closed__1;
                    if v_isShared_4474_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_4473_, 0, v___x_4476_);
                        v___x_4478_ = v___x_4473_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_4479_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4479_, 0, v___x_4476_);
                        v___x_4478_ = v_reuseFailAlloc_4479_;
                        state = 3;
                        continue;
                    }
                } else {
                    v___x_4480_ = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkBaseName___closed__3;
                    if v_isShared_4474_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_4473_, 0, v___x_4480_);
                        v___x_4482_ = v___x_4473_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_4483_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4483_, 0, v___x_4480_);
                        v___x_4482_ = v_reuseFailAlloc_4483_;
                        state = 4;
                        continue;
                    }
                }
            }
            3 => {
                return v___x_4478_;
            }
            4 => {
                return v___x_4482_;
            }
            5 => {
                if v_isShared_4488_ == 0 {
                    v___x_4490_ = v___x_4487_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_4491_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4491_, 0, v_a_4485_);
                    v___x_4490_ = v_reuseFailAlloc_4491_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_4490_;
            }
            7 => {
                v___x_4496_ = lean_string_utf8_byte_size(v_str_4493_);
                v___x_4497_ = lean_nat_dec_eq(v___y_4495_, v___x_4496_);
                if v___x_4497_ == 0 {
                    v___x_4498_ = lean_string_utf8_next_fast(v_str_4493_, v___y_4495_);
                    crate::leanh::lean_inc_ref(v_str_4493_);
                    v_suffix_4499_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                    crate::leanh::lean_ctor_set(v_suffix_4499_, 0, v_str_4493_);
                    crate::leanh::lean_ctor_set(v_suffix_4499_, 1, v___x_4498_);
                    crate::leanh::lean_ctor_set(v_suffix_4499_, 2, v___x_4496_);
                    v___x_4500_ = l_String_Slice_isNat(v_suffix_4499_);
                    crate::leanh::lean_dec_ref_known(v_suffix_4499_, 3);
                    if v___x_4500_ == 0 {
                        crate::leanh::lean_dec(v___y_4495_);
                        crate::leanh::lean_dec_ref(v_type_4459_);
                        v___x_4501_ = crate::leanh::lean_box(0);
                        v___x_4502_ = l_Lean_Name_str___override(v___x_4501_, v_str_4493_);
                        v___x_4503_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_4503_, 0, v___x_4502_);
                        return v___x_4503_;
                    } else {
                        v___x_4504_ = crate::leanh::lean_unsigned_to_nat(0);
                        v___x_4505_ = lean_nat_dec_eq(v___y_4495_, v___x_4504_);
                        if v___x_4505_ == 0 {
                            crate::leanh::lean_dec_ref(v_type_4459_);
                            v___x_4506_ =
                                lean_string_utf8_extract(v_str_4493_, v___x_4504_, v___y_4495_);
                            crate::leanh::lean_dec(v___y_4495_);
                            crate::leanh::lean_dec_ref(v_str_4493_);
                            v___x_4507_ = crate::leanh::lean_box(0);
                            v___x_4508_ = l_Lean_Name_str___override(v___x_4507_, v___x_4506_);
                            v___x_4509_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_4509_, 0, v___x_4508_);
                            return v___x_4509_;
                        } else {
                            crate::leanh::lean_dec(v___y_4495_);
                            crate::leanh::lean_dec_ref(v_str_4493_);
                            v___y_4466_ = v_a_4460_;
                            v___y_4467_ = v_a_4461_;
                            v___y_4468_ = v_a_4462_;
                            v___y_4469_ = v_a_4463_;
                            state = 1;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec(v___y_4495_);
                    crate::leanh::lean_dec_ref(v_type_4459_);
                    v___x_4510_ = crate::leanh::lean_box(0);
                    v___x_4511_ = l_Lean_Name_str___override(v___x_4510_, v_str_4493_);
                    v___x_4512_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_4512_, 0, v___x_4511_);
                    return v___x_4512_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkBaseName___boxed(
    mut v_name_4519_: *mut crate::leanh::LeanObject,
    mut v_type_4520_: *mut crate::leanh::LeanObject,
    mut v_a_4521_: *mut crate::leanh::LeanObject,
    mut v_a_4522_: *mut crate::leanh::LeanObject,
    mut v_a_4523_: *mut crate::leanh::LeanObject,
    mut v_a_4524_: *mut crate::leanh::LeanObject,
    mut v_a_4525_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4526_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4526_ = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkBaseName(
        v_name_4519_,
        v_type_4520_,
        v_a_4521_,
        v_a_4522_,
        v_a_4523_,
        v_a_4524_,
    );
    crate::leanh::lean_dec(v_a_4524_);
    crate::leanh::lean_dec_ref(v_a_4523_);
    crate::leanh::lean_dec(v_a_4522_);
    crate::leanh::lean_dec_ref(v_a_4521_);
    return v_res_4526_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkBaseName_spec__0(
    mut v___x_4527_: *mut crate::leanh::LeanObject,
    mut v_str_4528_: *mut crate::leanh::LeanObject,
    mut v_inst_4529_: *mut crate::leanh::LeanObject,
    mut v_R_4530_: *mut crate::leanh::LeanObject,
    mut v_a_4531_: *mut crate::leanh::LeanObject,
    mut v_b_4532_: *mut crate::leanh::LeanObject,
    mut v_c_4533_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4534_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4534_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkBaseName_spec__0___redArg(v___x_4527_, v_str_4528_, v_a_4531_, v_b_4532_);
    return v___x_4534_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkBaseName_spec__0___boxed(
    mut v___x_4535_: *mut crate::leanh::LeanObject,
    mut v_str_4536_: *mut crate::leanh::LeanObject,
    mut v_inst_4537_: *mut crate::leanh::LeanObject,
    mut v_R_4538_: *mut crate::leanh::LeanObject,
    mut v_a_4539_: *mut crate::leanh::LeanObject,
    mut v_b_4540_: *mut crate::leanh::LeanObject,
    mut v_c_4541_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4542_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4542_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkBaseName_spec__0(v___x_4535_, v_str_4536_, v_inst_4537_, v_R_4538_, v_a_4539_, v_b_4540_, v_c_4541_);
    crate::leanh::lean_dec(v_b_4540_);
    crate::leanh::lean_dec_ref(v_str_4536_);
    crate::leanh::lean_dec_ref(v___x_4535_);
    return v_res_4542_;
}
pub unsafe fn l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__1_spec__2_spec__5___redArg(
    mut v_keys_4543_: *mut crate::leanh::LeanObject,
    mut v_i_4544_: *mut crate::leanh::LeanObject,
    mut v_k_4545_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_4546_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4547_: u8 = 0;
    let mut v_k_x27_4548_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4549_: u8 = 0;
    let mut v___x_4550_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4551_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4546_ = lean_array_get_size(v_keys_4543_);
                v___x_4547_ = lean_nat_dec_lt(v_i_4544_, v___x_4546_);
                if v___x_4547_ == 0 {
                    crate::leanh::lean_dec(v_i_4544_);
                    return v___x_4547_;
                } else {
                    v_k_x27_4548_ = lean_array_fget_borrowed(v_keys_4543_, v_i_4544_);
                    v___x_4549_ = lean_name_eq(v_k_4545_, v_k_x27_4548_);
                    if v___x_4549_ == 0 {
                        v___x_4550_ = crate::leanh::lean_unsigned_to_nat(1);
                        v___x_4551_ = lean_nat_add(v_i_4544_, v___x_4550_);
                        crate::leanh::lean_dec(v_i_4544_);
                        v_i_4544_ = v___x_4551_;
                        state = 0;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v_i_4544_);
                        return v___x_4549_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__1_spec__2_spec__5___redArg___boxed(
    mut v_keys_4553_: *mut crate::leanh::LeanObject,
    mut v_i_4554_: *mut crate::leanh::LeanObject,
    mut v_k_4555_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4556_: u8 = 0;
    let mut v_r_4557_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4556_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__1_spec__2_spec__5___redArg(v_keys_4553_, v_i_4554_, v_k_4555_);
    crate::leanh::lean_dec(v_k_4555_);
    crate::leanh::lean_dec_ref(v_keys_4553_);
    v_r_4557_ = crate::leanh::lean_box((v_res_4556_) as usize);
    return v_r_4557_;
}
pub unsafe fn _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__1_spec__2___redArg___closed__0()
-> usize {
    let mut v___x_4558_: usize = 0;
    let mut v___x_4559_: usize = 0;
    let mut v___x_4560_: usize = 0;
    v___x_4558_ = 5usize;
    v___x_4559_ = 1usize;
    v___x_4560_ = lean_usize_shift_left(v___x_4559_, v___x_4558_);
    return v___x_4560_;
}
pub unsafe fn _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__1_spec__2___redArg___closed__1()
-> usize {
    let mut v___x_4561_: usize = 0;
    let mut v___x_4562_: usize = 0;
    let mut v___x_4563_: usize = 0;
    v___x_4561_ = 1usize;
    v___x_4562_ = crate::leanh::lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__1_spec__2___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__1_spec__2___redArg___closed__0_once), _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__1_spec__2___redArg___closed__0);
    v___x_4563_ = lean_usize_sub(v___x_4562_, v___x_4561_);
    return v___x_4563_;
}
pub unsafe fn l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__1_spec__2___redArg(
    mut v_x_4564_: *mut crate::leanh::LeanObject,
    mut v_x_4565_: usize,
    mut v_x_4566_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v_es_4567_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4568_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4569_: usize = 0;
    let mut v___x_4570_: usize = 0;
    let mut v___x_4571_: usize = 0;
    let mut v_j_4572_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4573_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_key_4574_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4575_: u8 = 0;
    let mut v_node_4576_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4577_: usize = 0;
    let mut v___x_4579_: u8 = 0;
    let mut v_ks_4580_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4581_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4582_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_4564_) == 0 {
                    v_es_4567_ = crate::leanh::lean_ctor_get(v_x_4564_, 0);
                    v___x_4568_ = crate::leanh::lean_box(2);
                    v___x_4569_ = 5usize;
                    v___x_4570_ = crate::leanh::lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__1_spec__2___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__1_spec__2___redArg___closed__1_once), _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__1_spec__2___redArg___closed__1);
                    v___x_4571_ = lean_usize_land(v_x_4565_, v___x_4570_);
                    v_j_4572_ = lean_usize_to_nat(v___x_4571_);
                    v___x_4573_ = lean_array_get_borrowed(v___x_4568_, v_es_4567_, v_j_4572_);
                    crate::leanh::lean_dec(v_j_4572_);
                    match crate::leanh::lean_obj_tag(v___x_4573_) {
                        0 => {
                            v_key_4574_ = crate::leanh::lean_ctor_get(v___x_4573_, 0);
                            v___x_4575_ = lean_name_eq(v_x_4566_, v_key_4574_);
                            return v___x_4575_;
                        }
                        1 => {
                            v_node_4576_ = crate::leanh::lean_ctor_get(v___x_4573_, 0);
                            v___x_4577_ = lean_usize_shift_right(v_x_4565_, v___x_4569_);
                            v_x_4564_ = v_node_4576_;
                            v_x_4565_ = v___x_4577_;
                            state = 0;
                            continue;
                        }
                        _ => {
                            v___x_4579_ = 0;
                            return v___x_4579_;
                        }
                    }
                } else {
                    v_ks_4580_ = crate::leanh::lean_ctor_get(v_x_4564_, 0);
                    v___x_4581_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___x_4582_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__1_spec__2_spec__5___redArg(v_ks_4580_, v___x_4581_, v_x_4566_);
                    return v___x_4582_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__1_spec__2___redArg___boxed(
    mut v_x_4583_: *mut crate::leanh::LeanObject,
    mut v_x_4584_: *mut crate::leanh::LeanObject,
    mut v_x_4585_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_39859__boxed_4586_: usize = 0;
    let mut v_res_4587_: u8 = 0;
    let mut v_r_4588_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_39859__boxed_4586_ = crate::leanh::lean_unbox_usize(v_x_4584_);
    crate::leanh::lean_dec(v_x_4584_);
    v_res_4587_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__1_spec__2___redArg(v_x_4583_, v_x_39859__boxed_4586_, v_x_4585_);
    crate::leanh::lean_dec(v_x_4585_);
    crate::leanh::lean_dec_ref(v_x_4583_);
    v_r_4588_ = crate::leanh::lean_box((v_res_4587_) as usize);
    return v_r_4588_;
}
pub unsafe fn _init_l_Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__1___redArg___closed__0()
-> u64 {
    let mut v___x_4589_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4590_: u64 = 0;
    v___x_4589_ = crate::leanh::lean_unsigned_to_nat(1723);
    v___x_4590_ = lean_uint64_of_nat(v___x_4589_);
    return v___x_4590_;
}
pub unsafe fn l_Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__1___redArg(
    mut v_x_4591_: *mut crate::leanh::LeanObject,
    mut v_x_4592_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___y_4594_: u64 = 0;
    let mut v___x_4595_: usize = 0;
    let mut v___x_4596_: u8 = 0;
    let mut v___x_4597_: u64 = 0;
    let mut v_hash_4598_: u64 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_4592_) == 0 {
                    v___x_4597_ = crate::leanh::lean_uint64_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__1___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__1___redArg___closed__0_once), _init_l_Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__1___redArg___closed__0);
                    v___y_4594_ = v___x_4597_;
                    state = 1;
                    continue;
                } else {
                    v_hash_4598_ = crate::leanh::lean_ctor_get_uint64(
                        v_x_4592_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2) as u32,
                    );
                    v___y_4594_ = v_hash_4598_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_4595_ = lean_uint64_to_usize(v___y_4594_);
                v___x_4596_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__1_spec__2___redArg(v_x_4591_, v___x_4595_, v_x_4592_);
                return v___x_4596_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__1___redArg___boxed(
    mut v_x_4599_: *mut crate::leanh::LeanObject,
    mut v_x_4600_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4601_: u8 = 0;
    let mut v_r_4602_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4601_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__1___redArg(v_x_4599_, v_x_4600_);
    crate::leanh::lean_dec(v_x_4600_);
    crate::leanh::lean_dec_ref(v_x_4599_);
    v_r_4602_ = crate::leanh::lean_box((v_res_4601_) as usize);
    return v_r_4602_;
}
pub unsafe fn l___private_Init_While_0__whileM_erased___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__2___redArg(
    mut v_a_4603_: *mut crate::leanh::LeanObject,
    mut v_a_4604_: *mut crate::leanh::LeanObject,
    mut v___y_4605_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4607_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toGoalState_4608_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_clean_4609_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_4610_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4612_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4613_: u8 = 0;
    let mut v_used_4614_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4615_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4616_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4617_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4618_: u8 = 0;
    let mut v___x_4620_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4621_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4622_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4624_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4626_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4627_: u8 = 0;
    let mut v_unused_4628_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4607_ = lean_st_ref_get(v___y_4605_);
                v_toGoalState_4608_ = crate::leanh::lean_ctor_get(v___x_4607_, 0);
                crate::leanh::lean_inc_ref(v_toGoalState_4608_);
                crate::leanh::lean_dec(v___x_4607_);
                v_clean_4609_ = crate::leanh::lean_ctor_get(v_toGoalState_4608_, 15);
                crate::leanh::lean_inc_ref(v_clean_4609_);
                crate::leanh::lean_dec_ref(v_toGoalState_4608_);
                v_snd_4610_ = crate::leanh::lean_ctor_get(v_a_4604_, 1);
                v_isSharedCheck_4627_ = (!crate::leanh::lean_is_exclusive(v_a_4604_)) as u8;
                if v_isSharedCheck_4627_ == 0 {
                    v_unused_4628_ = crate::leanh::lean_ctor_get(v_a_4604_, 0);
                    crate::leanh::lean_dec(v_unused_4628_);
                    v___x_4612_ = v_a_4604_;
                    v_isShared_4613_ = v_isSharedCheck_4627_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snd_4610_);
                    crate::leanh::lean_dec(v_a_4604_);
                    v___x_4612_ = crate::leanh::lean_box(0);
                    v_isShared_4613_ = v_isSharedCheck_4627_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_used_4614_ = crate::leanh::lean_ctor_get(v_clean_4609_, 0);
                crate::leanh::lean_inc_ref(v_used_4614_);
                crate::leanh::lean_dec_ref(v_clean_4609_);
                crate::leanh::lean_inc(v_snd_4610_);
                crate::leanh::lean_inc(v_a_4603_);
                v___x_4615_ = lean_name_append_index_after(v_a_4603_, v_snd_4610_);
                v___x_4616_ = crate::leanh::lean_unsigned_to_nat(1);
                v___x_4617_ = lean_nat_add(v_snd_4610_, v___x_4616_);
                crate::leanh::lean_dec(v_snd_4610_);
                v___x_4618_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__1___redArg(v_used_4614_, v___x_4615_);
                crate::leanh::lean_dec_ref(v_used_4614_);
                if v___x_4618_ == 0 {
                    crate::leanh::lean_dec(v_a_4603_);
                    if v_isShared_4613_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_4612_, 1, v___x_4617_);
                        crate::leanh::lean_ctor_set(v___x_4612_, 0, v___x_4615_);
                        v___x_4620_ = v___x_4612_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_4622_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4622_, 0, v___x_4615_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4622_, 1, v___x_4617_);
                        v___x_4620_ = v_reuseFailAlloc_4622_;
                        state = 2;
                        continue;
                    }
                } else {
                    if v_isShared_4613_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_4612_, 1, v___x_4617_);
                        crate::leanh::lean_ctor_set(v___x_4612_, 0, v___x_4615_);
                        v___x_4624_ = v___x_4612_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_4626_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4626_, 0, v___x_4615_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4626_, 1, v___x_4617_);
                        v___x_4624_ = v_reuseFailAlloc_4626_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                v___x_4621_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4621_, 0, v___x_4620_);
                return v___x_4621_;
            }
            3 => {
                v_a_4604_ = v___x_4624_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_While_0__whileM_erased___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__2___redArg___boxed(
    mut v_a_4629_: *mut crate::leanh::LeanObject,
    mut v_a_4630_: *mut crate::leanh::LeanObject,
    mut v___y_4631_: *mut crate::leanh::LeanObject,
    mut v___y_4632_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4633_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4633_ = l___private_Init_While_0__whileM_erased___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__2___redArg(v_a_4629_, v_a_4630_, v___y_4631_);
    crate::leanh::lean_dec(v___y_4631_);
    return v_res_4633_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__0_spec__0_spec__1_spec__5___redArg(
    mut v_x_4634_: *mut crate::leanh::LeanObject,
    mut v_x_4635_: *mut crate::leanh::LeanObject,
    mut v_x_4636_: *mut crate::leanh::LeanObject,
    mut v_x_4637_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_ks_4638_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_vs_4639_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4641_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4642_: u8 = 0;
    let mut v___x_4643_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4644_: u8 = 0;
    let mut v___x_4645_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4646_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4648_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4649_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_x27_4650_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4651_: u8 = 0;
    let mut v___x_4653_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4654_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4655_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4657_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4658_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4659_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4661_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4662_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4663_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ks_4638_ = crate::leanh::lean_ctor_get(v_x_4634_, 0);
                v_vs_4639_ = crate::leanh::lean_ctor_get(v_x_4634_, 1);
                v_isSharedCheck_4663_ = (!crate::leanh::lean_is_exclusive(v_x_4634_)) as u8;
                if v_isSharedCheck_4663_ == 0 {
                    v___x_4641_ = v_x_4634_;
                    v_isShared_4642_ = v_isSharedCheck_4663_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_vs_4639_);
                    crate::leanh::lean_inc(v_ks_4638_);
                    crate::leanh::lean_dec(v_x_4634_);
                    v___x_4641_ = crate::leanh::lean_box(0);
                    v_isShared_4642_ = v_isSharedCheck_4663_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_4643_ = lean_array_get_size(v_ks_4638_);
                v___x_4644_ = lean_nat_dec_lt(v_x_4635_, v___x_4643_);
                if v___x_4644_ == 0 {
                    crate::leanh::lean_dec(v_x_4635_);
                    v___x_4645_ = lean_array_push(v_ks_4638_, v_x_4636_);
                    v___x_4646_ = lean_array_push(v_vs_4639_, v_x_4637_);
                    if v_isShared_4642_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_4641_, 1, v___x_4646_);
                        crate::leanh::lean_ctor_set(v___x_4641_, 0, v___x_4645_);
                        v___x_4648_ = v___x_4641_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_4649_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4649_, 0, v___x_4645_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4649_, 1, v___x_4646_);
                        v___x_4648_ = v_reuseFailAlloc_4649_;
                        state = 2;
                        continue;
                    }
                } else {
                    v_k_x27_4650_ = lean_array_fget_borrowed(v_ks_4638_, v_x_4635_);
                    v___x_4651_ = lean_name_eq(v_x_4636_, v_k_x27_4650_);
                    if v___x_4651_ == 0 {
                        if v_isShared_4642_ == 0 {
                            v___x_4653_ = v___x_4641_;
                            state = 3;
                            continue;
                        } else {
                            v_reuseFailAlloc_4657_ =
                                crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_4657_, 0, v_ks_4638_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_4657_, 1, v_vs_4639_);
                            v___x_4653_ = v_reuseFailAlloc_4657_;
                            state = 3;
                            continue;
                        }
                    } else {
                        v___x_4658_ = lean_array_fset(v_ks_4638_, v_x_4635_, v_x_4636_);
                        v___x_4659_ = lean_array_fset(v_vs_4639_, v_x_4635_, v_x_4637_);
                        crate::leanh::lean_dec(v_x_4635_);
                        if v_isShared_4642_ == 0 {
                            crate::leanh::lean_ctor_set(v___x_4641_, 1, v___x_4659_);
                            crate::leanh::lean_ctor_set(v___x_4641_, 0, v___x_4658_);
                            v___x_4661_ = v___x_4641_;
                            state = 4;
                            continue;
                        } else {
                            v_reuseFailAlloc_4662_ =
                                crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_4662_, 0, v___x_4658_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_4662_, 1, v___x_4659_);
                            v___x_4661_ = v_reuseFailAlloc_4662_;
                            state = 4;
                            continue;
                        }
                    }
                }
            }
            2 => {
                return v___x_4648_;
            }
            3 => {
                v___x_4654_ = crate::leanh::lean_unsigned_to_nat(1);
                v___x_4655_ = lean_nat_add(v_x_4635_, v___x_4654_);
                crate::leanh::lean_dec(v_x_4635_);
                v_x_4634_ = v___x_4653_;
                v_x_4635_ = v___x_4655_;
                state = 0;
                continue;
            }
            4 => {
                return v___x_4661_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__0_spec__0_spec__1___redArg(
    mut v_n_4664_: *mut crate::leanh::LeanObject,
    mut v_k_4665_: *mut crate::leanh::LeanObject,
    mut v_v_4666_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4667_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4668_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4667_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_4668_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__0_spec__0_spec__1_spec__5___redArg(v_n_4664_, v___x_4667_, v_k_4665_, v_v_4666_);
    return v___x_4668_;
}
pub unsafe fn _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__0_spec__0___redArg___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4669_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4669_ = l_Lean_PersistentHashMap_mkEmptyEntries(
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
    );
    return v___x_4669_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__0_spec__0___redArg(
    mut v_x_4670_: *mut crate::leanh::LeanObject,
    mut v_x_4671_: usize,
    mut v_x_4672_: usize,
    mut v_x_4673_: *mut crate::leanh::LeanObject,
    mut v_x_4674_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_es_4675_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4676_: usize = 0;
    let mut v___x_4677_: usize = 0;
    let mut v___x_4678_: usize = 0;
    let mut v___x_4679_: usize = 0;
    let mut v_j_4680_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4681_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4682_: u8 = 0;
    let mut v___x_4684_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4685_: u8 = 0;
    let mut v_v_4686_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4687_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_xs_x27_4688_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4690_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4691_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4693_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4694_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_key_4695_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_4696_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4698_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4699_: u8 = 0;
    let mut v___x_4700_: u8 = 0;
    let mut v___x_4701_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4702_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4704_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4705_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4706_: u8 = 0;
    let mut v_node_4707_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4709_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4710_: u8 = 0;
    let mut v___x_4711_: usize = 0;
    let mut v___x_4712_: usize = 0;
    let mut v___x_4713_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4715_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4716_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4717_: u8 = 0;
    let mut v___x_4718_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4719_: u8 = 0;
    let mut v_unused_4720_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ks_4721_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_vs_4722_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4724_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4725_: u8 = 0;
    let mut v___x_4727_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_newNode_4728_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4730_: u8 = 0;
    let mut v_ks_4731_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_vs_4732_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4733_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4734_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4735_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4736_: usize = 0;
    let mut v___x_4737_: u8 = 0;
    let mut v___x_4738_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4739_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4740_: u8 = 0;
    let mut v_reuseFailAlloc_4741_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4742_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_4670_) == 0 {
                    v_es_4675_ = crate::leanh::lean_ctor_get(v_x_4670_, 0);
                    v___x_4676_ = 5usize;
                    v___x_4677_ = 1usize;
                    v___x_4678_ = crate::leanh::lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__1_spec__2___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__1_spec__2___redArg___closed__1_once), _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__1_spec__2___redArg___closed__1);
                    v___x_4679_ = lean_usize_land(v_x_4671_, v___x_4678_);
                    v_j_4680_ = lean_usize_to_nat(v___x_4679_);
                    v___x_4681_ = lean_array_get_size(v_es_4675_);
                    v___x_4682_ = lean_nat_dec_lt(v_j_4680_, v___x_4681_);
                    if v___x_4682_ == 0 {
                        crate::leanh::lean_dec(v_j_4680_);
                        crate::leanh::lean_dec(v_x_4674_);
                        crate::leanh::lean_dec(v_x_4673_);
                        return v_x_4670_;
                    } else {
                        crate::leanh::lean_inc_ref(v_es_4675_);
                        v_isSharedCheck_4719_ = (!crate::leanh::lean_is_exclusive(v_x_4670_)) as u8;
                        if v_isSharedCheck_4719_ == 0 {
                            v_unused_4720_ = crate::leanh::lean_ctor_get(v_x_4670_, 0);
                            crate::leanh::lean_dec(v_unused_4720_);
                            v___x_4684_ = v_x_4670_;
                            v_isShared_4685_ = v_isSharedCheck_4719_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_dec(v_x_4670_);
                            v___x_4684_ = crate::leanh::lean_box(0);
                            v_isShared_4685_ = v_isSharedCheck_4719_;
                            state = 1;
                            continue;
                        }
                    }
                } else {
                    v_ks_4721_ = crate::leanh::lean_ctor_get(v_x_4670_, 0);
                    v_vs_4722_ = crate::leanh::lean_ctor_get(v_x_4670_, 1);
                    v_isSharedCheck_4742_ = (!crate::leanh::lean_is_exclusive(v_x_4670_)) as u8;
                    if v_isSharedCheck_4742_ == 0 {
                        v___x_4724_ = v_x_4670_;
                        v_isShared_4725_ = v_isSharedCheck_4742_;
                        state = 8;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_vs_4722_);
                        crate::leanh::lean_inc(v_ks_4721_);
                        crate::leanh::lean_dec(v_x_4670_);
                        v___x_4724_ = crate::leanh::lean_box(0);
                        v_isShared_4725_ = v_isSharedCheck_4742_;
                        state = 8;
                        continue;
                    }
                }
            }
            1 => {
                v_v_4686_ = lean_array_fget(v_es_4675_, v_j_4680_);
                v___x_4687_ = crate::leanh::lean_box(0);
                v_xs_x27_4688_ = lean_array_fset(v_es_4675_, v_j_4680_, v___x_4687_);
                match crate::leanh::lean_obj_tag(v_v_4686_) {
                    0 => {
                        v_key_4695_ = crate::leanh::lean_ctor_get(v_v_4686_, 0);
                        v_val_4696_ = crate::leanh::lean_ctor_get(v_v_4686_, 1);
                        v_isSharedCheck_4706_ = (!crate::leanh::lean_is_exclusive(v_v_4686_)) as u8;
                        if v_isSharedCheck_4706_ == 0 {
                            v___x_4698_ = v_v_4686_;
                            v_isShared_4699_ = v_isSharedCheck_4706_;
                            state = 4;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_val_4696_);
                            crate::leanh::lean_inc(v_key_4695_);
                            crate::leanh::lean_dec(v_v_4686_);
                            v___x_4698_ = crate::leanh::lean_box(0);
                            v_isShared_4699_ = v_isSharedCheck_4706_;
                            state = 4;
                            continue;
                        }
                    }
                    1 => {
                        v_node_4707_ = crate::leanh::lean_ctor_get(v_v_4686_, 0);
                        v_isSharedCheck_4717_ = (!crate::leanh::lean_is_exclusive(v_v_4686_)) as u8;
                        if v_isSharedCheck_4717_ == 0 {
                            v___x_4709_ = v_v_4686_;
                            v_isShared_4710_ = v_isSharedCheck_4717_;
                            state = 6;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_node_4707_);
                            crate::leanh::lean_dec(v_v_4686_);
                            v___x_4709_ = crate::leanh::lean_box(0);
                            v_isShared_4710_ = v_isSharedCheck_4717_;
                            state = 6;
                            continue;
                        }
                    }
                    _ => {
                        v___x_4718_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_4718_, 0, v_x_4673_);
                        crate::leanh::lean_ctor_set(v___x_4718_, 1, v_x_4674_);
                        v___y_4690_ = v___x_4718_;
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                v___x_4691_ = lean_array_fset(v_xs_x27_4688_, v_j_4680_, v___y_4690_);
                crate::leanh::lean_dec(v_j_4680_);
                if v_isShared_4685_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4684_, 0, v___x_4691_);
                    v___x_4693_ = v___x_4684_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_4694_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4694_, 0, v___x_4691_);
                    v___x_4693_ = v_reuseFailAlloc_4694_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_4693_;
            }
            4 => {
                v___x_4700_ = lean_name_eq(v_x_4673_, v_key_4695_);
                if v___x_4700_ == 0 {
                    crate::leanh::lean_del_object(v___x_4698_);
                    v___x_4701_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(
                        v_key_4695_,
                        v_val_4696_,
                        v_x_4673_,
                        v_x_4674_,
                    );
                    v___x_4702_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_4702_, 0, v___x_4701_);
                    v___y_4690_ = v___x_4702_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_dec(v_val_4696_);
                    crate::leanh::lean_dec(v_key_4695_);
                    if v_isShared_4699_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_4698_, 1, v_x_4674_);
                        crate::leanh::lean_ctor_set(v___x_4698_, 0, v_x_4673_);
                        v___x_4704_ = v___x_4698_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_4705_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4705_, 0, v_x_4673_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4705_, 1, v_x_4674_);
                        v___x_4704_ = v_reuseFailAlloc_4705_;
                        state = 5;
                        continue;
                    }
                }
            }
            5 => {
                v___y_4690_ = v___x_4704_;
                state = 2;
                continue;
            }
            6 => {
                v___x_4711_ = lean_usize_shift_right(v_x_4671_, v___x_4676_);
                v___x_4712_ = lean_usize_add(v_x_4672_, v___x_4677_);
                v___x_4713_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__0_spec__0___redArg(v_node_4707_, v___x_4711_, v___x_4712_, v_x_4673_, v_x_4674_);
                if v_isShared_4710_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4709_, 0, v___x_4713_);
                    v___x_4715_ = v___x_4709_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_4716_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4716_, 0, v___x_4713_);
                    v___x_4715_ = v_reuseFailAlloc_4716_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                v___y_4690_ = v___x_4715_;
                state = 2;
                continue;
            }
            8 => {
                if v_isShared_4725_ == 0 {
                    v___x_4727_ = v___x_4724_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_4741_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4741_, 0, v_ks_4721_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4741_, 1, v_vs_4722_);
                    v___x_4727_ = v_reuseFailAlloc_4741_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                v_newNode_4728_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__0_spec__0_spec__1___redArg(v___x_4727_, v_x_4673_, v_x_4674_);
                v___x_4736_ = 7usize;
                v___x_4737_ = lean_usize_dec_le(v___x_4736_, v_x_4672_);
                if v___x_4737_ == 0 {
                    v___x_4738_ =
                        l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_4728_);
                    v___x_4739_ = crate::leanh::lean_unsigned_to_nat(4);
                    v___x_4740_ = lean_nat_dec_lt(v___x_4738_, v___x_4739_);
                    crate::leanh::lean_dec(v___x_4738_);
                    v___y_4730_ = v___x_4740_;
                    state = 10;
                    continue;
                } else {
                    v___y_4730_ = v___x_4737_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                if v___y_4730_ == 0 {
                    v_ks_4731_ = crate::leanh::lean_ctor_get(v_newNode_4728_, 0);
                    crate::leanh::lean_inc_ref(v_ks_4731_);
                    v_vs_4732_ = crate::leanh::lean_ctor_get(v_newNode_4728_, 1);
                    crate::leanh::lean_inc_ref(v_vs_4732_);
                    crate::leanh::lean_dec_ref(v_newNode_4728_);
                    v___x_4733_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___x_4734_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__0_spec__0___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__0_spec__0___redArg___closed__0_once), _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__0_spec__0___redArg___closed__0);
                    v___x_4735_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__0_spec__0_spec__2___redArg(v_x_4672_, v_ks_4731_, v_vs_4732_, v___x_4733_, v___x_4734_);
                    crate::leanh::lean_dec_ref(v_vs_4732_);
                    crate::leanh::lean_dec_ref(v_ks_4731_);
                    return v___x_4735_;
                } else {
                    return v_newNode_4728_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__0_spec__0_spec__2___redArg(
    mut v_depth_4743_: usize,
    mut v_keys_4744_: *mut crate::leanh::LeanObject,
    mut v_vals_4745_: *mut crate::leanh::LeanObject,
    mut v_i_4746_: *mut crate::leanh::LeanObject,
    mut v_entries_4747_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4748_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4749_: u8 = 0;
    let mut v_k_4750_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_4751_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4753_: u64 = 0;
    let mut v_h_4754_: usize = 0;
    let mut v___x_4755_: usize = 0;
    let mut v___x_4756_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4757_: usize = 0;
    let mut v___x_4758_: usize = 0;
    let mut v___x_4759_: usize = 0;
    let mut v_h_4760_: usize = 0;
    let mut v___x_4761_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4762_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4764_: u64 = 0;
    let mut v_hash_4765_: u64 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4748_ = lean_array_get_size(v_keys_4744_);
                v___x_4749_ = lean_nat_dec_lt(v_i_4746_, v___x_4748_);
                if v___x_4749_ == 0 {
                    crate::leanh::lean_dec(v_i_4746_);
                    return v_entries_4747_;
                } else {
                    v_k_4750_ = lean_array_fget_borrowed(v_keys_4744_, v_i_4746_);
                    v_v_4751_ = lean_array_fget_borrowed(v_vals_4745_, v_i_4746_);
                    if crate::leanh::lean_obj_tag(v_k_4750_) == 0 {
                        v___x_4764_ = crate::leanh::lean_uint64_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__1___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__1___redArg___closed__0_once), _init_l_Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__1___redArg___closed__0);
                        v___y_4753_ = v___x_4764_;
                        state = 1;
                        continue;
                    } else {
                        v_hash_4765_ = crate::leanh::lean_ctor_get_uint64(
                            v_k_4750_,
                            (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2) as u32,
                        );
                        v___y_4753_ = v_hash_4765_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_h_4754_ = lean_uint64_to_usize(v___y_4753_);
                v___x_4755_ = 5usize;
                v___x_4756_ = crate::leanh::lean_unsigned_to_nat(1);
                v___x_4757_ = 1usize;
                v___x_4758_ = lean_usize_sub(v_depth_4743_, v___x_4757_);
                v___x_4759_ = lean_usize_mul(v___x_4755_, v___x_4758_);
                v_h_4760_ = lean_usize_shift_right(v_h_4754_, v___x_4759_);
                v___x_4761_ = lean_nat_add(v_i_4746_, v___x_4756_);
                crate::leanh::lean_dec(v_i_4746_);
                crate::leanh::lean_inc(v_v_4751_);
                crate::leanh::lean_inc(v_k_4750_);
                v___x_4762_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__0_spec__0___redArg(v_entries_4747_, v_h_4760_, v_depth_4743_, v_k_4750_, v_v_4751_);
                v_i_4746_ = v___x_4761_;
                v_entries_4747_ = v___x_4762_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__0_spec__0_spec__2___redArg___boxed(
    mut v_depth_4766_: *mut crate::leanh::LeanObject,
    mut v_keys_4767_: *mut crate::leanh::LeanObject,
    mut v_vals_4768_: *mut crate::leanh::LeanObject,
    mut v_i_4769_: *mut crate::leanh::LeanObject,
    mut v_entries_4770_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_depth_boxed_4771_: usize = 0;
    let mut v_res_4772_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_depth_boxed_4771_ = crate::leanh::lean_unbox_usize(v_depth_4766_);
    crate::leanh::lean_dec(v_depth_4766_);
    v_res_4772_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__0_spec__0_spec__2___redArg(v_depth_boxed_4771_, v_keys_4767_, v_vals_4768_, v_i_4769_, v_entries_4770_);
    crate::leanh::lean_dec_ref(v_vals_4768_);
    crate::leanh::lean_dec_ref(v_keys_4767_);
    return v_res_4772_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__0_spec__0___redArg___boxed(
    mut v_x_4773_: *mut crate::leanh::LeanObject,
    mut v_x_4774_: *mut crate::leanh::LeanObject,
    mut v_x_4775_: *mut crate::leanh::LeanObject,
    mut v_x_4776_: *mut crate::leanh::LeanObject,
    mut v_x_4777_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_40060__boxed_4778_: usize = 0;
    let mut v_x_40061__boxed_4779_: usize = 0;
    let mut v_res_4780_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_40060__boxed_4778_ = crate::leanh::lean_unbox_usize(v_x_4774_);
    crate::leanh::lean_dec(v_x_4774_);
    v_x_40061__boxed_4779_ = crate::leanh::lean_unbox_usize(v_x_4775_);
    crate::leanh::lean_dec(v_x_4775_);
    v_res_4780_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__0_spec__0___redArg(v_x_4773_, v_x_40060__boxed_4778_, v_x_40061__boxed_4779_, v_x_4776_, v_x_4777_);
    return v_res_4780_;
}
pub unsafe fn l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__0___redArg(
    mut v_x_4781_: *mut crate::leanh::LeanObject,
    mut v_x_4782_: *mut crate::leanh::LeanObject,
    mut v_x_4783_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_4785_: u64 = 0;
    let mut v___x_4786_: usize = 0;
    let mut v___x_4787_: usize = 0;
    let mut v___x_4788_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4789_: u64 = 0;
    let mut v_hash_4790_: u64 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_4782_) == 0 {
                    v___x_4789_ = crate::leanh::lean_uint64_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__1___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__1___redArg___closed__0_once), _init_l_Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__1___redArg___closed__0);
                    v___y_4785_ = v___x_4789_;
                    state = 1;
                    continue;
                } else {
                    v_hash_4790_ = crate::leanh::lean_ctor_get_uint64(
                        v_x_4782_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2) as u32,
                    );
                    v___y_4785_ = v_hash_4790_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_4786_ = lean_uint64_to_usize(v___y_4785_);
                v___x_4787_ = 1usize;
                v___x_4788_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__0_spec__0___redArg(v_x_4781_, v___x_4786_, v___x_4787_, v_x_4782_, v_x_4783_);
                return v___x_4788_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__3_spec__5_spec__9___redArg(
    mut v_keys_4791_: *mut crate::leanh::LeanObject,
    mut v_vals_4792_: *mut crate::leanh::LeanObject,
    mut v_i_4793_: *mut crate::leanh::LeanObject,
    mut v_k_4794_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4795_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4796_: u8 = 0;
    let mut v___x_4797_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_x27_4798_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4799_: u8 = 0;
    let mut v___x_4800_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4801_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4803_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4804_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4795_ = lean_array_get_size(v_keys_4791_);
                v___x_4796_ = lean_nat_dec_lt(v_i_4793_, v___x_4795_);
                if v___x_4796_ == 0 {
                    crate::leanh::lean_dec(v_i_4793_);
                    v___x_4797_ = crate::leanh::lean_box(0);
                    return v___x_4797_;
                } else {
                    v_k_x27_4798_ = lean_array_fget_borrowed(v_keys_4791_, v_i_4793_);
                    v___x_4799_ = lean_name_eq(v_k_4794_, v_k_x27_4798_);
                    if v___x_4799_ == 0 {
                        v___x_4800_ = crate::leanh::lean_unsigned_to_nat(1);
                        v___x_4801_ = lean_nat_add(v_i_4793_, v___x_4800_);
                        crate::leanh::lean_dec(v_i_4793_);
                        v_i_4793_ = v___x_4801_;
                        state = 0;
                        continue;
                    } else {
                        v___x_4803_ = lean_array_fget_borrowed(v_vals_4792_, v_i_4793_);
                        crate::leanh::lean_dec(v_i_4793_);
                        crate::leanh::lean_inc(v___x_4803_);
                        v___x_4804_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_4804_, 0, v___x_4803_);
                        return v___x_4804_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__3_spec__5_spec__9___redArg___boxed(
    mut v_keys_4805_: *mut crate::leanh::LeanObject,
    mut v_vals_4806_: *mut crate::leanh::LeanObject,
    mut v_i_4807_: *mut crate::leanh::LeanObject,
    mut v_k_4808_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4809_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4809_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__3_spec__5_spec__9___redArg(v_keys_4805_, v_vals_4806_, v_i_4807_, v_k_4808_);
    crate::leanh::lean_dec(v_k_4808_);
    crate::leanh::lean_dec_ref(v_vals_4806_);
    crate::leanh::lean_dec_ref(v_keys_4805_);
    return v_res_4809_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__3_spec__5___redArg(
    mut v_x_4810_: *mut crate::leanh::LeanObject,
    mut v_x_4811_: usize,
    mut v_x_4812_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_es_4813_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4814_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4815_: usize = 0;
    let mut v___x_4816_: usize = 0;
    let mut v___x_4817_: usize = 0;
    let mut v_j_4818_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4819_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_key_4820_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_4821_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4822_: u8 = 0;
    let mut v___x_4823_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4824_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_node_4825_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4826_: usize = 0;
    let mut v___x_4828_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ks_4829_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_vs_4830_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4831_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4832_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_4810_) == 0 {
                    v_es_4813_ = crate::leanh::lean_ctor_get(v_x_4810_, 0);
                    v___x_4814_ = crate::leanh::lean_box(2);
                    v___x_4815_ = 5usize;
                    v___x_4816_ = crate::leanh::lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__1_spec__2___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__1_spec__2___redArg___closed__1_once), _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__1_spec__2___redArg___closed__1);
                    v___x_4817_ = lean_usize_land(v_x_4811_, v___x_4816_);
                    v_j_4818_ = lean_usize_to_nat(v___x_4817_);
                    v___x_4819_ = lean_array_get_borrowed(v___x_4814_, v_es_4813_, v_j_4818_);
                    crate::leanh::lean_dec(v_j_4818_);
                    match crate::leanh::lean_obj_tag(v___x_4819_) {
                        0 => {
                            v_key_4820_ = crate::leanh::lean_ctor_get(v___x_4819_, 0);
                            v_val_4821_ = crate::leanh::lean_ctor_get(v___x_4819_, 1);
                            v___x_4822_ = lean_name_eq(v_x_4812_, v_key_4820_);
                            if v___x_4822_ == 0 {
                                v___x_4823_ = crate::leanh::lean_box(0);
                                return v___x_4823_;
                            } else {
                                crate::leanh::lean_inc(v_val_4821_);
                                v___x_4824_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                                crate::leanh::lean_ctor_set(v___x_4824_, 0, v_val_4821_);
                                return v___x_4824_;
                            }
                        }
                        1 => {
                            v_node_4825_ = crate::leanh::lean_ctor_get(v___x_4819_, 0);
                            v___x_4826_ = lean_usize_shift_right(v_x_4811_, v___x_4815_);
                            v_x_4810_ = v_node_4825_;
                            v_x_4811_ = v___x_4826_;
                            state = 0;
                            continue;
                        }
                        _ => {
                            v___x_4828_ = crate::leanh::lean_box(0);
                            return v___x_4828_;
                        }
                    }
                } else {
                    v_ks_4829_ = crate::leanh::lean_ctor_get(v_x_4810_, 0);
                    v_vs_4830_ = crate::leanh::lean_ctor_get(v_x_4810_, 1);
                    v___x_4831_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___x_4832_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__3_spec__5_spec__9___redArg(v_ks_4829_, v_vs_4830_, v___x_4831_, v_x_4812_);
                    return v___x_4832_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__3_spec__5___redArg___boxed(
    mut v_x_4833_: *mut crate::leanh::LeanObject,
    mut v_x_4834_: *mut crate::leanh::LeanObject,
    mut v_x_4835_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_40263__boxed_4836_: usize = 0;
    let mut v_res_4837_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_40263__boxed_4836_ = crate::leanh::lean_unbox_usize(v_x_4834_);
    crate::leanh::lean_dec(v_x_4834_);
    v_res_4837_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__3_spec__5___redArg(v_x_4833_, v_x_40263__boxed_4836_, v_x_4835_);
    crate::leanh::lean_dec(v_x_4835_);
    crate::leanh::lean_dec_ref(v_x_4833_);
    return v_res_4837_;
}
pub unsafe fn l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__3___redArg(
    mut v_x_4838_: *mut crate::leanh::LeanObject,
    mut v_x_4839_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_4841_: u64 = 0;
    let mut v___x_4842_: usize = 0;
    let mut v___x_4843_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4844_: u64 = 0;
    let mut v_hash_4845_: u64 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_4839_) == 0 {
                    v___x_4844_ = crate::leanh::lean_uint64_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__1___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__1___redArg___closed__0_once), _init_l_Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__1___redArg___closed__0);
                    v___y_4841_ = v___x_4844_;
                    state = 1;
                    continue;
                } else {
                    v_hash_4845_ = crate::leanh::lean_ctor_get_uint64(
                        v_x_4839_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2) as u32,
                    );
                    v___y_4841_ = v_hash_4845_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_4842_ = lean_uint64_to_usize(v___y_4841_);
                v___x_4843_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__3_spec__5___redArg(v_x_4838_, v___x_4842_, v_x_4839_);
                return v___x_4843_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__3___redArg___boxed(
    mut v_x_4846_: *mut crate::leanh::LeanObject,
    mut v_x_4847_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4848_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4848_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__3___redArg(v_x_4846_, v_x_4847_);
    crate::leanh::lean_dec(v_x_4847_);
    crate::leanh::lean_dec_ref(v_x_4846_);
    return v_res_4848_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName(
    mut v_name_4852_: *mut crate::leanh::LeanObject,
    mut v_type_4853_: *mut crate::leanh::LeanObject,
    mut v_a_4854_: *mut crate::leanh::LeanObject,
    mut v_a_4855_: *mut crate::leanh::LeanObject,
    mut v_a_4856_: *mut crate::leanh::LeanObject,
    mut v_a_4857_: *mut crate::leanh::LeanObject,
    mut v_a_4858_: *mut crate::leanh::LeanObject,
    mut v_a_4859_: *mut crate::leanh::LeanObject,
    mut v_a_4860_: *mut crate::leanh::LeanObject,
    mut v_a_4861_: *mut crate::leanh::LeanObject,
    mut v_a_4862_: *mut crate::leanh::LeanObject,
    mut v_a_4863_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_name_4866_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4867_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4868_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toGoalState_4869_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_clean_4870_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mvarId_4871_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4873_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4874_: u8 = 0;
    let mut v_nextDeclIdx_4875_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_enodeMap_4876_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_exprs_4877_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_parents_4878_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_congrTable_4879_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_appMap_4880_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_indicesFound_4881_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_newFacts_4882_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_inconsistent_4883_: u8 = 0;
    let mut v_nextIdx_4884_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_newRawFacts_4885_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_facts_4886_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_extThms_4887_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ematch_4888_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_inj_4889_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_split_4890_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sstates_4891_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4893_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4894_: u8 = 0;
    let mut v_used_4895_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_next_4896_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4898_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4899_: u8 = 0;
    let mut v___x_4900_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4901_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4903_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4905_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4907_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4908_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4909_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4910_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4911_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4912_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4913_: u8 = 0;
    let mut v_isSharedCheck_4914_: u8 = 0;
    let mut v_unused_4915_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4916_: u8 = 0;
    let mut v_unused_4917_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4919_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4920_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4921_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4922_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4923_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4924_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4925_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4926_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4927_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4928_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4929_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4930_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4931_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4932_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4933_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4934_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4935_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toGoalState_4936_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_clean_4937_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_4938_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_4939_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mvarId_4940_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4942_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4943_: u8 = 0;
    let mut v_nextDeclIdx_4944_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_enodeMap_4945_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_exprs_4946_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_parents_4947_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_congrTable_4948_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_appMap_4949_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_indicesFound_4950_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_newFacts_4951_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_inconsistent_4952_: u8 = 0;
    let mut v_nextIdx_4953_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_newRawFacts_4954_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_facts_4955_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_extThms_4956_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ematch_4957_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_inj_4958_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_split_4959_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sstates_4960_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4962_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4963_: u8 = 0;
    let mut v_used_4964_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_next_4965_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4967_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4968_: u8 = 0;
    let mut v___x_4969_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4971_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4973_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4975_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4976_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4977_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4978_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4979_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4980_: u8 = 0;
    let mut v_isSharedCheck_4981_: u8 = 0;
    let mut v_unused_4982_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4983_: u8 = 0;
    let mut v_unused_4984_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4985_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4987_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4988_: u8 = 0;
    let mut v___x_4990_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4991_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4992_: u8 = 0;
    let mut v_name_4994_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4995_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4996_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4997_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4998_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4999_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5000_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5001_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5002_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5003_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5004_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5005_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toGoalState_5006_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_clean_5007_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_used_5008_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5009_: u8 = 0;
    let mut v___x_5010_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5011_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5012_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toGoalState_5013_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_clean_5014_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_next_5015_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5016_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_5017_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5018_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5019_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5020_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5022_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5023_: u8 = 0;
    let mut v___x_5025_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5026_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5028_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5029_: u8 = 0;
    let mut v___x_5030_: u8 = 0;
    let mut v___x_5032_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5033_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5034_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5035_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5036_: u8 = 0;
    let mut v_a_5037_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5039_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5040_: u8 = 0;
    let mut v___x_5042_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5043_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5044_: u8 = 0;
    let mut v_clean_5045_: u8 = 0;
    let mut v___x_5046_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_5047_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5049_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5050_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5051_: u8 = 0;
    let mut v___x_5052_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5053_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5054_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5055_: u8 = 0;
    let mut v___x_5056_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5057_: u8 = 0;
    let mut v___x_5059_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5060_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5061_: u8 = 0;
    let mut v___x_5062_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5064_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5065_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5066_: u8 = 0;
    let mut v___x_5067_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5068_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5070_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5071_: u8 = 0;
    let mut v___x_5073_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5074_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5075_: u8 = 0;
    let mut v___x_5076_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5077_: u8 = 0;
    let mut v___x_5078_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5079_: u8 = 0;
    let mut v_isSharedCheck_5080_: u8 = 0;
    let mut v_a_5081_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5083_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5084_: u8 = 0;
    let mut v___x_5086_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5087_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5088_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5019_ = l_Lean_Meta_Grind_getConfig___redArg(v_a_4856_);
                if crate::leanh::lean_obj_tag(v___x_5019_) == 0 {
                    v_a_5020_ = crate::leanh::lean_ctor_get(v___x_5019_, 0);
                    v_isSharedCheck_5080_ = (!crate::leanh::lean_is_exclusive(v___x_5019_)) as u8;
                    if v_isSharedCheck_5080_ == 0 {
                        v___x_5022_ = v___x_5019_;
                        v_isShared_5023_ = v_isSharedCheck_5080_;
                        state = 18;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_5020_);
                        crate::leanh::lean_dec(v___x_5019_);
                        v___x_5022_ = crate::leanh::lean_box(0);
                        v_isShared_5023_ = v_isSharedCheck_5080_;
                        state = 18;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_type_4853_);
                    crate::leanh::lean_dec(v_name_4852_);
                    v_a_5081_ = crate::leanh::lean_ctor_get(v___x_5019_, 0);
                    v_isSharedCheck_5088_ = (!crate::leanh::lean_is_exclusive(v___x_5019_)) as u8;
                    if v_isSharedCheck_5088_ == 0 {
                        v___x_5083_ = v___x_5019_;
                        v_isShared_5084_ = v_isSharedCheck_5088_;
                        state = 29;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_5081_);
                        crate::leanh::lean_dec(v___x_5019_);
                        v___x_5083_ = crate::leanh::lean_box(0);
                        v_isShared_5084_ = v_isSharedCheck_5088_;
                        state = 29;
                        continue;
                    }
                }
            }
            1 => {
                v___x_4868_ = lean_st_ref_take(v___y_4867_);
                v_toGoalState_4869_ = crate::leanh::lean_ctor_get(v___x_4868_, 0);
                crate::leanh::lean_inc_ref(v_toGoalState_4869_);
                v_clean_4870_ = crate::leanh::lean_ctor_get(v_toGoalState_4869_, 15);
                crate::leanh::lean_inc_ref(v_clean_4870_);
                v_mvarId_4871_ = crate::leanh::lean_ctor_get(v___x_4868_, 1);
                v_isSharedCheck_4916_ = (!crate::leanh::lean_is_exclusive(v___x_4868_)) as u8;
                if v_isSharedCheck_4916_ == 0 {
                    v_unused_4917_ = crate::leanh::lean_ctor_get(v___x_4868_, 0);
                    crate::leanh::lean_dec(v_unused_4917_);
                    v___x_4873_ = v___x_4868_;
                    v_isShared_4874_ = v_isSharedCheck_4916_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_mvarId_4871_);
                    crate::leanh::lean_dec(v___x_4868_);
                    v___x_4873_ = crate::leanh::lean_box(0);
                    v_isShared_4874_ = v_isSharedCheck_4916_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_nextDeclIdx_4875_ = crate::leanh::lean_ctor_get(v_toGoalState_4869_, 0);
                v_enodeMap_4876_ = crate::leanh::lean_ctor_get(v_toGoalState_4869_, 1);
                v_exprs_4877_ = crate::leanh::lean_ctor_get(v_toGoalState_4869_, 2);
                v_parents_4878_ = crate::leanh::lean_ctor_get(v_toGoalState_4869_, 3);
                v_congrTable_4879_ = crate::leanh::lean_ctor_get(v_toGoalState_4869_, 4);
                v_appMap_4880_ = crate::leanh::lean_ctor_get(v_toGoalState_4869_, 5);
                v_indicesFound_4881_ = crate::leanh::lean_ctor_get(v_toGoalState_4869_, 6);
                v_newFacts_4882_ = crate::leanh::lean_ctor_get(v_toGoalState_4869_, 7);
                v_inconsistent_4883_ = crate::leanh::lean_ctor_get_uint8(
                    v_toGoalState_4869_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 17) as u32,
                );
                v_nextIdx_4884_ = crate::leanh::lean_ctor_get(v_toGoalState_4869_, 8);
                v_newRawFacts_4885_ = crate::leanh::lean_ctor_get(v_toGoalState_4869_, 9);
                v_facts_4886_ = crate::leanh::lean_ctor_get(v_toGoalState_4869_, 10);
                v_extThms_4887_ = crate::leanh::lean_ctor_get(v_toGoalState_4869_, 11);
                v_ematch_4888_ = crate::leanh::lean_ctor_get(v_toGoalState_4869_, 12);
                v_inj_4889_ = crate::leanh::lean_ctor_get(v_toGoalState_4869_, 13);
                v_split_4890_ = crate::leanh::lean_ctor_get(v_toGoalState_4869_, 14);
                v_sstates_4891_ = crate::leanh::lean_ctor_get(v_toGoalState_4869_, 16);
                v_isSharedCheck_4914_ =
                    (!crate::leanh::lean_is_exclusive(v_toGoalState_4869_)) as u8;
                if v_isSharedCheck_4914_ == 0 {
                    v_unused_4915_ = crate::leanh::lean_ctor_get(v_toGoalState_4869_, 15);
                    crate::leanh::lean_dec(v_unused_4915_);
                    v___x_4893_ = v_toGoalState_4869_;
                    v_isShared_4894_ = v_isSharedCheck_4914_;
                    state = 3;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_sstates_4891_);
                    crate::leanh::lean_inc(v_split_4890_);
                    crate::leanh::lean_inc(v_inj_4889_);
                    crate::leanh::lean_inc(v_ematch_4888_);
                    crate::leanh::lean_inc(v_extThms_4887_);
                    crate::leanh::lean_inc(v_facts_4886_);
                    crate::leanh::lean_inc(v_newRawFacts_4885_);
                    crate::leanh::lean_inc(v_nextIdx_4884_);
                    crate::leanh::lean_inc(v_newFacts_4882_);
                    crate::leanh::lean_inc(v_indicesFound_4881_);
                    crate::leanh::lean_inc(v_appMap_4880_);
                    crate::leanh::lean_inc(v_congrTable_4879_);
                    crate::leanh::lean_inc(v_parents_4878_);
                    crate::leanh::lean_inc(v_exprs_4877_);
                    crate::leanh::lean_inc(v_enodeMap_4876_);
                    crate::leanh::lean_inc(v_nextDeclIdx_4875_);
                    crate::leanh::lean_dec(v_toGoalState_4869_);
                    v___x_4893_ = crate::leanh::lean_box(0);
                    v_isShared_4894_ = v_isSharedCheck_4914_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v_used_4895_ = crate::leanh::lean_ctor_get(v_clean_4870_, 0);
                v_next_4896_ = crate::leanh::lean_ctor_get(v_clean_4870_, 1);
                v_isSharedCheck_4913_ = (!crate::leanh::lean_is_exclusive(v_clean_4870_)) as u8;
                if v_isSharedCheck_4913_ == 0 {
                    v___x_4898_ = v_clean_4870_;
                    v_isShared_4899_ = v_isSharedCheck_4913_;
                    state = 4;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_next_4896_);
                    crate::leanh::lean_inc(v_used_4895_);
                    crate::leanh::lean_dec(v_clean_4870_);
                    v___x_4898_ = crate::leanh::lean_box(0);
                    v_isShared_4899_ = v_isSharedCheck_4913_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_4900_ = crate::leanh::lean_box(0);
                crate::leanh::lean_inc(v_name_4866_);
                v___x_4901_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__0___redArg(v_used_4895_, v_name_4866_, v___x_4900_);
                if v_isShared_4899_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4898_, 0, v___x_4901_);
                    v___x_4903_ = v___x_4898_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_4912_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4912_, 0, v___x_4901_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4912_, 1, v_next_4896_);
                    v___x_4903_ = v_reuseFailAlloc_4912_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                if v_isShared_4894_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4893_, 15, v___x_4903_);
                    v___x_4905_ = v___x_4893_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_4911_ = crate::leanh::lean_alloc_ctor(0, 17, (1) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4911_, 0, v_nextDeclIdx_4875_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4911_, 1, v_enodeMap_4876_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4911_, 2, v_exprs_4877_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4911_, 3, v_parents_4878_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4911_, 4, v_congrTable_4879_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4911_, 5, v_appMap_4880_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4911_, 6, v_indicesFound_4881_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4911_, 7, v_newFacts_4882_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4911_, 8, v_nextIdx_4884_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4911_, 9, v_newRawFacts_4885_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4911_, 10, v_facts_4886_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4911_, 11, v_extThms_4887_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4911_, 12, v_ematch_4888_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4911_, 13, v_inj_4889_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4911_, 14, v_split_4890_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4911_, 15, v___x_4903_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4911_, 16, v_sstates_4891_);
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_4911_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 17) as u32,
                        v_inconsistent_4883_,
                    );
                    v___x_4905_ = v_reuseFailAlloc_4911_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                if v_isShared_4874_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4873_, 0, v___x_4905_);
                    v___x_4907_ = v___x_4873_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_4910_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4910_, 0, v___x_4905_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4910_, 1, v_mvarId_4871_);
                    v___x_4907_ = v_reuseFailAlloc_4910_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                v___x_4908_ = lean_st_ref_set(v___y_4867_, v___x_4907_);
                v___x_4909_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4909_, 0, v_name_4866_);
                return v___x_4909_;
            }
            8 => {
                v___x_4932_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4932_, 0, v___y_4920_);
                crate::leanh::lean_ctor_set(v___x_4932_, 1, v___y_4931_);
                crate::leanh::lean_inc(v___y_4925_);
                v___x_4933_ = l___private_Init_While_0__whileM_erased___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__2___redArg(v___y_4925_, v___x_4932_, v___y_4921_);
                if crate::leanh::lean_obj_tag(v___x_4933_) == 0 {
                    v_a_4934_ = crate::leanh::lean_ctor_get(v___x_4933_, 0);
                    crate::leanh::lean_inc(v_a_4934_);
                    crate::leanh::lean_dec_ref_known(v___x_4933_, 1);
                    v___x_4935_ = lean_st_ref_take(v___y_4921_);
                    v_toGoalState_4936_ = crate::leanh::lean_ctor_get(v___x_4935_, 0);
                    crate::leanh::lean_inc_ref(v_toGoalState_4936_);
                    v_clean_4937_ = crate::leanh::lean_ctor_get(v_toGoalState_4936_, 15);
                    crate::leanh::lean_inc_ref(v_clean_4937_);
                    v_fst_4938_ = crate::leanh::lean_ctor_get(v_a_4934_, 0);
                    crate::leanh::lean_inc(v_fst_4938_);
                    v_snd_4939_ = crate::leanh::lean_ctor_get(v_a_4934_, 1);
                    crate::leanh::lean_inc(v_snd_4939_);
                    crate::leanh::lean_dec(v_a_4934_);
                    v_mvarId_4940_ = crate::leanh::lean_ctor_get(v___x_4935_, 1);
                    v_isSharedCheck_4983_ = (!crate::leanh::lean_is_exclusive(v___x_4935_)) as u8;
                    if v_isSharedCheck_4983_ == 0 {
                        v_unused_4984_ = crate::leanh::lean_ctor_get(v___x_4935_, 0);
                        crate::leanh::lean_dec(v_unused_4984_);
                        v___x_4942_ = v___x_4935_;
                        v_isShared_4943_ = v_isSharedCheck_4983_;
                        state = 9;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_mvarId_4940_);
                        crate::leanh::lean_dec(v___x_4935_);
                        v___x_4942_ = crate::leanh::lean_box(0);
                        v_isShared_4943_ = v_isSharedCheck_4983_;
                        state = 9;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v___y_4925_);
                    v_a_4985_ = crate::leanh::lean_ctor_get(v___x_4933_, 0);
                    v_isSharedCheck_4992_ = (!crate::leanh::lean_is_exclusive(v___x_4933_)) as u8;
                    if v_isSharedCheck_4992_ == 0 {
                        v___x_4987_ = v___x_4933_;
                        v_isShared_4988_ = v_isSharedCheck_4992_;
                        state = 15;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4985_);
                        crate::leanh::lean_dec(v___x_4933_);
                        v___x_4987_ = crate::leanh::lean_box(0);
                        v_isShared_4988_ = v_isSharedCheck_4992_;
                        state = 15;
                        continue;
                    }
                }
            }
            9 => {
                v_nextDeclIdx_4944_ = crate::leanh::lean_ctor_get(v_toGoalState_4936_, 0);
                v_enodeMap_4945_ = crate::leanh::lean_ctor_get(v_toGoalState_4936_, 1);
                v_exprs_4946_ = crate::leanh::lean_ctor_get(v_toGoalState_4936_, 2);
                v_parents_4947_ = crate::leanh::lean_ctor_get(v_toGoalState_4936_, 3);
                v_congrTable_4948_ = crate::leanh::lean_ctor_get(v_toGoalState_4936_, 4);
                v_appMap_4949_ = crate::leanh::lean_ctor_get(v_toGoalState_4936_, 5);
                v_indicesFound_4950_ = crate::leanh::lean_ctor_get(v_toGoalState_4936_, 6);
                v_newFacts_4951_ = crate::leanh::lean_ctor_get(v_toGoalState_4936_, 7);
                v_inconsistent_4952_ = crate::leanh::lean_ctor_get_uint8(
                    v_toGoalState_4936_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 17) as u32,
                );
                v_nextIdx_4953_ = crate::leanh::lean_ctor_get(v_toGoalState_4936_, 8);
                v_newRawFacts_4954_ = crate::leanh::lean_ctor_get(v_toGoalState_4936_, 9);
                v_facts_4955_ = crate::leanh::lean_ctor_get(v_toGoalState_4936_, 10);
                v_extThms_4956_ = crate::leanh::lean_ctor_get(v_toGoalState_4936_, 11);
                v_ematch_4957_ = crate::leanh::lean_ctor_get(v_toGoalState_4936_, 12);
                v_inj_4958_ = crate::leanh::lean_ctor_get(v_toGoalState_4936_, 13);
                v_split_4959_ = crate::leanh::lean_ctor_get(v_toGoalState_4936_, 14);
                v_sstates_4960_ = crate::leanh::lean_ctor_get(v_toGoalState_4936_, 16);
                v_isSharedCheck_4981_ =
                    (!crate::leanh::lean_is_exclusive(v_toGoalState_4936_)) as u8;
                if v_isSharedCheck_4981_ == 0 {
                    v_unused_4982_ = crate::leanh::lean_ctor_get(v_toGoalState_4936_, 15);
                    crate::leanh::lean_dec(v_unused_4982_);
                    v___x_4962_ = v_toGoalState_4936_;
                    v_isShared_4963_ = v_isSharedCheck_4981_;
                    state = 10;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_sstates_4960_);
                    crate::leanh::lean_inc(v_split_4959_);
                    crate::leanh::lean_inc(v_inj_4958_);
                    crate::leanh::lean_inc(v_ematch_4957_);
                    crate::leanh::lean_inc(v_extThms_4956_);
                    crate::leanh::lean_inc(v_facts_4955_);
                    crate::leanh::lean_inc(v_newRawFacts_4954_);
                    crate::leanh::lean_inc(v_nextIdx_4953_);
                    crate::leanh::lean_inc(v_newFacts_4951_);
                    crate::leanh::lean_inc(v_indicesFound_4950_);
                    crate::leanh::lean_inc(v_appMap_4949_);
                    crate::leanh::lean_inc(v_congrTable_4948_);
                    crate::leanh::lean_inc(v_parents_4947_);
                    crate::leanh::lean_inc(v_exprs_4946_);
                    crate::leanh::lean_inc(v_enodeMap_4945_);
                    crate::leanh::lean_inc(v_nextDeclIdx_4944_);
                    crate::leanh::lean_dec(v_toGoalState_4936_);
                    v___x_4962_ = crate::leanh::lean_box(0);
                    v_isShared_4963_ = v_isSharedCheck_4981_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                v_used_4964_ = crate::leanh::lean_ctor_get(v_clean_4937_, 0);
                v_next_4965_ = crate::leanh::lean_ctor_get(v_clean_4937_, 1);
                v_isSharedCheck_4980_ = (!crate::leanh::lean_is_exclusive(v_clean_4937_)) as u8;
                if v_isSharedCheck_4980_ == 0 {
                    v___x_4967_ = v_clean_4937_;
                    v_isShared_4968_ = v_isSharedCheck_4980_;
                    state = 11;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_next_4965_);
                    crate::leanh::lean_inc(v_used_4964_);
                    crate::leanh::lean_dec(v_clean_4937_);
                    v___x_4967_ = crate::leanh::lean_box(0);
                    v_isShared_4968_ = v_isSharedCheck_4980_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                v___x_4969_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__0___redArg(v_next_4965_, v___y_4925_, v_snd_4939_);
                if v_isShared_4968_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4967_, 1, v___x_4969_);
                    v___x_4971_ = v___x_4967_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_4979_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4979_, 0, v_used_4964_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4979_, 1, v___x_4969_);
                    v___x_4971_ = v_reuseFailAlloc_4979_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                if v_isShared_4963_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4962_, 15, v___x_4971_);
                    v___x_4973_ = v___x_4962_;
                    state = 13;
                    continue;
                } else {
                    v_reuseFailAlloc_4978_ = crate::leanh::lean_alloc_ctor(0, 17, (1) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4978_, 0, v_nextDeclIdx_4944_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4978_, 1, v_enodeMap_4945_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4978_, 2, v_exprs_4946_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4978_, 3, v_parents_4947_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4978_, 4, v_congrTable_4948_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4978_, 5, v_appMap_4949_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4978_, 6, v_indicesFound_4950_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4978_, 7, v_newFacts_4951_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4978_, 8, v_nextIdx_4953_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4978_, 9, v_newRawFacts_4954_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4978_, 10, v_facts_4955_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4978_, 11, v_extThms_4956_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4978_, 12, v_ematch_4957_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4978_, 13, v_inj_4958_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4978_, 14, v_split_4959_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4978_, 15, v___x_4971_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4978_, 16, v_sstates_4960_);
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_4978_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 17) as u32,
                        v_inconsistent_4952_,
                    );
                    v___x_4973_ = v_reuseFailAlloc_4978_;
                    state = 13;
                    continue;
                }
            }
            13 => {
                if v_isShared_4943_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4942_, 0, v___x_4973_);
                    v___x_4975_ = v___x_4942_;
                    state = 14;
                    continue;
                } else {
                    v_reuseFailAlloc_4977_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4977_, 0, v___x_4973_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4977_, 1, v_mvarId_4940_);
                    v___x_4975_ = v_reuseFailAlloc_4977_;
                    state = 14;
                    continue;
                }
            }
            14 => {
                v___x_4976_ = lean_st_ref_set(v___y_4921_, v___x_4975_);
                v_name_4866_ = v_fst_4938_;
                v___y_4867_ = v___y_4921_;
                state = 1;
                continue;
            }
            15 => {
                if v_isShared_4988_ == 0 {
                    v___x_4990_ = v___x_4987_;
                    state = 16;
                    continue;
                } else {
                    v_reuseFailAlloc_4991_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4991_, 0, v_a_4985_);
                    v___x_4990_ = v_reuseFailAlloc_4991_;
                    state = 16;
                    continue;
                }
            }
            16 => {
                return v___x_4990_;
            }
            17 => {
                v___x_5005_ = lean_st_ref_get(v___y_4995_);
                v_toGoalState_5006_ = crate::leanh::lean_ctor_get(v___x_5005_, 0);
                crate::leanh::lean_inc_ref(v_toGoalState_5006_);
                crate::leanh::lean_dec(v___x_5005_);
                v_clean_5007_ = crate::leanh::lean_ctor_get(v_toGoalState_5006_, 15);
                crate::leanh::lean_inc_ref(v_clean_5007_);
                crate::leanh::lean_dec_ref(v_toGoalState_5006_);
                v_used_5008_ = crate::leanh::lean_ctor_get(v_clean_5007_, 0);
                crate::leanh::lean_inc_ref(v_used_5008_);
                crate::leanh::lean_dec_ref(v_clean_5007_);
                v___x_5009_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__1___redArg(v_used_5008_, v_name_4994_);
                crate::leanh::lean_dec_ref(v_used_5008_);
                if v___x_5009_ == 0 {
                    crate::leanh::lean_dec_ref(v_type_4853_);
                    v_name_4866_ = v_name_4994_;
                    v___y_4867_ = v___y_4995_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_name_4994_);
                    v___x_5010_ =
                        l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkBaseName(
                            v_name_4994_,
                            v_type_4853_,
                            v___y_5001_,
                            v___y_5002_,
                            v___y_5003_,
                            v___y_5004_,
                        );
                    if crate::leanh::lean_obj_tag(v___x_5010_) == 0 {
                        v_a_5011_ = crate::leanh::lean_ctor_get(v___x_5010_, 0);
                        crate::leanh::lean_inc(v_a_5011_);
                        crate::leanh::lean_dec_ref_known(v___x_5010_, 1);
                        v___x_5012_ = lean_st_ref_get(v___y_4995_);
                        v_toGoalState_5013_ = crate::leanh::lean_ctor_get(v___x_5012_, 0);
                        crate::leanh::lean_inc_ref(v_toGoalState_5013_);
                        crate::leanh::lean_dec(v___x_5012_);
                        v_clean_5014_ = crate::leanh::lean_ctor_get(v_toGoalState_5013_, 15);
                        crate::leanh::lean_inc_ref(v_clean_5014_);
                        crate::leanh::lean_dec_ref(v_toGoalState_5013_);
                        v_next_5015_ = crate::leanh::lean_ctor_get(v_clean_5014_, 1);
                        crate::leanh::lean_inc_ref(v_next_5015_);
                        crate::leanh::lean_dec_ref(v_clean_5014_);
                        v___x_5016_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__3___redArg(v_next_5015_, v_a_5011_);
                        crate::leanh::lean_dec_ref(v_next_5015_);
                        if crate::leanh::lean_obj_tag(v___x_5016_) == 1 {
                            v_val_5017_ = crate::leanh::lean_ctor_get(v___x_5016_, 0);
                            crate::leanh::lean_inc(v_val_5017_);
                            crate::leanh::lean_dec_ref_known(v___x_5016_, 1);
                            v___y_4919_ = v___y_4999_;
                            v___y_4920_ = v_name_4994_;
                            v___y_4921_ = v___y_4995_;
                            v___y_4922_ = v___y_4998_;
                            v___y_4923_ = v___y_5002_;
                            v___y_4924_ = v___y_5004_;
                            v___y_4925_ = v_a_5011_;
                            v___y_4926_ = v___y_5000_;
                            v___y_4927_ = v___y_5003_;
                            v___y_4928_ = v___y_4996_;
                            v___y_4929_ = v___y_4997_;
                            v___y_4930_ = v___y_5001_;
                            v___y_4931_ = v_val_5017_;
                            state = 8;
                            continue;
                        } else {
                            crate::leanh::lean_dec(v___x_5016_);
                            v___x_5018_ = crate::leanh::lean_unsigned_to_nat(1);
                            v___y_4919_ = v___y_4999_;
                            v___y_4920_ = v_name_4994_;
                            v___y_4921_ = v___y_4995_;
                            v___y_4922_ = v___y_4998_;
                            v___y_4923_ = v___y_5002_;
                            v___y_4924_ = v___y_5004_;
                            v___y_4925_ = v_a_5011_;
                            v___y_4926_ = v___y_5000_;
                            v___y_4927_ = v___y_5003_;
                            v___y_4928_ = v___y_4996_;
                            v___y_4929_ = v___y_4997_;
                            v___y_4930_ = v___y_5001_;
                            v___y_4931_ = v___x_5018_;
                            state = 8;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec(v_name_4994_);
                        return v___x_5010_;
                    }
                }
            }
            18 => {
                v_clean_5045_ = crate::leanh::lean_ctor_get_uint8(
                    v_a_5020_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 13 + 16) as u32,
                );
                crate::leanh::lean_dec(v_a_5020_);
                if v_clean_5045_ == 0 {
                    v___x_5046_ = l_Lean_Meta_Grind_getOriginalName_x3f(v_name_4852_);
                    if crate::leanh::lean_obj_tag(v___x_5046_) == 1 {
                        crate::leanh::lean_dec_ref(v_type_4853_);
                        crate::leanh::lean_dec(v_name_4852_);
                        v_val_5047_ = crate::leanh::lean_ctor_get(v___x_5046_, 0);
                        crate::leanh::lean_inc(v_val_5047_);
                        crate::leanh::lean_dec_ref_known(v___x_5046_, 1);
                        if v_isShared_5023_ == 0 {
                            crate::leanh::lean_ctor_set(v___x_5022_, 0, v_val_5047_);
                            v___x_5049_ = v___x_5022_;
                            state = 24;
                            continue;
                        } else {
                            v_reuseFailAlloc_5050_ =
                                crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_5050_, 0, v_val_5047_);
                            v___x_5049_ = v_reuseFailAlloc_5050_;
                            state = 24;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec(v___x_5046_);
                        v___x_5051_ = l_Lean_Name_hasMacroScopes(v_name_4852_);
                        if v___x_5051_ == 0 {
                            crate::leanh::lean_del_object(v___x_5022_);
                            crate::leanh::lean_dec_ref(v_type_4853_);
                            v___x_5052_ =
                                l_Lean_Core_mkFreshUserName(v_name_4852_, v_a_4862_, v_a_4863_);
                            return v___x_5052_;
                        } else {
                            crate::leanh::lean_inc(v_name_4852_);
                            v___x_5053_ = lean_erase_macro_scopes(v_name_4852_);
                            v___x_5054_ = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkBaseName___closed__1;
                            v___x_5055_ = lean_name_eq(v___x_5053_, v___x_5054_);
                            if v___x_5055_ == 0 {
                                v___x_5056_ = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName___closed__1;
                                v___x_5057_ = lean_name_eq(v___x_5053_, v___x_5056_);
                                crate::leanh::lean_dec(v___x_5053_);
                                if v___x_5057_ == 0 {
                                    crate::leanh::lean_dec_ref(v_type_4853_);
                                    if v_isShared_5023_ == 0 {
                                        crate::leanh::lean_ctor_set(v___x_5022_, 0, v_name_4852_);
                                        v___x_5059_ = v___x_5022_;
                                        state = 25;
                                        continue;
                                    } else {
                                        v_reuseFailAlloc_5060_ =
                                            crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                                        crate::leanh::lean_ctor_set(
                                            v_reuseFailAlloc_5060_,
                                            0,
                                            v_name_4852_,
                                        );
                                        v___x_5059_ = v_reuseFailAlloc_5060_;
                                        state = 25;
                                        continue;
                                    }
                                } else {
                                    crate::leanh::lean_del_object(v___x_5022_);
                                    state = 19;
                                    continue;
                                }
                            } else {
                                crate::leanh::lean_dec(v___x_5053_);
                                crate::leanh::lean_del_object(v___x_5022_);
                                state = 19;
                                continue;
                            }
                        }
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_5022_);
                    v___x_5061_ = l_Lean_Name_hasMacroScopes(v_name_4852_);
                    if v___x_5061_ == 0 {
                        v_name_4994_ = v_name_4852_;
                        v___y_4995_ = v_a_4854_;
                        v___y_4996_ = v_a_4855_;
                        v___y_4997_ = v_a_4856_;
                        v___y_4998_ = v_a_4857_;
                        v___y_4999_ = v_a_4858_;
                        v___y_5000_ = v_a_4859_;
                        v___y_5001_ = v_a_4860_;
                        v___y_5002_ = v_a_4861_;
                        v___y_5003_ = v_a_4862_;
                        v___y_5004_ = v_a_4863_;
                        state = 17;
                        continue;
                    } else {
                        v___x_5062_ = lean_erase_macro_scopes(v_name_4852_);
                        v___x_5076_ = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkBaseName___closed__1;
                        v___x_5077_ = lean_name_eq(v___x_5062_, v___x_5076_);
                        if v___x_5077_ == 0 {
                            v___x_5078_ = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName___closed__1;
                            v___x_5079_ = lean_name_eq(v___x_5062_, v___x_5078_);
                            if v___x_5079_ == 0 {
                                v_name_4994_ = v___x_5062_;
                                v___y_4995_ = v_a_4854_;
                                v___y_4996_ = v_a_4855_;
                                v___y_4997_ = v_a_4856_;
                                v___y_4998_ = v_a_4857_;
                                v___y_4999_ = v_a_4858_;
                                v___y_5000_ = v_a_4859_;
                                v___y_5001_ = v_a_4860_;
                                v___y_5002_ = v_a_4861_;
                                v___y_5003_ = v_a_4862_;
                                v___y_5004_ = v_a_4863_;
                                state = 17;
                                continue;
                            } else {
                                state = 26;
                                continue;
                            }
                        } else {
                            state = 26;
                            continue;
                        }
                    }
                }
            }
            19 => {
                v___x_5025_ =
                    l_Lean_Meta_isProp(v_type_4853_, v_a_4860_, v_a_4861_, v_a_4862_, v_a_4863_);
                if crate::leanh::lean_obj_tag(v___x_5025_) == 0 {
                    v_a_5026_ = crate::leanh::lean_ctor_get(v___x_5025_, 0);
                    v_isSharedCheck_5036_ = (!crate::leanh::lean_is_exclusive(v___x_5025_)) as u8;
                    if v_isSharedCheck_5036_ == 0 {
                        v___x_5028_ = v___x_5025_;
                        v_isShared_5029_ = v_isSharedCheck_5036_;
                        state = 20;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_5026_);
                        crate::leanh::lean_dec(v___x_5025_);
                        v___x_5028_ = crate::leanh::lean_box(0);
                        v_isShared_5029_ = v_isSharedCheck_5036_;
                        state = 20;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_name_4852_);
                    v_a_5037_ = crate::leanh::lean_ctor_get(v___x_5025_, 0);
                    v_isSharedCheck_5044_ = (!crate::leanh::lean_is_exclusive(v___x_5025_)) as u8;
                    if v_isSharedCheck_5044_ == 0 {
                        v___x_5039_ = v___x_5025_;
                        v_isShared_5040_ = v_isSharedCheck_5044_;
                        state = 22;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_5037_);
                        crate::leanh::lean_dec(v___x_5025_);
                        v___x_5039_ = crate::leanh::lean_box(0);
                        v_isShared_5040_ = v_isSharedCheck_5044_;
                        state = 22;
                        continue;
                    }
                }
            }
            20 => {
                v___x_5030_ = (crate::leanh::lean_unbox(v_a_5026_) as u8);
                crate::leanh::lean_dec(v_a_5026_);
                if v___x_5030_ == 0 {
                    if v_isShared_5029_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_5028_, 0, v_name_4852_);
                        v___x_5032_ = v___x_5028_;
                        state = 21;
                        continue;
                    } else {
                        v_reuseFailAlloc_5033_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_5033_, 0, v_name_4852_);
                        v___x_5032_ = v_reuseFailAlloc_5033_;
                        state = 21;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_5028_);
                    crate::leanh::lean_dec(v_name_4852_);
                    v___x_5034_ = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkBaseName___closed__3;
                    v___x_5035_ = l_Lean_Core_mkFreshUserName(v___x_5034_, v_a_4862_, v_a_4863_);
                    return v___x_5035_;
                }
            }
            21 => {
                return v___x_5032_;
            }
            22 => {
                if v_isShared_5040_ == 0 {
                    v___x_5042_ = v___x_5039_;
                    state = 23;
                    continue;
                } else {
                    v_reuseFailAlloc_5043_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5043_, 0, v_a_5037_);
                    v___x_5042_ = v_reuseFailAlloc_5043_;
                    state = 23;
                    continue;
                }
            }
            23 => {
                return v___x_5042_;
            }
            24 => {
                return v___x_5049_;
            }
            25 => {
                return v___x_5059_;
            }
            26 => {
                crate::leanh::lean_inc_ref(v_type_4853_);
                v___x_5064_ =
                    l_Lean_Meta_isProp(v_type_4853_, v_a_4860_, v_a_4861_, v_a_4862_, v_a_4863_);
                if crate::leanh::lean_obj_tag(v___x_5064_) == 0 {
                    v_a_5065_ = crate::leanh::lean_ctor_get(v___x_5064_, 0);
                    crate::leanh::lean_inc(v_a_5065_);
                    crate::leanh::lean_dec_ref_known(v___x_5064_, 1);
                    v___x_5066_ = (crate::leanh::lean_unbox(v_a_5065_) as u8);
                    crate::leanh::lean_dec(v_a_5065_);
                    if v___x_5066_ == 0 {
                        v_name_4994_ = v___x_5062_;
                        v___y_4995_ = v_a_4854_;
                        v___y_4996_ = v_a_4855_;
                        v___y_4997_ = v_a_4856_;
                        v___y_4998_ = v_a_4857_;
                        v___y_4999_ = v_a_4858_;
                        v___y_5000_ = v_a_4859_;
                        v___y_5001_ = v_a_4860_;
                        v___y_5002_ = v_a_4861_;
                        v___y_5003_ = v_a_4862_;
                        v___y_5004_ = v_a_4863_;
                        state = 17;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v___x_5062_);
                        v___x_5067_ = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkBaseName___closed__3;
                        v_name_4994_ = v___x_5067_;
                        v___y_4995_ = v_a_4854_;
                        v___y_4996_ = v_a_4855_;
                        v___y_4997_ = v_a_4856_;
                        v___y_4998_ = v_a_4857_;
                        v___y_4999_ = v_a_4858_;
                        v___y_5000_ = v_a_4859_;
                        v___y_5001_ = v_a_4860_;
                        v___y_5002_ = v_a_4861_;
                        v___y_5003_ = v_a_4862_;
                        v___y_5004_ = v_a_4863_;
                        state = 17;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v___x_5062_);
                    crate::leanh::lean_dec_ref(v_type_4853_);
                    v_a_5068_ = crate::leanh::lean_ctor_get(v___x_5064_, 0);
                    v_isSharedCheck_5075_ = (!crate::leanh::lean_is_exclusive(v___x_5064_)) as u8;
                    if v_isSharedCheck_5075_ == 0 {
                        v___x_5070_ = v___x_5064_;
                        v_isShared_5071_ = v_isSharedCheck_5075_;
                        state = 27;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_5068_);
                        crate::leanh::lean_dec(v___x_5064_);
                        v___x_5070_ = crate::leanh::lean_box(0);
                        v_isShared_5071_ = v_isSharedCheck_5075_;
                        state = 27;
                        continue;
                    }
                }
            }
            27 => {
                if v_isShared_5071_ == 0 {
                    v___x_5073_ = v___x_5070_;
                    state = 28;
                    continue;
                } else {
                    v_reuseFailAlloc_5074_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5074_, 0, v_a_5068_);
                    v___x_5073_ = v_reuseFailAlloc_5074_;
                    state = 28;
                    continue;
                }
            }
            28 => {
                return v___x_5073_;
            }
            29 => {
                if v_isShared_5084_ == 0 {
                    v___x_5086_ = v___x_5083_;
                    state = 30;
                    continue;
                } else {
                    v_reuseFailAlloc_5087_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5087_, 0, v_a_5081_);
                    v___x_5086_ = v_reuseFailAlloc_5087_;
                    state = 30;
                    continue;
                }
            }
            30 => {
                return v___x_5086_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName___boxed(
    mut v_name_5089_: *mut crate::leanh::LeanObject,
    mut v_type_5090_: *mut crate::leanh::LeanObject,
    mut v_a_5091_: *mut crate::leanh::LeanObject,
    mut v_a_5092_: *mut crate::leanh::LeanObject,
    mut v_a_5093_: *mut crate::leanh::LeanObject,
    mut v_a_5094_: *mut crate::leanh::LeanObject,
    mut v_a_5095_: *mut crate::leanh::LeanObject,
    mut v_a_5096_: *mut crate::leanh::LeanObject,
    mut v_a_5097_: *mut crate::leanh::LeanObject,
    mut v_a_5098_: *mut crate::leanh::LeanObject,
    mut v_a_5099_: *mut crate::leanh::LeanObject,
    mut v_a_5100_: *mut crate::leanh::LeanObject,
    mut v_a_5101_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5102_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5102_ = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName(
        v_name_5089_,
        v_type_5090_,
        v_a_5091_,
        v_a_5092_,
        v_a_5093_,
        v_a_5094_,
        v_a_5095_,
        v_a_5096_,
        v_a_5097_,
        v_a_5098_,
        v_a_5099_,
        v_a_5100_,
    );
    crate::leanh::lean_dec(v_a_5100_);
    crate::leanh::lean_dec_ref(v_a_5099_);
    crate::leanh::lean_dec(v_a_5098_);
    crate::leanh::lean_dec_ref(v_a_5097_);
    crate::leanh::lean_dec(v_a_5096_);
    crate::leanh::lean_dec_ref(v_a_5095_);
    crate::leanh::lean_dec(v_a_5094_);
    crate::leanh::lean_dec_ref(v_a_5093_);
    crate::leanh::lean_dec(v_a_5092_);
    crate::leanh::lean_dec(v_a_5091_);
    return v_res_5102_;
}
pub unsafe fn l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__0(
    mut v_00_u03b2_5103_: *mut crate::leanh::LeanObject,
    mut v_x_5104_: *mut crate::leanh::LeanObject,
    mut v_x_5105_: *mut crate::leanh::LeanObject,
    mut v_x_5106_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5107_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5107_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__0___redArg(v_x_5104_, v_x_5105_, v_x_5106_);
    return v___x_5107_;
}
pub unsafe fn l_Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__1(
    mut v_00_u03b2_5108_: *mut crate::leanh::LeanObject,
    mut v_x_5109_: *mut crate::leanh::LeanObject,
    mut v_x_5110_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_5111_: u8 = 0;
    v___x_5111_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__1___redArg(v_x_5109_, v_x_5110_);
    return v___x_5111_;
}
pub unsafe fn l_Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__1___boxed(
    mut v_00_u03b2_5112_: *mut crate::leanh::LeanObject,
    mut v_x_5113_: *mut crate::leanh::LeanObject,
    mut v_x_5114_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5115_: u8 = 0;
    let mut v_r_5116_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5115_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__1(v_00_u03b2_5112_, v_x_5113_, v_x_5114_);
    crate::leanh::lean_dec(v_x_5114_);
    crate::leanh::lean_dec_ref(v_x_5113_);
    v_r_5116_ = crate::leanh::lean_box((v_res_5115_) as usize);
    return v_r_5116_;
}
pub unsafe fn l___private_Init_While_0__whileM_erased___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__2(
    mut v_a_5117_: *mut crate::leanh::LeanObject,
    mut v_inst_5118_: *mut crate::leanh::LeanObject,
    mut v_a_5119_: *mut crate::leanh::LeanObject,
    mut v___y_5120_: *mut crate::leanh::LeanObject,
    mut v___y_5121_: *mut crate::leanh::LeanObject,
    mut v___y_5122_: *mut crate::leanh::LeanObject,
    mut v___y_5123_: *mut crate::leanh::LeanObject,
    mut v___y_5124_: *mut crate::leanh::LeanObject,
    mut v___y_5125_: *mut crate::leanh::LeanObject,
    mut v___y_5126_: *mut crate::leanh::LeanObject,
    mut v___y_5127_: *mut crate::leanh::LeanObject,
    mut v___y_5128_: *mut crate::leanh::LeanObject,
    mut v___y_5129_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5131_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5131_ = l___private_Init_While_0__whileM_erased___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__2___redArg(v_a_5117_, v_a_5119_, v___y_5120_);
    return v___x_5131_;
}
pub unsafe fn l___private_Init_While_0__whileM_erased___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__2___boxed(
    mut v_a_5132_: *mut crate::leanh::LeanObject,
    mut v_inst_5133_: *mut crate::leanh::LeanObject,
    mut v_a_5134_: *mut crate::leanh::LeanObject,
    mut v___y_5135_: *mut crate::leanh::LeanObject,
    mut v___y_5136_: *mut crate::leanh::LeanObject,
    mut v___y_5137_: *mut crate::leanh::LeanObject,
    mut v___y_5138_: *mut crate::leanh::LeanObject,
    mut v___y_5139_: *mut crate::leanh::LeanObject,
    mut v___y_5140_: *mut crate::leanh::LeanObject,
    mut v___y_5141_: *mut crate::leanh::LeanObject,
    mut v___y_5142_: *mut crate::leanh::LeanObject,
    mut v___y_5143_: *mut crate::leanh::LeanObject,
    mut v___y_5144_: *mut crate::leanh::LeanObject,
    mut v___y_5145_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5146_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5146_ = l___private_Init_While_0__whileM_erased___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__2(v_a_5132_, v_inst_5133_, v_a_5134_, v___y_5135_, v___y_5136_, v___y_5137_, v___y_5138_, v___y_5139_, v___y_5140_, v___y_5141_, v___y_5142_, v___y_5143_, v___y_5144_);
    crate::leanh::lean_dec(v___y_5144_);
    crate::leanh::lean_dec_ref(v___y_5143_);
    crate::leanh::lean_dec(v___y_5142_);
    crate::leanh::lean_dec_ref(v___y_5141_);
    crate::leanh::lean_dec(v___y_5140_);
    crate::leanh::lean_dec_ref(v___y_5139_);
    crate::leanh::lean_dec(v___y_5138_);
    crate::leanh::lean_dec_ref(v___y_5137_);
    crate::leanh::lean_dec(v___y_5136_);
    crate::leanh::lean_dec(v___y_5135_);
    return v_res_5146_;
}
pub unsafe fn l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__3(
    mut v_00_u03b2_5147_: *mut crate::leanh::LeanObject,
    mut v_x_5148_: *mut crate::leanh::LeanObject,
    mut v_x_5149_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5150_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5150_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__3___redArg(v_x_5148_, v_x_5149_);
    return v___x_5150_;
}
pub unsafe fn l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__3___boxed(
    mut v_00_u03b2_5151_: *mut crate::leanh::LeanObject,
    mut v_x_5152_: *mut crate::leanh::LeanObject,
    mut v_x_5153_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5154_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5154_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__3(v_00_u03b2_5151_, v_x_5152_, v_x_5153_);
    crate::leanh::lean_dec(v_x_5153_);
    crate::leanh::lean_dec_ref(v_x_5152_);
    return v_res_5154_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__0_spec__0(
    mut v_00_u03b2_5155_: *mut crate::leanh::LeanObject,
    mut v_x_5156_: *mut crate::leanh::LeanObject,
    mut v_x_5157_: usize,
    mut v_x_5158_: usize,
    mut v_x_5159_: *mut crate::leanh::LeanObject,
    mut v_x_5160_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5161_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5161_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__0_spec__0___redArg(v_x_5156_, v_x_5157_, v_x_5158_, v_x_5159_, v_x_5160_);
    return v___x_5161_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__0_spec__0___boxed(
    mut v_00_u03b2_5162_: *mut crate::leanh::LeanObject,
    mut v_x_5163_: *mut crate::leanh::LeanObject,
    mut v_x_5164_: *mut crate::leanh::LeanObject,
    mut v_x_5165_: *mut crate::leanh::LeanObject,
    mut v_x_5166_: *mut crate::leanh::LeanObject,
    mut v_x_5167_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_40762__boxed_5168_: usize = 0;
    let mut v_x_40763__boxed_5169_: usize = 0;
    let mut v_res_5170_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_40762__boxed_5168_ = crate::leanh::lean_unbox_usize(v_x_5164_);
    crate::leanh::lean_dec(v_x_5164_);
    v_x_40763__boxed_5169_ = crate::leanh::lean_unbox_usize(v_x_5165_);
    crate::leanh::lean_dec(v_x_5165_);
    v_res_5170_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__0_spec__0(v_00_u03b2_5162_, v_x_5163_, v_x_40762__boxed_5168_, v_x_40763__boxed_5169_, v_x_5166_, v_x_5167_);
    return v_res_5170_;
}
pub unsafe fn l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__1_spec__2(
    mut v_00_u03b2_5171_: *mut crate::leanh::LeanObject,
    mut v_x_5172_: *mut crate::leanh::LeanObject,
    mut v_x_5173_: usize,
    mut v_x_5174_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_5175_: u8 = 0;
    v___x_5175_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__1_spec__2___redArg(v_x_5172_, v_x_5173_, v_x_5174_);
    return v___x_5175_;
}
pub unsafe fn l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__1_spec__2___boxed(
    mut v_00_u03b2_5176_: *mut crate::leanh::LeanObject,
    mut v_x_5177_: *mut crate::leanh::LeanObject,
    mut v_x_5178_: *mut crate::leanh::LeanObject,
    mut v_x_5179_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_40779__boxed_5180_: usize = 0;
    let mut v_res_5181_: u8 = 0;
    let mut v_r_5182_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_40779__boxed_5180_ = crate::leanh::lean_unbox_usize(v_x_5178_);
    crate::leanh::lean_dec(v_x_5178_);
    v_res_5181_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__1_spec__2(v_00_u03b2_5176_, v_x_5177_, v_x_40779__boxed_5180_, v_x_5179_);
    crate::leanh::lean_dec(v_x_5179_);
    crate::leanh::lean_dec_ref(v_x_5177_);
    v_r_5182_ = crate::leanh::lean_box((v_res_5181_) as usize);
    return v_r_5182_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__3_spec__5(
    mut v_00_u03b2_5183_: *mut crate::leanh::LeanObject,
    mut v_x_5184_: *mut crate::leanh::LeanObject,
    mut v_x_5185_: usize,
    mut v_x_5186_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5187_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5187_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__3_spec__5___redArg(v_x_5184_, v_x_5185_, v_x_5186_);
    return v___x_5187_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__3_spec__5___boxed(
    mut v_00_u03b2_5188_: *mut crate::leanh::LeanObject,
    mut v_x_5189_: *mut crate::leanh::LeanObject,
    mut v_x_5190_: *mut crate::leanh::LeanObject,
    mut v_x_5191_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_40790__boxed_5192_: usize = 0;
    let mut v_res_5193_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_40790__boxed_5192_ = crate::leanh::lean_unbox_usize(v_x_5190_);
    crate::leanh::lean_dec(v_x_5190_);
    v_res_5193_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__3_spec__5(v_00_u03b2_5188_, v_x_5189_, v_x_40790__boxed_5192_, v_x_5191_);
    crate::leanh::lean_dec(v_x_5191_);
    crate::leanh::lean_dec_ref(v_x_5189_);
    return v_res_5193_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__0_spec__0_spec__1(
    mut v_00_u03b2_5194_: *mut crate::leanh::LeanObject,
    mut v_n_5195_: *mut crate::leanh::LeanObject,
    mut v_k_5196_: *mut crate::leanh::LeanObject,
    mut v_v_5197_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5198_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5198_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__0_spec__0_spec__1___redArg(v_n_5195_, v_k_5196_, v_v_5197_);
    return v___x_5198_;
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__0_spec__0_spec__2(
    mut v_00_u03b2_5199_: *mut crate::leanh::LeanObject,
    mut v_depth_5200_: usize,
    mut v_keys_5201_: *mut crate::leanh::LeanObject,
    mut v_vals_5202_: *mut crate::leanh::LeanObject,
    mut v_heq_5203_: *mut crate::leanh::LeanObject,
    mut v_i_5204_: *mut crate::leanh::LeanObject,
    mut v_entries_5205_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5206_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5206_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__0_spec__0_spec__2___redArg(v_depth_5200_, v_keys_5201_, v_vals_5202_, v_i_5204_, v_entries_5205_);
    return v___x_5206_;
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__0_spec__0_spec__2___boxed(
    mut v_00_u03b2_5207_: *mut crate::leanh::LeanObject,
    mut v_depth_5208_: *mut crate::leanh::LeanObject,
    mut v_keys_5209_: *mut crate::leanh::LeanObject,
    mut v_vals_5210_: *mut crate::leanh::LeanObject,
    mut v_heq_5211_: *mut crate::leanh::LeanObject,
    mut v_i_5212_: *mut crate::leanh::LeanObject,
    mut v_entries_5213_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_depth_boxed_5214_: usize = 0;
    let mut v_res_5215_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_depth_boxed_5214_ = crate::leanh::lean_unbox_usize(v_depth_5208_);
    crate::leanh::lean_dec(v_depth_5208_);
    v_res_5215_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__0_spec__0_spec__2(v_00_u03b2_5207_, v_depth_boxed_5214_, v_keys_5209_, v_vals_5210_, v_heq_5211_, v_i_5212_, v_entries_5213_);
    crate::leanh::lean_dec_ref(v_vals_5210_);
    crate::leanh::lean_dec_ref(v_keys_5209_);
    return v_res_5215_;
}
pub unsafe fn l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__1_spec__2_spec__5(
    mut v_00_u03b2_5216_: *mut crate::leanh::LeanObject,
    mut v_keys_5217_: *mut crate::leanh::LeanObject,
    mut v_vals_5218_: *mut crate::leanh::LeanObject,
    mut v_heq_5219_: *mut crate::leanh::LeanObject,
    mut v_i_5220_: *mut crate::leanh::LeanObject,
    mut v_k_5221_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_5222_: u8 = 0;
    v___x_5222_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__1_spec__2_spec__5___redArg(v_keys_5217_, v_i_5220_, v_k_5221_);
    return v___x_5222_;
}
pub unsafe fn l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__1_spec__2_spec__5___boxed(
    mut v_00_u03b2_5223_: *mut crate::leanh::LeanObject,
    mut v_keys_5224_: *mut crate::leanh::LeanObject,
    mut v_vals_5225_: *mut crate::leanh::LeanObject,
    mut v_heq_5226_: *mut crate::leanh::LeanObject,
    mut v_i_5227_: *mut crate::leanh::LeanObject,
    mut v_k_5228_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5229_: u8 = 0;
    let mut v_r_5230_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5229_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__1_spec__2_spec__5(v_00_u03b2_5223_, v_keys_5224_, v_vals_5225_, v_heq_5226_, v_i_5227_, v_k_5228_);
    crate::leanh::lean_dec(v_k_5228_);
    crate::leanh::lean_dec_ref(v_vals_5225_);
    crate::leanh::lean_dec_ref(v_keys_5224_);
    v_r_5230_ = crate::leanh::lean_box((v_res_5229_) as usize);
    return v_r_5230_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__3_spec__5_spec__9(
    mut v_00_u03b2_5231_: *mut crate::leanh::LeanObject,
    mut v_keys_5232_: *mut crate::leanh::LeanObject,
    mut v_vals_5233_: *mut crate::leanh::LeanObject,
    mut v_heq_5234_: *mut crate::leanh::LeanObject,
    mut v_i_5235_: *mut crate::leanh::LeanObject,
    mut v_k_5236_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5237_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5237_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__3_spec__5_spec__9___redArg(v_keys_5232_, v_vals_5233_, v_i_5235_, v_k_5236_);
    return v___x_5237_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__3_spec__5_spec__9___boxed(
    mut v_00_u03b2_5238_: *mut crate::leanh::LeanObject,
    mut v_keys_5239_: *mut crate::leanh::LeanObject,
    mut v_vals_5240_: *mut crate::leanh::LeanObject,
    mut v_heq_5241_: *mut crate::leanh::LeanObject,
    mut v_i_5242_: *mut crate::leanh::LeanObject,
    mut v_k_5243_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5244_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5244_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__3_spec__5_spec__9(v_00_u03b2_5238_, v_keys_5239_, v_vals_5240_, v_heq_5241_, v_i_5242_, v_k_5243_);
    crate::leanh::lean_dec(v_k_5243_);
    crate::leanh::lean_dec_ref(v_vals_5240_);
    crate::leanh::lean_dec_ref(v_keys_5239_);
    return v_res_5244_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__0_spec__0_spec__1_spec__5(
    mut v_00_u03b2_5245_: *mut crate::leanh::LeanObject,
    mut v_x_5246_: *mut crate::leanh::LeanObject,
    mut v_x_5247_: *mut crate::leanh::LeanObject,
    mut v_x_5248_: *mut crate::leanh::LeanObject,
    mut v_x_5249_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5250_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5250_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__0_spec__0_spec__1_spec__5___redArg(v_x_5246_, v_x_5247_, v_x_5248_, v_x_5249_);
    return v___x_5250_;
}
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_intro1_spec__0_spec__0(
    mut v_msgData_5251_: *mut crate::leanh::LeanObject,
    mut v___y_5252_: *mut crate::leanh::LeanObject,
    mut v___y_5253_: *mut crate::leanh::LeanObject,
    mut v___y_5254_: *mut crate::leanh::LeanObject,
    mut v___y_5255_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5257_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_5258_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5259_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_5260_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_lctx_5261_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_5262_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5263_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5264_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5265_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5257_ = lean_st_ref_get(v___y_5255_);
    v_env_5258_ = crate::leanh::lean_ctor_get(v___x_5257_, 0);
    crate::leanh::lean_inc_ref(v_env_5258_);
    crate::leanh::lean_dec(v___x_5257_);
    v___x_5259_ = lean_st_ref_get(v___y_5253_);
    v_mctx_5260_ = crate::leanh::lean_ctor_get(v___x_5259_, 0);
    crate::leanh::lean_inc_ref(v_mctx_5260_);
    crate::leanh::lean_dec(v___x_5259_);
    v_lctx_5261_ = crate::leanh::lean_ctor_get(v___y_5252_, 2);
    v_options_5262_ = crate::leanh::lean_ctor_get(v___y_5254_, 2);
    crate::leanh::lean_inc_ref(v_options_5262_);
    crate::leanh::lean_inc_ref(v_lctx_5261_);
    v___x_5263_ = crate::leanh::lean_alloc_ctor(0, 4, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_5263_, 0, v_env_5258_);
    crate::leanh::lean_ctor_set(v___x_5263_, 1, v_mctx_5260_);
    crate::leanh::lean_ctor_set(v___x_5263_, 2, v_lctx_5261_);
    crate::leanh::lean_ctor_set(v___x_5263_, 3, v_options_5262_);
    v___x_5264_ = crate::leanh::lean_alloc_ctor(3, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_5264_, 0, v___x_5263_);
    crate::leanh::lean_ctor_set(v___x_5264_, 1, v_msgData_5251_);
    v___x_5265_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_5265_, 0, v___x_5264_);
    return v___x_5265_;
}
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_intro1_spec__0_spec__0___boxed(
    mut v_msgData_5266_: *mut crate::leanh::LeanObject,
    mut v___y_5267_: *mut crate::leanh::LeanObject,
    mut v___y_5268_: *mut crate::leanh::LeanObject,
    mut v___y_5269_: *mut crate::leanh::LeanObject,
    mut v___y_5270_: *mut crate::leanh::LeanObject,
    mut v___y_5271_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5272_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5272_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_intro1_spec__0_spec__0(v_msgData_5266_, v___y_5267_, v___y_5268_, v___y_5269_, v___y_5270_);
    crate::leanh::lean_dec(v___y_5270_);
    crate::leanh::lean_dec_ref(v___y_5269_);
    crate::leanh::lean_dec(v___y_5268_);
    crate::leanh::lean_dec_ref(v___y_5267_);
    return v_res_5272_;
}
pub unsafe fn l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_intro1_spec__0___redArg(
    mut v_msg_5273_: *mut crate::leanh::LeanObject,
    mut v___y_5274_: *mut crate::leanh::LeanObject,
    mut v___y_5275_: *mut crate::leanh::LeanObject,
    mut v___y_5276_: *mut crate::leanh::LeanObject,
    mut v___y_5277_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_ref_5279_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5280_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5281_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5283_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5284_: u8 = 0;
    let mut v___x_5285_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5287_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5288_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5289_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ref_5279_ = crate::leanh::lean_ctor_get(v___y_5276_, 5);
                v___x_5280_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_intro1_spec__0_spec__0(v_msg_5273_, v___y_5274_, v___y_5275_, v___y_5276_, v___y_5277_);
                v_a_5281_ = crate::leanh::lean_ctor_get(v___x_5280_, 0);
                v_isSharedCheck_5289_ = (!crate::leanh::lean_is_exclusive(v___x_5280_)) as u8;
                if v_isSharedCheck_5289_ == 0 {
                    v___x_5283_ = v___x_5280_;
                    v_isShared_5284_ = v_isSharedCheck_5289_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_a_5281_);
                    crate::leanh::lean_dec(v___x_5280_);
                    v___x_5283_ = crate::leanh::lean_box(0);
                    v_isShared_5284_ = v_isSharedCheck_5289_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                crate::leanh::lean_inc(v_ref_5279_);
                v___x_5285_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_5285_, 0, v_ref_5279_);
                crate::leanh::lean_ctor_set(v___x_5285_, 1, v_a_5281_);
                if v_isShared_5284_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_5283_, 1);
                    crate::leanh::lean_ctor_set(v___x_5283_, 0, v___x_5285_);
                    v___x_5287_ = v___x_5283_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5288_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5288_, 0, v___x_5285_);
                    v___x_5287_ = v_reuseFailAlloc_5288_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_5287_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_intro1_spec__0___redArg___boxed(
    mut v_msg_5290_: *mut crate::leanh::LeanObject,
    mut v___y_5291_: *mut crate::leanh::LeanObject,
    mut v___y_5292_: *mut crate::leanh::LeanObject,
    mut v___y_5293_: *mut crate::leanh::LeanObject,
    mut v___y_5294_: *mut crate::leanh::LeanObject,
    mut v___y_5295_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5296_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5296_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_intro1_spec__0___redArg(v_msg_5290_, v___y_5291_, v___y_5292_, v___y_5293_, v___y_5294_);
    crate::leanh::lean_dec(v___y_5294_);
    crate::leanh::lean_dec_ref(v___y_5293_);
    crate::leanh::lean_dec(v___y_5292_);
    crate::leanh::lean_dec_ref(v___y_5291_);
    return v_res_5296_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_intro1___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_5298_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5299_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5298_ = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_intro1___closed__0;
    v___x_5299_ = l_Lean_stringToMessageData(v___x_5298_);
    return v___x_5299_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_intro1(
    mut v_a_5300_: *mut crate::leanh::LeanObject,
    mut v_a_5301_: *mut crate::leanh::LeanObject,
    mut v_a_5302_: *mut crate::leanh::LeanObject,
    mut v_a_5303_: *mut crate::leanh::LeanObject,
    mut v_a_5304_: *mut crate::leanh::LeanObject,
    mut v_a_5305_: *mut crate::leanh::LeanObject,
    mut v_a_5306_: *mut crate::leanh::LeanObject,
    mut v_a_5307_: *mut crate::leanh::LeanObject,
    mut v_a_5308_: *mut crate::leanh::LeanObject,
    mut v_a_5309_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_fst_5312_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_5313_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5314_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5315_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5316_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5317_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5318_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5319_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5320_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5321_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5322_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5323_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5324_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5325_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5326_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mvarId_5327_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5328_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5329_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5331_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5332_: u8 = 0;
    let mut v_fst_5333_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_5334_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5335_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toGoalState_5336_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5338_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5339_: u8 = 0;
    let mut v___x_5341_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5342_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5344_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5345_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5346_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5347_: u8 = 0;
    let mut v_unused_5348_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5349_: u8 = 0;
    let mut v_a_5350_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5352_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5353_: u8 = 0;
    let mut v___x_5355_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5356_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5357_: u8 = 0;
    let mut v_a_5358_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5360_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5361_: u8 = 0;
    let mut v___x_5363_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5364_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5365_: u8 = 0;
    let mut v___x_5366_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mvarId_5367_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5368_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5369_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_binderName_5370_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_binderType_5371_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_declName_5372_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_type_5373_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5374_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5375_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5376_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5378_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5379_: u8 = 0;
    let mut v___x_5381_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5382_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5383_: u8 = 0;
    let mut v_a_5384_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5386_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5387_: u8 = 0;
    let mut v___x_5389_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5390_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5391_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5366_ = lean_st_ref_get(v_a_5300_);
                v_mvarId_5367_ = crate::leanh::lean_ctor_get(v___x_5366_, 1);
                crate::leanh::lean_inc(v_mvarId_5367_);
                crate::leanh::lean_dec(v___x_5366_);
                v___x_5368_ = l_Lean_MVarId_getType(
                    v_mvarId_5367_,
                    v_a_5306_,
                    v_a_5307_,
                    v_a_5308_,
                    v_a_5309_,
                );
                if crate::leanh::lean_obj_tag(v___x_5368_) == 0 {
                    v_a_5369_ = crate::leanh::lean_ctor_get(v___x_5368_, 0);
                    crate::leanh::lean_inc(v_a_5369_);
                    crate::leanh::lean_dec_ref_known(v___x_5368_, 1);
                    match crate::leanh::lean_obj_tag(v_a_5369_) {
                        7 => {
                            v_binderName_5370_ = crate::leanh::lean_ctor_get(v_a_5369_, 0);
                            crate::leanh::lean_inc(v_binderName_5370_);
                            v_binderType_5371_ = crate::leanh::lean_ctor_get(v_a_5369_, 1);
                            crate::leanh::lean_inc_ref(v_binderType_5371_);
                            crate::leanh::lean_dec_ref_known(v_a_5369_, 3);
                            v_fst_5312_ = v_binderName_5370_;
                            v_snd_5313_ = v_binderType_5371_;
                            v___y_5314_ = v_a_5300_;
                            v___y_5315_ = v_a_5301_;
                            v___y_5316_ = v_a_5302_;
                            v___y_5317_ = v_a_5303_;
                            v___y_5318_ = v_a_5304_;
                            v___y_5319_ = v_a_5305_;
                            v___y_5320_ = v_a_5306_;
                            v___y_5321_ = v_a_5307_;
                            v___y_5322_ = v_a_5308_;
                            v___y_5323_ = v_a_5309_;
                            state = 1;
                            continue;
                        }
                        8 => {
                            v_declName_5372_ = crate::leanh::lean_ctor_get(v_a_5369_, 0);
                            crate::leanh::lean_inc(v_declName_5372_);
                            v_type_5373_ = crate::leanh::lean_ctor_get(v_a_5369_, 1);
                            crate::leanh::lean_inc_ref(v_type_5373_);
                            crate::leanh::lean_dec_ref_known(v_a_5369_, 4);
                            v_fst_5312_ = v_declName_5372_;
                            v_snd_5313_ = v_type_5373_;
                            v___y_5314_ = v_a_5300_;
                            v___y_5315_ = v_a_5301_;
                            v___y_5316_ = v_a_5302_;
                            v___y_5317_ = v_a_5303_;
                            v___y_5318_ = v_a_5304_;
                            v___y_5319_ = v_a_5305_;
                            v___y_5320_ = v_a_5306_;
                            v___y_5321_ = v_a_5307_;
                            v___y_5322_ = v_a_5308_;
                            v___y_5323_ = v_a_5309_;
                            state = 1;
                            continue;
                        }
                        _ => {
                            crate::leanh::lean_dec(v_a_5369_);
                            v___x_5374_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_intro1___closed__1), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_intro1___closed__1_once), _init_l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_intro1___closed__1);
                            v___x_5375_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_intro1_spec__0___redArg(v___x_5374_, v_a_5306_, v_a_5307_, v_a_5308_, v_a_5309_);
                            v_a_5376_ = crate::leanh::lean_ctor_get(v___x_5375_, 0);
                            v_isSharedCheck_5383_ =
                                (!crate::leanh::lean_is_exclusive(v___x_5375_)) as u8;
                            if v_isSharedCheck_5383_ == 0 {
                                v___x_5378_ = v___x_5375_;
                                v_isShared_5379_ = v_isSharedCheck_5383_;
                                state = 10;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_5376_);
                                crate::leanh::lean_dec(v___x_5375_);
                                v___x_5378_ = crate::leanh::lean_box(0);
                                v_isShared_5379_ = v_isSharedCheck_5383_;
                                state = 10;
                                continue;
                            }
                        }
                    }
                } else {
                    v_a_5384_ = crate::leanh::lean_ctor_get(v___x_5368_, 0);
                    v_isSharedCheck_5391_ = (!crate::leanh::lean_is_exclusive(v___x_5368_)) as u8;
                    if v_isSharedCheck_5391_ == 0 {
                        v___x_5386_ = v___x_5368_;
                        v_isShared_5387_ = v_isSharedCheck_5391_;
                        state = 12;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_5384_);
                        crate::leanh::lean_dec(v___x_5368_);
                        v___x_5386_ = crate::leanh::lean_box(0);
                        v_isShared_5387_ = v_isSharedCheck_5391_;
                        state = 12;
                        continue;
                    }
                }
            }
            1 => {
                v___x_5324_ =
                    l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName(
                        v_fst_5312_,
                        v_snd_5313_,
                        v___y_5314_,
                        v___y_5315_,
                        v___y_5316_,
                        v___y_5317_,
                        v___y_5318_,
                        v___y_5319_,
                        v___y_5320_,
                        v___y_5321_,
                        v___y_5322_,
                        v___y_5323_,
                    );
                if crate::leanh::lean_obj_tag(v___x_5324_) == 0 {
                    v_a_5325_ = crate::leanh::lean_ctor_get(v___x_5324_, 0);
                    crate::leanh::lean_inc(v_a_5325_);
                    crate::leanh::lean_dec_ref_known(v___x_5324_, 1);
                    v___x_5326_ = lean_st_ref_get(v___y_5314_);
                    v_mvarId_5327_ = crate::leanh::lean_ctor_get(v___x_5326_, 1);
                    crate::leanh::lean_inc(v_mvarId_5327_);
                    crate::leanh::lean_dec(v___x_5326_);
                    v___x_5328_ = l_Lean_MVarId_intro(
                        v_mvarId_5327_,
                        v_a_5325_,
                        v___y_5320_,
                        v___y_5321_,
                        v___y_5322_,
                        v___y_5323_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_5328_) == 0 {
                        v_a_5329_ = crate::leanh::lean_ctor_get(v___x_5328_, 0);
                        v_isSharedCheck_5349_ =
                            (!crate::leanh::lean_is_exclusive(v___x_5328_)) as u8;
                        if v_isSharedCheck_5349_ == 0 {
                            v___x_5331_ = v___x_5328_;
                            v_isShared_5332_ = v_isSharedCheck_5349_;
                            state = 2;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_5329_);
                            crate::leanh::lean_dec(v___x_5328_);
                            v___x_5331_ = crate::leanh::lean_box(0);
                            v_isShared_5332_ = v_isSharedCheck_5349_;
                            state = 2;
                            continue;
                        }
                    } else {
                        v_a_5350_ = crate::leanh::lean_ctor_get(v___x_5328_, 0);
                        v_isSharedCheck_5357_ =
                            (!crate::leanh::lean_is_exclusive(v___x_5328_)) as u8;
                        if v_isSharedCheck_5357_ == 0 {
                            v___x_5352_ = v___x_5328_;
                            v_isShared_5353_ = v_isSharedCheck_5357_;
                            state = 6;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_5350_);
                            crate::leanh::lean_dec(v___x_5328_);
                            v___x_5352_ = crate::leanh::lean_box(0);
                            v_isShared_5353_ = v_isSharedCheck_5357_;
                            state = 6;
                            continue;
                        }
                    }
                } else {
                    v_a_5358_ = crate::leanh::lean_ctor_get(v___x_5324_, 0);
                    v_isSharedCheck_5365_ = (!crate::leanh::lean_is_exclusive(v___x_5324_)) as u8;
                    if v_isSharedCheck_5365_ == 0 {
                        v___x_5360_ = v___x_5324_;
                        v_isShared_5361_ = v_isSharedCheck_5365_;
                        state = 8;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_5358_);
                        crate::leanh::lean_dec(v___x_5324_);
                        v___x_5360_ = crate::leanh::lean_box(0);
                        v_isShared_5361_ = v_isSharedCheck_5365_;
                        state = 8;
                        continue;
                    }
                }
            }
            2 => {
                v_fst_5333_ = crate::leanh::lean_ctor_get(v_a_5329_, 0);
                crate::leanh::lean_inc(v_fst_5333_);
                v_snd_5334_ = crate::leanh::lean_ctor_get(v_a_5329_, 1);
                crate::leanh::lean_inc(v_snd_5334_);
                crate::leanh::lean_dec(v_a_5329_);
                v___x_5335_ = lean_st_ref_take(v___y_5314_);
                v_toGoalState_5336_ = crate::leanh::lean_ctor_get(v___x_5335_, 0);
                v_isSharedCheck_5347_ = (!crate::leanh::lean_is_exclusive(v___x_5335_)) as u8;
                if v_isSharedCheck_5347_ == 0 {
                    v_unused_5348_ = crate::leanh::lean_ctor_get(v___x_5335_, 1);
                    crate::leanh::lean_dec(v_unused_5348_);
                    v___x_5338_ = v___x_5335_;
                    v_isShared_5339_ = v_isSharedCheck_5347_;
                    state = 3;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_toGoalState_5336_);
                    crate::leanh::lean_dec(v___x_5335_);
                    v___x_5338_ = crate::leanh::lean_box(0);
                    v_isShared_5339_ = v_isSharedCheck_5347_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_5339_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5338_, 1, v_snd_5334_);
                    v___x_5341_ = v___x_5338_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_5346_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5346_, 0, v_toGoalState_5336_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5346_, 1, v_snd_5334_);
                    v___x_5341_ = v_reuseFailAlloc_5346_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_5342_ = lean_st_ref_set(v___y_5314_, v___x_5341_);
                if v_isShared_5332_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5331_, 0, v_fst_5333_);
                    v___x_5344_ = v___x_5331_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_5345_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5345_, 0, v_fst_5333_);
                    v___x_5344_ = v_reuseFailAlloc_5345_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_5344_;
            }
            6 => {
                if v_isShared_5353_ == 0 {
                    v___x_5355_ = v___x_5352_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_5356_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5356_, 0, v_a_5350_);
                    v___x_5355_ = v_reuseFailAlloc_5356_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_5355_;
            }
            8 => {
                if v_isShared_5361_ == 0 {
                    v___x_5363_ = v___x_5360_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_5364_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5364_, 0, v_a_5358_);
                    v___x_5363_ = v_reuseFailAlloc_5364_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_5363_;
            }
            10 => {
                if v_isShared_5379_ == 0 {
                    v___x_5381_ = v___x_5378_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_5382_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5382_, 0, v_a_5376_);
                    v___x_5381_ = v_reuseFailAlloc_5382_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                return v___x_5381_;
            }
            12 => {
                if v_isShared_5387_ == 0 {
                    v___x_5389_ = v___x_5386_;
                    state = 13;
                    continue;
                } else {
                    v_reuseFailAlloc_5390_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5390_, 0, v_a_5384_);
                    v___x_5389_ = v_reuseFailAlloc_5390_;
                    state = 13;
                    continue;
                }
            }
            13 => {
                return v___x_5389_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_intro1___boxed(
    mut v_a_5392_: *mut crate::leanh::LeanObject,
    mut v_a_5393_: *mut crate::leanh::LeanObject,
    mut v_a_5394_: *mut crate::leanh::LeanObject,
    mut v_a_5395_: *mut crate::leanh::LeanObject,
    mut v_a_5396_: *mut crate::leanh::LeanObject,
    mut v_a_5397_: *mut crate::leanh::LeanObject,
    mut v_a_5398_: *mut crate::leanh::LeanObject,
    mut v_a_5399_: *mut crate::leanh::LeanObject,
    mut v_a_5400_: *mut crate::leanh::LeanObject,
    mut v_a_5401_: *mut crate::leanh::LeanObject,
    mut v_a_5402_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5403_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5403_ = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_intro1(
        v_a_5392_, v_a_5393_, v_a_5394_, v_a_5395_, v_a_5396_, v_a_5397_, v_a_5398_, v_a_5399_,
        v_a_5400_, v_a_5401_,
    );
    crate::leanh::lean_dec(v_a_5401_);
    crate::leanh::lean_dec_ref(v_a_5400_);
    crate::leanh::lean_dec(v_a_5399_);
    crate::leanh::lean_dec_ref(v_a_5398_);
    crate::leanh::lean_dec(v_a_5397_);
    crate::leanh::lean_dec_ref(v_a_5396_);
    crate::leanh::lean_dec(v_a_5395_);
    crate::leanh::lean_dec_ref(v_a_5394_);
    crate::leanh::lean_dec(v_a_5393_);
    crate::leanh::lean_dec(v_a_5392_);
    return v_res_5403_;
}
pub unsafe fn l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_intro1_spec__0(
    mut v_00_u03b1_5404_: *mut crate::leanh::LeanObject,
    mut v_msg_5405_: *mut crate::leanh::LeanObject,
    mut v___y_5406_: *mut crate::leanh::LeanObject,
    mut v___y_5407_: *mut crate::leanh::LeanObject,
    mut v___y_5408_: *mut crate::leanh::LeanObject,
    mut v___y_5409_: *mut crate::leanh::LeanObject,
    mut v___y_5410_: *mut crate::leanh::LeanObject,
    mut v___y_5411_: *mut crate::leanh::LeanObject,
    mut v___y_5412_: *mut crate::leanh::LeanObject,
    mut v___y_5413_: *mut crate::leanh::LeanObject,
    mut v___y_5414_: *mut crate::leanh::LeanObject,
    mut v___y_5415_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5417_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5417_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_intro1_spec__0___redArg(v_msg_5405_, v___y_5412_, v___y_5413_, v___y_5414_, v___y_5415_);
    return v___x_5417_;
}
pub unsafe fn l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_intro1_spec__0___boxed(
    mut v_00_u03b1_5418_: *mut crate::leanh::LeanObject,
    mut v_msg_5419_: *mut crate::leanh::LeanObject,
    mut v___y_5420_: *mut crate::leanh::LeanObject,
    mut v___y_5421_: *mut crate::leanh::LeanObject,
    mut v___y_5422_: *mut crate::leanh::LeanObject,
    mut v___y_5423_: *mut crate::leanh::LeanObject,
    mut v___y_5424_: *mut crate::leanh::LeanObject,
    mut v___y_5425_: *mut crate::leanh::LeanObject,
    mut v___y_5426_: *mut crate::leanh::LeanObject,
    mut v___y_5427_: *mut crate::leanh::LeanObject,
    mut v___y_5428_: *mut crate::leanh::LeanObject,
    mut v___y_5429_: *mut crate::leanh::LeanObject,
    mut v___y_5430_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5431_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5431_ = l_Lean_throwError___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_intro1_spec__0(v_00_u03b1_5418_, v_msg_5419_, v___y_5420_, v___y_5421_, v___y_5422_, v___y_5423_, v___y_5424_, v___y_5425_, v___y_5426_, v___y_5427_, v___y_5428_, v___y_5429_);
    crate::leanh::lean_dec(v___y_5429_);
    crate::leanh::lean_dec_ref(v___y_5428_);
    crate::leanh::lean_dec(v___y_5427_);
    crate::leanh::lean_dec_ref(v___y_5426_);
    crate::leanh::lean_dec(v___y_5425_);
    crate::leanh::lean_dec_ref(v___y_5424_);
    crate::leanh::lean_dec(v___y_5423_);
    crate::leanh::lean_dec_ref(v___y_5422_);
    crate::leanh::lean_dec(v___y_5421_);
    crate::leanh::lean_dec(v___y_5420_);
    return v_res_5431_;
}
pub unsafe fn l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__0___redArg___lam__0(
    mut v_x_5432_: *mut crate::leanh::LeanObject,
    mut v___y_5433_: *mut crate::leanh::LeanObject,
    mut v___y_5434_: *mut crate::leanh::LeanObject,
    mut v___y_5435_: *mut crate::leanh::LeanObject,
    mut v___y_5436_: *mut crate::leanh::LeanObject,
    mut v___y_5437_: *mut crate::leanh::LeanObject,
    mut v___y_5438_: *mut crate::leanh::LeanObject,
    mut v___y_5439_: *mut crate::leanh::LeanObject,
    mut v___y_5440_: *mut crate::leanh::LeanObject,
    mut v___y_5441_: *mut crate::leanh::LeanObject,
    mut v___y_5442_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5444_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    crate::leanh::lean_inc(v___y_5438_);
    crate::leanh::lean_inc_ref(v___y_5437_);
    crate::leanh::lean_inc(v___y_5436_);
    crate::leanh::lean_inc_ref(v___y_5435_);
    crate::leanh::lean_inc(v___y_5434_);
    crate::leanh::lean_inc(v___y_5433_);
    v___x_5444_ = crate::leanh::lean_apply_11(
        v_x_5432_,
        v___y_5433_,
        v___y_5434_,
        v___y_5435_,
        v___y_5436_,
        v___y_5437_,
        v___y_5438_,
        v___y_5439_,
        v___y_5440_,
        v___y_5441_,
        v___y_5442_,
        crate::leanh::lean_box(0),
    );
    return v___x_5444_;
}
pub unsafe fn l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__0___redArg___lam__0___boxed(
    mut v_x_5445_: *mut crate::leanh::LeanObject,
    mut v___y_5446_: *mut crate::leanh::LeanObject,
    mut v___y_5447_: *mut crate::leanh::LeanObject,
    mut v___y_5448_: *mut crate::leanh::LeanObject,
    mut v___y_5449_: *mut crate::leanh::LeanObject,
    mut v___y_5450_: *mut crate::leanh::LeanObject,
    mut v___y_5451_: *mut crate::leanh::LeanObject,
    mut v___y_5452_: *mut crate::leanh::LeanObject,
    mut v___y_5453_: *mut crate::leanh::LeanObject,
    mut v___y_5454_: *mut crate::leanh::LeanObject,
    mut v___y_5455_: *mut crate::leanh::LeanObject,
    mut v___y_5456_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5457_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5457_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__0___redArg___lam__0(v_x_5445_, v___y_5446_, v___y_5447_, v___y_5448_, v___y_5449_, v___y_5450_, v___y_5451_, v___y_5452_, v___y_5453_, v___y_5454_, v___y_5455_);
    crate::leanh::lean_dec(v___y_5451_);
    crate::leanh::lean_dec_ref(v___y_5450_);
    crate::leanh::lean_dec(v___y_5449_);
    crate::leanh::lean_dec_ref(v___y_5448_);
    crate::leanh::lean_dec(v___y_5447_);
    crate::leanh::lean_dec(v___y_5446_);
    return v_res_5457_;
}
pub unsafe fn l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__0___redArg(
    mut v_mvarId_5458_: *mut crate::leanh::LeanObject,
    mut v_x_5459_: *mut crate::leanh::LeanObject,
    mut v___y_5460_: *mut crate::leanh::LeanObject,
    mut v___y_5461_: *mut crate::leanh::LeanObject,
    mut v___y_5462_: *mut crate::leanh::LeanObject,
    mut v___y_5463_: *mut crate::leanh::LeanObject,
    mut v___y_5464_: *mut crate::leanh::LeanObject,
    mut v___y_5465_: *mut crate::leanh::LeanObject,
    mut v___y_5466_: *mut crate::leanh::LeanObject,
    mut v___y_5467_: *mut crate::leanh::LeanObject,
    mut v___y_5468_: *mut crate::leanh::LeanObject,
    mut v___y_5469_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_5471_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5472_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5473_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5475_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5476_: u8 = 0;
    let mut v___x_5478_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5479_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5480_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                crate::leanh::lean_inc(v___y_5465_);
                crate::leanh::lean_inc_ref(v___y_5464_);
                crate::leanh::lean_inc(v___y_5463_);
                crate::leanh::lean_inc_ref(v___y_5462_);
                crate::leanh::lean_inc(v___y_5461_);
                crate::leanh::lean_inc(v___y_5460_);
                v___f_5471_ = crate::leanh::lean_alloc_closure(l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__0___redArg___lam__0___boxed as *mut core::ffi::c_void, 12, 7);
                crate::leanh::lean_closure_set(v___f_5471_, 0, v_x_5459_);
                crate::leanh::lean_closure_set(v___f_5471_, 1, v___y_5460_);
                crate::leanh::lean_closure_set(v___f_5471_, 2, v___y_5461_);
                crate::leanh::lean_closure_set(v___f_5471_, 3, v___y_5462_);
                crate::leanh::lean_closure_set(v___f_5471_, 4, v___y_5463_);
                crate::leanh::lean_closure_set(v___f_5471_, 5, v___y_5464_);
                crate::leanh::lean_closure_set(v___f_5471_, 6, v___y_5465_);
                v___x_5472_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(
                    crate::leanh::lean_box(0),
                    v_mvarId_5458_,
                    v___f_5471_,
                    v___y_5466_,
                    v___y_5467_,
                    v___y_5468_,
                    v___y_5469_,
                );
                if crate::leanh::lean_obj_tag(v___x_5472_) == 0 {
                    return v___x_5472_;
                } else {
                    v_a_5473_ = crate::leanh::lean_ctor_get(v___x_5472_, 0);
                    v_isSharedCheck_5480_ = (!crate::leanh::lean_is_exclusive(v___x_5472_)) as u8;
                    if v_isSharedCheck_5480_ == 0 {
                        v___x_5475_ = v___x_5472_;
                        v_isShared_5476_ = v_isSharedCheck_5480_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_5473_);
                        crate::leanh::lean_dec(v___x_5472_);
                        v___x_5475_ = crate::leanh::lean_box(0);
                        v_isShared_5476_ = v_isSharedCheck_5480_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_5476_ == 0 {
                    v___x_5478_ = v___x_5475_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5479_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5479_, 0, v_a_5473_);
                    v___x_5478_ = v_reuseFailAlloc_5479_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_5478_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__0___redArg___boxed(
    mut v_mvarId_5481_: *mut crate::leanh::LeanObject,
    mut v_x_5482_: *mut crate::leanh::LeanObject,
    mut v___y_5483_: *mut crate::leanh::LeanObject,
    mut v___y_5484_: *mut crate::leanh::LeanObject,
    mut v___y_5485_: *mut crate::leanh::LeanObject,
    mut v___y_5486_: *mut crate::leanh::LeanObject,
    mut v___y_5487_: *mut crate::leanh::LeanObject,
    mut v___y_5488_: *mut crate::leanh::LeanObject,
    mut v___y_5489_: *mut crate::leanh::LeanObject,
    mut v___y_5490_: *mut crate::leanh::LeanObject,
    mut v___y_5491_: *mut crate::leanh::LeanObject,
    mut v___y_5492_: *mut crate::leanh::LeanObject,
    mut v___y_5493_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5494_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5494_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__0___redArg(v_mvarId_5481_, v_x_5482_, v___y_5483_, v___y_5484_, v___y_5485_, v___y_5486_, v___y_5487_, v___y_5488_, v___y_5489_, v___y_5490_, v___y_5491_, v___y_5492_);
    crate::leanh::lean_dec(v___y_5492_);
    crate::leanh::lean_dec_ref(v___y_5491_);
    crate::leanh::lean_dec(v___y_5490_);
    crate::leanh::lean_dec_ref(v___y_5489_);
    crate::leanh::lean_dec(v___y_5488_);
    crate::leanh::lean_dec_ref(v___y_5487_);
    crate::leanh::lean_dec(v___y_5486_);
    crate::leanh::lean_dec_ref(v___y_5485_);
    crate::leanh::lean_dec(v___y_5484_);
    crate::leanh::lean_dec(v___y_5483_);
    return v_res_5494_;
}
pub unsafe fn l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__0(
    mut v_00_u03b1_5495_: *mut crate::leanh::LeanObject,
    mut v_mvarId_5496_: *mut crate::leanh::LeanObject,
    mut v_x_5497_: *mut crate::leanh::LeanObject,
    mut v___y_5498_: *mut crate::leanh::LeanObject,
    mut v___y_5499_: *mut crate::leanh::LeanObject,
    mut v___y_5500_: *mut crate::leanh::LeanObject,
    mut v___y_5501_: *mut crate::leanh::LeanObject,
    mut v___y_5502_: *mut crate::leanh::LeanObject,
    mut v___y_5503_: *mut crate::leanh::LeanObject,
    mut v___y_5504_: *mut crate::leanh::LeanObject,
    mut v___y_5505_: *mut crate::leanh::LeanObject,
    mut v___y_5506_: *mut crate::leanh::LeanObject,
    mut v___y_5507_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5509_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5509_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__0___redArg(v_mvarId_5496_, v_x_5497_, v___y_5498_, v___y_5499_, v___y_5500_, v___y_5501_, v___y_5502_, v___y_5503_, v___y_5504_, v___y_5505_, v___y_5506_, v___y_5507_);
    return v___x_5509_;
}
pub unsafe fn l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__0___boxed(
    mut v_00_u03b1_5510_: *mut crate::leanh::LeanObject,
    mut v_mvarId_5511_: *mut crate::leanh::LeanObject,
    mut v_x_5512_: *mut crate::leanh::LeanObject,
    mut v___y_5513_: *mut crate::leanh::LeanObject,
    mut v___y_5514_: *mut crate::leanh::LeanObject,
    mut v___y_5515_: *mut crate::leanh::LeanObject,
    mut v___y_5516_: *mut crate::leanh::LeanObject,
    mut v___y_5517_: *mut crate::leanh::LeanObject,
    mut v___y_5518_: *mut crate::leanh::LeanObject,
    mut v___y_5519_: *mut crate::leanh::LeanObject,
    mut v___y_5520_: *mut crate::leanh::LeanObject,
    mut v___y_5521_: *mut crate::leanh::LeanObject,
    mut v___y_5522_: *mut crate::leanh::LeanObject,
    mut v___y_5523_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5524_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5524_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__0(v_00_u03b1_5510_, v_mvarId_5511_, v_x_5512_, v___y_5513_, v___y_5514_, v___y_5515_, v___y_5516_, v___y_5517_, v___y_5518_, v___y_5519_, v___y_5520_, v___y_5521_, v___y_5522_);
    crate::leanh::lean_dec(v___y_5522_);
    crate::leanh::lean_dec_ref(v___y_5521_);
    crate::leanh::lean_dec(v___y_5520_);
    crate::leanh::lean_dec_ref(v___y_5519_);
    crate::leanh::lean_dec(v___y_5518_);
    crate::leanh::lean_dec_ref(v___y_5517_);
    crate::leanh::lean_dec(v___y_5516_);
    crate::leanh::lean_dec_ref(v___y_5515_);
    crate::leanh::lean_dec(v___y_5514_);
    crate::leanh::lean_dec(v___y_5513_);
    return v_res_5524_;
}
pub unsafe fn l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__3___redArg___lam__0(
    mut v_x_5525_: *mut crate::leanh::LeanObject,
    mut v___y_5526_: *mut crate::leanh::LeanObject,
    mut v___y_5527_: *mut crate::leanh::LeanObject,
    mut v___y_5528_: *mut crate::leanh::LeanObject,
    mut v___y_5529_: *mut crate::leanh::LeanObject,
    mut v___y_5530_: *mut crate::leanh::LeanObject,
    mut v___y_5531_: *mut crate::leanh::LeanObject,
    mut v___y_5532_: *mut crate::leanh::LeanObject,
    mut v___y_5533_: *mut crate::leanh::LeanObject,
    mut v___y_5534_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5536_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    crate::leanh::lean_inc(v___y_5530_);
    crate::leanh::lean_inc_ref(v___y_5529_);
    crate::leanh::lean_inc(v___y_5528_);
    crate::leanh::lean_inc_ref(v___y_5527_);
    crate::leanh::lean_inc(v___y_5526_);
    v___x_5536_ = crate::leanh::lean_apply_10(
        v_x_5525_,
        v___y_5526_,
        v___y_5527_,
        v___y_5528_,
        v___y_5529_,
        v___y_5530_,
        v___y_5531_,
        v___y_5532_,
        v___y_5533_,
        v___y_5534_,
        crate::leanh::lean_box(0),
    );
    return v___x_5536_;
}
pub unsafe fn l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__3___redArg___lam__0___boxed(
    mut v_x_5537_: *mut crate::leanh::LeanObject,
    mut v___y_5538_: *mut crate::leanh::LeanObject,
    mut v___y_5539_: *mut crate::leanh::LeanObject,
    mut v___y_5540_: *mut crate::leanh::LeanObject,
    mut v___y_5541_: *mut crate::leanh::LeanObject,
    mut v___y_5542_: *mut crate::leanh::LeanObject,
    mut v___y_5543_: *mut crate::leanh::LeanObject,
    mut v___y_5544_: *mut crate::leanh::LeanObject,
    mut v___y_5545_: *mut crate::leanh::LeanObject,
    mut v___y_5546_: *mut crate::leanh::LeanObject,
    mut v___y_5547_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5548_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5548_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__3___redArg___lam__0(v_x_5537_, v___y_5538_, v___y_5539_, v___y_5540_, v___y_5541_, v___y_5542_, v___y_5543_, v___y_5544_, v___y_5545_, v___y_5546_);
    crate::leanh::lean_dec(v___y_5542_);
    crate::leanh::lean_dec_ref(v___y_5541_);
    crate::leanh::lean_dec(v___y_5540_);
    crate::leanh::lean_dec_ref(v___y_5539_);
    crate::leanh::lean_dec(v___y_5538_);
    return v_res_5548_;
}
pub unsafe fn l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__3___redArg(
    mut v_mvarId_5549_: *mut crate::leanh::LeanObject,
    mut v_x_5550_: *mut crate::leanh::LeanObject,
    mut v___y_5551_: *mut crate::leanh::LeanObject,
    mut v___y_5552_: *mut crate::leanh::LeanObject,
    mut v___y_5553_: *mut crate::leanh::LeanObject,
    mut v___y_5554_: *mut crate::leanh::LeanObject,
    mut v___y_5555_: *mut crate::leanh::LeanObject,
    mut v___y_5556_: *mut crate::leanh::LeanObject,
    mut v___y_5557_: *mut crate::leanh::LeanObject,
    mut v___y_5558_: *mut crate::leanh::LeanObject,
    mut v___y_5559_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_5561_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5562_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5563_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5565_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5566_: u8 = 0;
    let mut v___x_5568_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5569_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5570_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                crate::leanh::lean_inc(v___y_5555_);
                crate::leanh::lean_inc_ref(v___y_5554_);
                crate::leanh::lean_inc(v___y_5553_);
                crate::leanh::lean_inc_ref(v___y_5552_);
                crate::leanh::lean_inc(v___y_5551_);
                v___f_5561_ = crate::leanh::lean_alloc_closure(l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__3___redArg___lam__0___boxed as *mut core::ffi::c_void, 11, 6);
                crate::leanh::lean_closure_set(v___f_5561_, 0, v_x_5550_);
                crate::leanh::lean_closure_set(v___f_5561_, 1, v___y_5551_);
                crate::leanh::lean_closure_set(v___f_5561_, 2, v___y_5552_);
                crate::leanh::lean_closure_set(v___f_5561_, 3, v___y_5553_);
                crate::leanh::lean_closure_set(v___f_5561_, 4, v___y_5554_);
                crate::leanh::lean_closure_set(v___f_5561_, 5, v___y_5555_);
                v___x_5562_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(
                    crate::leanh::lean_box(0),
                    v_mvarId_5549_,
                    v___f_5561_,
                    v___y_5556_,
                    v___y_5557_,
                    v___y_5558_,
                    v___y_5559_,
                );
                if crate::leanh::lean_obj_tag(v___x_5562_) == 0 {
                    return v___x_5562_;
                } else {
                    v_a_5563_ = crate::leanh::lean_ctor_get(v___x_5562_, 0);
                    v_isSharedCheck_5570_ = (!crate::leanh::lean_is_exclusive(v___x_5562_)) as u8;
                    if v_isSharedCheck_5570_ == 0 {
                        v___x_5565_ = v___x_5562_;
                        v_isShared_5566_ = v_isSharedCheck_5570_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_5563_);
                        crate::leanh::lean_dec(v___x_5562_);
                        v___x_5565_ = crate::leanh::lean_box(0);
                        v_isShared_5566_ = v_isSharedCheck_5570_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_5566_ == 0 {
                    v___x_5568_ = v___x_5565_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5569_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5569_, 0, v_a_5563_);
                    v___x_5568_ = v_reuseFailAlloc_5569_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_5568_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__3___redArg___boxed(
    mut v_mvarId_5571_: *mut crate::leanh::LeanObject,
    mut v_x_5572_: *mut crate::leanh::LeanObject,
    mut v___y_5573_: *mut crate::leanh::LeanObject,
    mut v___y_5574_: *mut crate::leanh::LeanObject,
    mut v___y_5575_: *mut crate::leanh::LeanObject,
    mut v___y_5576_: *mut crate::leanh::LeanObject,
    mut v___y_5577_: *mut crate::leanh::LeanObject,
    mut v___y_5578_: *mut crate::leanh::LeanObject,
    mut v___y_5579_: *mut crate::leanh::LeanObject,
    mut v___y_5580_: *mut crate::leanh::LeanObject,
    mut v___y_5581_: *mut crate::leanh::LeanObject,
    mut v___y_5582_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5583_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5583_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__3___redArg(v_mvarId_5571_, v_x_5572_, v___y_5573_, v___y_5574_, v___y_5575_, v___y_5576_, v___y_5577_, v___y_5578_, v___y_5579_, v___y_5580_, v___y_5581_);
    crate::leanh::lean_dec(v___y_5581_);
    crate::leanh::lean_dec_ref(v___y_5580_);
    crate::leanh::lean_dec(v___y_5579_);
    crate::leanh::lean_dec_ref(v___y_5578_);
    crate::leanh::lean_dec(v___y_5577_);
    crate::leanh::lean_dec_ref(v___y_5576_);
    crate::leanh::lean_dec(v___y_5575_);
    crate::leanh::lean_dec_ref(v___y_5574_);
    crate::leanh::lean_dec(v___y_5573_);
    return v_res_5583_;
}
pub unsafe fn l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__3(
    mut v_00_u03b1_5584_: *mut crate::leanh::LeanObject,
    mut v_mvarId_5585_: *mut crate::leanh::LeanObject,
    mut v_x_5586_: *mut crate::leanh::LeanObject,
    mut v___y_5587_: *mut crate::leanh::LeanObject,
    mut v___y_5588_: *mut crate::leanh::LeanObject,
    mut v___y_5589_: *mut crate::leanh::LeanObject,
    mut v___y_5590_: *mut crate::leanh::LeanObject,
    mut v___y_5591_: *mut crate::leanh::LeanObject,
    mut v___y_5592_: *mut crate::leanh::LeanObject,
    mut v___y_5593_: *mut crate::leanh::LeanObject,
    mut v___y_5594_: *mut crate::leanh::LeanObject,
    mut v___y_5595_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5597_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5597_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__3___redArg(v_mvarId_5585_, v_x_5586_, v___y_5587_, v___y_5588_, v___y_5589_, v___y_5590_, v___y_5591_, v___y_5592_, v___y_5593_, v___y_5594_, v___y_5595_);
    return v___x_5597_;
}
pub unsafe fn l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__3___boxed(
    mut v_00_u03b1_5598_: *mut crate::leanh::LeanObject,
    mut v_mvarId_5599_: *mut crate::leanh::LeanObject,
    mut v_x_5600_: *mut crate::leanh::LeanObject,
    mut v___y_5601_: *mut crate::leanh::LeanObject,
    mut v___y_5602_: *mut crate::leanh::LeanObject,
    mut v___y_5603_: *mut crate::leanh::LeanObject,
    mut v___y_5604_: *mut crate::leanh::LeanObject,
    mut v___y_5605_: *mut crate::leanh::LeanObject,
    mut v___y_5606_: *mut crate::leanh::LeanObject,
    mut v___y_5607_: *mut crate::leanh::LeanObject,
    mut v___y_5608_: *mut crate::leanh::LeanObject,
    mut v___y_5609_: *mut crate::leanh::LeanObject,
    mut v___y_5610_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5611_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5611_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__3(v_00_u03b1_5598_, v_mvarId_5599_, v_x_5600_, v___y_5601_, v___y_5602_, v___y_5603_, v___y_5604_, v___y_5605_, v___y_5606_, v___y_5607_, v___y_5608_, v___y_5609_);
    crate::leanh::lean_dec(v___y_5609_);
    crate::leanh::lean_dec_ref(v___y_5608_);
    crate::leanh::lean_dec(v___y_5607_);
    crate::leanh::lean_dec_ref(v___y_5606_);
    crate::leanh::lean_dec(v___y_5605_);
    crate::leanh::lean_dec_ref(v___y_5604_);
    crate::leanh::lean_dec(v___y_5603_);
    crate::leanh::lean_dec_ref(v___y_5602_);
    crate::leanh::lean_dec(v___y_5601_);
    return v_res_5611_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lam__0(
    mut v_a_5612_: *mut crate::leanh::LeanObject,
    mut v_generation_5613_: *mut crate::leanh::LeanObject,
    mut v___y_5614_: *mut crate::leanh::LeanObject,
    mut v___y_5615_: *mut crate::leanh::LeanObject,
    mut v___y_5616_: *mut crate::leanh::LeanObject,
    mut v___y_5617_: *mut crate::leanh::LeanObject,
    mut v___y_5618_: *mut crate::leanh::LeanObject,
    mut v___y_5619_: *mut crate::leanh::LeanObject,
    mut v___y_5620_: *mut crate::leanh::LeanObject,
    mut v___y_5621_: *mut crate::leanh::LeanObject,
    mut v___y_5622_: *mut crate::leanh::LeanObject,
    mut v___y_5623_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5625_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5626_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5627_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5628_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5629_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5630_: u8 = 0;
    let mut v___x_5631_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5632_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5633_: u8 = 0;
    let mut v___x_5634_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5635_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5636_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5637_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5638_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5639_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5640_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5641_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_expr_5642_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5643_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5645_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5646_: u8 = 0;
    let mut v___x_5647_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5648_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5650_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5651_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5652_: u8 = 0;
    let mut v_unused_5653_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5654_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5656_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5657_: u8 = 0;
    let mut v___x_5659_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5660_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5661_: u8 = 0;
    let mut v_a_5662_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5664_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5665_: u8 = 0;
    let mut v___x_5667_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5668_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5669_: u8 = 0;
    let mut v_a_5670_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5672_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5673_: u8 = 0;
    let mut v___x_5675_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5676_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5677_: u8 = 0;
    let mut v_a_5678_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5680_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5681_: u8 = 0;
    let mut v___x_5683_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5684_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5685_: u8 = 0;
    let mut v_a_5686_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5688_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5689_: u8 = 0;
    let mut v___x_5691_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5692_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5693_: u8 = 0;
    let mut v___x_5694_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5695_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5696_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5697_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mvarId_5698_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5699_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5700_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5701_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5703_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5704_: u8 = 0;
    let mut v___x_5705_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toGoalState_5706_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5708_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5709_: u8 = 0;
    let mut v___x_5711_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5712_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5714_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5715_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5716_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5717_: u8 = 0;
    let mut v_unused_5718_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5719_: u8 = 0;
    let mut v_a_5720_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5722_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5723_: u8 = 0;
    let mut v___x_5725_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5726_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5727_: u8 = 0;
    let mut v_a_5728_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5730_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5731_: u8 = 0;
    let mut v___x_5733_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5734_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5735_: u8 = 0;
    let mut v_a_5736_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5738_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5739_: u8 = 0;
    let mut v___x_5741_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5742_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5743_: u8 = 0;
    let mut v_a_5744_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5746_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5747_: u8 = 0;
    let mut v___x_5749_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5750_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5751_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                crate::leanh::lean_inc(v_a_5612_);
                v___x_5625_ = l_Lean_FVarId_getDecl___redArg(
                    v_a_5612_,
                    v___y_5620_,
                    v___y_5622_,
                    v___y_5623_,
                );
                if crate::leanh::lean_obj_tag(v___x_5625_) == 0 {
                    v_a_5626_ = crate::leanh::lean_ctor_get(v___x_5625_, 0);
                    crate::leanh::lean_inc(v_a_5626_);
                    crate::leanh::lean_dec_ref_known(v___x_5625_, 1);
                    v___x_5627_ = l_Lean_LocalDecl_type(v_a_5626_);
                    crate::leanh::lean_dec(v_a_5626_);
                    crate::leanh::lean_inc_ref(v___x_5627_);
                    v___x_5628_ = l_Lean_Meta_isProp(
                        v___x_5627_,
                        v___y_5620_,
                        v___y_5621_,
                        v___y_5622_,
                        v___y_5623_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_5628_) == 0 {
                        v_a_5629_ = crate::leanh::lean_ctor_get(v___x_5628_, 0);
                        crate::leanh::lean_inc(v_a_5629_);
                        crate::leanh::lean_dec_ref_known(v___x_5628_, 1);
                        v___x_5630_ = (crate::leanh::lean_unbox(v_a_5629_) as u8);
                        if v___x_5630_ == 0 {
                            crate::leanh::lean_dec_ref(v___x_5627_);
                            crate::leanh::lean_inc(v_a_5612_);
                            v___x_5631_ = l_Lean_FVarId_getDecl___redArg(
                                v_a_5612_,
                                v___y_5620_,
                                v___y_5622_,
                                v___y_5623_,
                            );
                            if crate::leanh::lean_obj_tag(v___x_5631_) == 0 {
                                v_a_5632_ = crate::leanh::lean_ctor_get(v___x_5631_, 0);
                                crate::leanh::lean_inc(v_a_5632_);
                                crate::leanh::lean_dec_ref_known(v___x_5631_, 1);
                                v___x_5633_ = (crate::leanh::lean_unbox(v_a_5629_) as u8);
                                crate::leanh::lean_dec(v_a_5629_);
                                v___x_5634_ = l_Lean_LocalDecl_value(v_a_5632_, v___x_5633_);
                                crate::leanh::lean_dec(v_a_5632_);
                                v___x_5635_ = l_Lean_Meta_Grind_preprocessHypothesis(
                                    v___x_5634_,
                                    v___y_5614_,
                                    v___y_5615_,
                                    v___y_5616_,
                                    v___y_5617_,
                                    v___y_5618_,
                                    v___y_5619_,
                                    v___y_5620_,
                                    v___y_5621_,
                                    v___y_5622_,
                                    v___y_5623_,
                                );
                                if crate::leanh::lean_obj_tag(v___x_5635_) == 0 {
                                    v_a_5636_ = crate::leanh::lean_ctor_get(v___x_5635_, 0);
                                    crate::leanh::lean_inc(v_a_5636_);
                                    crate::leanh::lean_dec_ref_known(v___x_5635_, 1);
                                    crate::leanh::lean_inc(v_a_5612_);
                                    v___x_5637_ = l_Lean_mkFVar(v_a_5612_);
                                    v___x_5638_ = l_Lean_Meta_Sym_shareCommon___redArg(
                                        v___x_5637_,
                                        v___y_5619_,
                                    );
                                    if crate::leanh::lean_obj_tag(v___x_5638_) == 0 {
                                        v_a_5639_ = crate::leanh::lean_ctor_get(v___x_5638_, 0);
                                        crate::leanh::lean_inc(v_a_5639_);
                                        crate::leanh::lean_dec_ref_known(v___x_5638_, 1);
                                        crate::leanh::lean_inc(v_a_5636_);
                                        v___x_5640_ = l_Lean_Meta_Simp_Result_getProof(
                                            v_a_5636_,
                                            v___y_5620_,
                                            v___y_5621_,
                                            v___y_5622_,
                                            v___y_5623_,
                                        );
                                        if crate::leanh::lean_obj_tag(v___x_5640_) == 0 {
                                            v_a_5641_ = crate::leanh::lean_ctor_get(v___x_5640_, 0);
                                            crate::leanh::lean_inc(v_a_5641_);
                                            crate::leanh::lean_dec_ref_known(v___x_5640_, 1);
                                            v_expr_5642_ =
                                                crate::leanh::lean_ctor_get(v_a_5636_, 0);
                                            crate::leanh::lean_inc_ref(v_expr_5642_);
                                            crate::leanh::lean_dec(v_a_5636_);
                                            v___x_5643_ = l_Lean_Meta_Grind_addNewEq(
                                                v_a_5639_,
                                                v_expr_5642_,
                                                v_a_5641_,
                                                v_generation_5613_,
                                                v___y_5614_,
                                                v___y_5615_,
                                                v___y_5616_,
                                                v___y_5617_,
                                                v___y_5618_,
                                                v___y_5619_,
                                                v___y_5620_,
                                                v___y_5621_,
                                                v___y_5622_,
                                                v___y_5623_,
                                            );
                                            if crate::leanh::lean_obj_tag(v___x_5643_) == 0 {
                                                v_isSharedCheck_5652_ =
                                                    (!crate::leanh::lean_is_exclusive(v___x_5643_))
                                                        as u8;
                                                if v_isSharedCheck_5652_ == 0 {
                                                    v_unused_5653_ =
                                                        crate::leanh::lean_ctor_get(v___x_5643_, 0);
                                                    crate::leanh::lean_dec(v_unused_5653_);
                                                    v___x_5645_ = v___x_5643_;
                                                    v_isShared_5646_ = v_isSharedCheck_5652_;
                                                    state = 1;
                                                    continue;
                                                } else {
                                                    crate::leanh::lean_dec(v___x_5643_);
                                                    v___x_5645_ = crate::leanh::lean_box(0);
                                                    v_isShared_5646_ = v_isSharedCheck_5652_;
                                                    state = 1;
                                                    continue;
                                                }
                                            } else {
                                                crate::leanh::lean_dec(v_a_5612_);
                                                v_a_5654_ =
                                                    crate::leanh::lean_ctor_get(v___x_5643_, 0);
                                                v_isSharedCheck_5661_ =
                                                    (!crate::leanh::lean_is_exclusive(v___x_5643_))
                                                        as u8;
                                                if v_isSharedCheck_5661_ == 0 {
                                                    v___x_5656_ = v___x_5643_;
                                                    v_isShared_5657_ = v_isSharedCheck_5661_;
                                                    state = 3;
                                                    continue;
                                                } else {
                                                    crate::leanh::lean_inc(v_a_5654_);
                                                    crate::leanh::lean_dec(v___x_5643_);
                                                    v___x_5656_ = crate::leanh::lean_box(0);
                                                    v_isShared_5657_ = v_isSharedCheck_5661_;
                                                    state = 3;
                                                    continue;
                                                }
                                            }
                                        } else {
                                            crate::leanh::lean_dec(v_a_5639_);
                                            crate::leanh::lean_dec(v_a_5636_);
                                            crate::leanh::lean_dec(v_generation_5613_);
                                            crate::leanh::lean_dec(v_a_5612_);
                                            v_a_5662_ = crate::leanh::lean_ctor_get(v___x_5640_, 0);
                                            v_isSharedCheck_5669_ =
                                                (!crate::leanh::lean_is_exclusive(v___x_5640_))
                                                    as u8;
                                            if v_isSharedCheck_5669_ == 0 {
                                                v___x_5664_ = v___x_5640_;
                                                v_isShared_5665_ = v_isSharedCheck_5669_;
                                                state = 5;
                                                continue;
                                            } else {
                                                crate::leanh::lean_inc(v_a_5662_);
                                                crate::leanh::lean_dec(v___x_5640_);
                                                v___x_5664_ = crate::leanh::lean_box(0);
                                                v_isShared_5665_ = v_isSharedCheck_5669_;
                                                state = 5;
                                                continue;
                                            }
                                        }
                                    } else {
                                        crate::leanh::lean_dec(v_a_5636_);
                                        crate::leanh::lean_dec(v_generation_5613_);
                                        crate::leanh::lean_dec(v_a_5612_);
                                        v_a_5670_ = crate::leanh::lean_ctor_get(v___x_5638_, 0);
                                        v_isSharedCheck_5677_ =
                                            (!crate::leanh::lean_is_exclusive(v___x_5638_)) as u8;
                                        if v_isSharedCheck_5677_ == 0 {
                                            v___x_5672_ = v___x_5638_;
                                            v_isShared_5673_ = v_isSharedCheck_5677_;
                                            state = 7;
                                            continue;
                                        } else {
                                            crate::leanh::lean_inc(v_a_5670_);
                                            crate::leanh::lean_dec(v___x_5638_);
                                            v___x_5672_ = crate::leanh::lean_box(0);
                                            v_isShared_5673_ = v_isSharedCheck_5677_;
                                            state = 7;
                                            continue;
                                        }
                                    }
                                } else {
                                    crate::leanh::lean_dec(v_generation_5613_);
                                    crate::leanh::lean_dec(v_a_5612_);
                                    v_a_5678_ = crate::leanh::lean_ctor_get(v___x_5635_, 0);
                                    v_isSharedCheck_5685_ =
                                        (!crate::leanh::lean_is_exclusive(v___x_5635_)) as u8;
                                    if v_isSharedCheck_5685_ == 0 {
                                        v___x_5680_ = v___x_5635_;
                                        v_isShared_5681_ = v_isSharedCheck_5685_;
                                        state = 9;
                                        continue;
                                    } else {
                                        crate::leanh::lean_inc(v_a_5678_);
                                        crate::leanh::lean_dec(v___x_5635_);
                                        v___x_5680_ = crate::leanh::lean_box(0);
                                        v_isShared_5681_ = v_isSharedCheck_5685_;
                                        state = 9;
                                        continue;
                                    }
                                }
                            } else {
                                crate::leanh::lean_dec(v_a_5629_);
                                crate::leanh::lean_dec(v_generation_5613_);
                                crate::leanh::lean_dec(v_a_5612_);
                                v_a_5686_ = crate::leanh::lean_ctor_get(v___x_5631_, 0);
                                v_isSharedCheck_5693_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_5631_)) as u8;
                                if v_isSharedCheck_5693_ == 0 {
                                    v___x_5688_ = v___x_5631_;
                                    v_isShared_5689_ = v_isSharedCheck_5693_;
                                    state = 11;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_a_5686_);
                                    crate::leanh::lean_dec(v___x_5631_);
                                    v___x_5688_ = crate::leanh::lean_box(0);
                                    v_isShared_5689_ = v_isSharedCheck_5693_;
                                    state = 11;
                                    continue;
                                }
                            }
                        } else {
                            crate::leanh::lean_dec(v_a_5629_);
                            crate::leanh::lean_dec(v_generation_5613_);
                            v___x_5694_ = lean_st_ref_get(v___y_5614_);
                            v___x_5695_ = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkBaseName___closed__3;
                            crate::leanh::lean_inc_ref(v___x_5627_);
                            v___x_5696_ = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName(v___x_5695_, v___x_5627_, v___y_5614_, v___y_5615_, v___y_5616_, v___y_5617_, v___y_5618_, v___y_5619_, v___y_5620_, v___y_5621_, v___y_5622_, v___y_5623_);
                            if crate::leanh::lean_obj_tag(v___x_5696_) == 0 {
                                v_a_5697_ = crate::leanh::lean_ctor_get(v___x_5696_, 0);
                                crate::leanh::lean_inc(v_a_5697_);
                                crate::leanh::lean_dec_ref_known(v___x_5696_, 1);
                                v_mvarId_5698_ = crate::leanh::lean_ctor_get(v___x_5694_, 1);
                                crate::leanh::lean_inc(v_mvarId_5698_);
                                crate::leanh::lean_dec(v___x_5694_);
                                v___x_5699_ = l_Lean_mkFVar(v_a_5612_);
                                v___x_5700_ = l_Lean_MVarId_assert(
                                    v_mvarId_5698_,
                                    v_a_5697_,
                                    v___x_5627_,
                                    v___x_5699_,
                                    v___y_5620_,
                                    v___y_5621_,
                                    v___y_5622_,
                                    v___y_5623_,
                                );
                                if crate::leanh::lean_obj_tag(v___x_5700_) == 0 {
                                    v_a_5701_ = crate::leanh::lean_ctor_get(v___x_5700_, 0);
                                    v_isSharedCheck_5719_ =
                                        (!crate::leanh::lean_is_exclusive(v___x_5700_)) as u8;
                                    if v_isSharedCheck_5719_ == 0 {
                                        v___x_5703_ = v___x_5700_;
                                        v_isShared_5704_ = v_isSharedCheck_5719_;
                                        state = 13;
                                        continue;
                                    } else {
                                        crate::leanh::lean_inc(v_a_5701_);
                                        crate::leanh::lean_dec(v___x_5700_);
                                        v___x_5703_ = crate::leanh::lean_box(0);
                                        v_isShared_5704_ = v_isSharedCheck_5719_;
                                        state = 13;
                                        continue;
                                    }
                                } else {
                                    v_a_5720_ = crate::leanh::lean_ctor_get(v___x_5700_, 0);
                                    v_isSharedCheck_5727_ =
                                        (!crate::leanh::lean_is_exclusive(v___x_5700_)) as u8;
                                    if v_isSharedCheck_5727_ == 0 {
                                        v___x_5722_ = v___x_5700_;
                                        v_isShared_5723_ = v_isSharedCheck_5727_;
                                        state = 17;
                                        continue;
                                    } else {
                                        crate::leanh::lean_inc(v_a_5720_);
                                        crate::leanh::lean_dec(v___x_5700_);
                                        v___x_5722_ = crate::leanh::lean_box(0);
                                        v_isShared_5723_ = v_isSharedCheck_5727_;
                                        state = 17;
                                        continue;
                                    }
                                }
                            } else {
                                crate::leanh::lean_dec(v___x_5694_);
                                crate::leanh::lean_dec_ref(v___x_5627_);
                                crate::leanh::lean_dec(v_a_5612_);
                                v_a_5728_ = crate::leanh::lean_ctor_get(v___x_5696_, 0);
                                v_isSharedCheck_5735_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_5696_)) as u8;
                                if v_isSharedCheck_5735_ == 0 {
                                    v___x_5730_ = v___x_5696_;
                                    v_isShared_5731_ = v_isSharedCheck_5735_;
                                    state = 19;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_a_5728_);
                                    crate::leanh::lean_dec(v___x_5696_);
                                    v___x_5730_ = crate::leanh::lean_box(0);
                                    v_isShared_5731_ = v_isSharedCheck_5735_;
                                    state = 19;
                                    continue;
                                }
                            }
                        }
                    } else {
                        crate::leanh::lean_dec_ref(v___x_5627_);
                        crate::leanh::lean_dec(v_generation_5613_);
                        crate::leanh::lean_dec(v_a_5612_);
                        v_a_5736_ = crate::leanh::lean_ctor_get(v___x_5628_, 0);
                        v_isSharedCheck_5743_ =
                            (!crate::leanh::lean_is_exclusive(v___x_5628_)) as u8;
                        if v_isSharedCheck_5743_ == 0 {
                            v___x_5738_ = v___x_5628_;
                            v_isShared_5739_ = v_isSharedCheck_5743_;
                            state = 21;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_5736_);
                            crate::leanh::lean_dec(v___x_5628_);
                            v___x_5738_ = crate::leanh::lean_box(0);
                            v_isShared_5739_ = v_isSharedCheck_5743_;
                            state = 21;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec(v_generation_5613_);
                    crate::leanh::lean_dec(v_a_5612_);
                    v_a_5744_ = crate::leanh::lean_ctor_get(v___x_5625_, 0);
                    v_isSharedCheck_5751_ = (!crate::leanh::lean_is_exclusive(v___x_5625_)) as u8;
                    if v_isSharedCheck_5751_ == 0 {
                        v___x_5746_ = v___x_5625_;
                        v_isShared_5747_ = v_isSharedCheck_5751_;
                        state = 23;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_5744_);
                        crate::leanh::lean_dec(v___x_5625_);
                        v___x_5746_ = crate::leanh::lean_box(0);
                        v_isShared_5747_ = v_isSharedCheck_5751_;
                        state = 23;
                        continue;
                    }
                }
            }
            1 => {
                v___x_5647_ = lean_st_ref_get(v___y_5614_);
                v___x_5648_ = crate::leanh::lean_alloc_ctor(3, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_5648_, 0, v_a_5612_);
                crate::leanh::lean_ctor_set(v___x_5648_, 1, v___x_5647_);
                if v_isShared_5646_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5645_, 0, v___x_5648_);
                    v___x_5650_ = v___x_5645_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5651_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5651_, 0, v___x_5648_);
                    v___x_5650_ = v_reuseFailAlloc_5651_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_5650_;
            }
            3 => {
                if v_isShared_5657_ == 0 {
                    v___x_5659_ = v___x_5656_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_5660_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5660_, 0, v_a_5654_);
                    v___x_5659_ = v_reuseFailAlloc_5660_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_5659_;
            }
            5 => {
                if v_isShared_5665_ == 0 {
                    v___x_5667_ = v___x_5664_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_5668_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5668_, 0, v_a_5662_);
                    v___x_5667_ = v_reuseFailAlloc_5668_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_5667_;
            }
            7 => {
                if v_isShared_5673_ == 0 {
                    v___x_5675_ = v___x_5672_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_5676_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5676_, 0, v_a_5670_);
                    v___x_5675_ = v_reuseFailAlloc_5676_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_5675_;
            }
            9 => {
                if v_isShared_5681_ == 0 {
                    v___x_5683_ = v___x_5680_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_5684_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5684_, 0, v_a_5678_);
                    v___x_5683_ = v_reuseFailAlloc_5684_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_5683_;
            }
            11 => {
                if v_isShared_5689_ == 0 {
                    v___x_5691_ = v___x_5688_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_5692_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5692_, 0, v_a_5686_);
                    v___x_5691_ = v_reuseFailAlloc_5692_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                return v___x_5691_;
            }
            13 => {
                v___x_5705_ = lean_st_ref_get(v___y_5614_);
                v_toGoalState_5706_ = crate::leanh::lean_ctor_get(v___x_5705_, 0);
                v_isSharedCheck_5717_ = (!crate::leanh::lean_is_exclusive(v___x_5705_)) as u8;
                if v_isSharedCheck_5717_ == 0 {
                    v_unused_5718_ = crate::leanh::lean_ctor_get(v___x_5705_, 1);
                    crate::leanh::lean_dec(v_unused_5718_);
                    v___x_5708_ = v___x_5705_;
                    v_isShared_5709_ = v_isSharedCheck_5717_;
                    state = 14;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_toGoalState_5706_);
                    crate::leanh::lean_dec(v___x_5705_);
                    v___x_5708_ = crate::leanh::lean_box(0);
                    v_isShared_5709_ = v_isSharedCheck_5717_;
                    state = 14;
                    continue;
                }
            }
            14 => {
                if v_isShared_5709_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5708_, 1, v_a_5701_);
                    v___x_5711_ = v___x_5708_;
                    state = 15;
                    continue;
                } else {
                    v_reuseFailAlloc_5716_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5716_, 0, v_toGoalState_5706_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5716_, 1, v_a_5701_);
                    v___x_5711_ = v_reuseFailAlloc_5716_;
                    state = 15;
                    continue;
                }
            }
            15 => {
                v___x_5712_ = crate::leanh::lean_alloc_ctor(2, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_5712_, 0, v___x_5711_);
                if v_isShared_5704_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5703_, 0, v___x_5712_);
                    v___x_5714_ = v___x_5703_;
                    state = 16;
                    continue;
                } else {
                    v_reuseFailAlloc_5715_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5715_, 0, v___x_5712_);
                    v___x_5714_ = v_reuseFailAlloc_5715_;
                    state = 16;
                    continue;
                }
            }
            16 => {
                return v___x_5714_;
            }
            17 => {
                if v_isShared_5723_ == 0 {
                    v___x_5725_ = v___x_5722_;
                    state = 18;
                    continue;
                } else {
                    v_reuseFailAlloc_5726_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5726_, 0, v_a_5720_);
                    v___x_5725_ = v_reuseFailAlloc_5726_;
                    state = 18;
                    continue;
                }
            }
            18 => {
                return v___x_5725_;
            }
            19 => {
                if v_isShared_5731_ == 0 {
                    v___x_5733_ = v___x_5730_;
                    state = 20;
                    continue;
                } else {
                    v_reuseFailAlloc_5734_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5734_, 0, v_a_5728_);
                    v___x_5733_ = v_reuseFailAlloc_5734_;
                    state = 20;
                    continue;
                }
            }
            20 => {
                return v___x_5733_;
            }
            21 => {
                if v_isShared_5739_ == 0 {
                    v___x_5741_ = v___x_5738_;
                    state = 22;
                    continue;
                } else {
                    v_reuseFailAlloc_5742_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5742_, 0, v_a_5736_);
                    v___x_5741_ = v_reuseFailAlloc_5742_;
                    state = 22;
                    continue;
                }
            }
            22 => {
                return v___x_5741_;
            }
            23 => {
                if v_isShared_5747_ == 0 {
                    v___x_5749_ = v___x_5746_;
                    state = 24;
                    continue;
                } else {
                    v_reuseFailAlloc_5750_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5750_, 0, v_a_5744_);
                    v___x_5749_ = v_reuseFailAlloc_5750_;
                    state = 24;
                    continue;
                }
            }
            24 => {
                return v___x_5749_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lam__0___boxed(
    mut v_a_5752_: *mut crate::leanh::LeanObject,
    mut v_generation_5753_: *mut crate::leanh::LeanObject,
    mut v___y_5754_: *mut crate::leanh::LeanObject,
    mut v___y_5755_: *mut crate::leanh::LeanObject,
    mut v___y_5756_: *mut crate::leanh::LeanObject,
    mut v___y_5757_: *mut crate::leanh::LeanObject,
    mut v___y_5758_: *mut crate::leanh::LeanObject,
    mut v___y_5759_: *mut crate::leanh::LeanObject,
    mut v___y_5760_: *mut crate::leanh::LeanObject,
    mut v___y_5761_: *mut crate::leanh::LeanObject,
    mut v___y_5762_: *mut crate::leanh::LeanObject,
    mut v___y_5763_: *mut crate::leanh::LeanObject,
    mut v___y_5764_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5765_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5765_ = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lam__0(
        v_a_5752_,
        v_generation_5753_,
        v___y_5754_,
        v___y_5755_,
        v___y_5756_,
        v___y_5757_,
        v___y_5758_,
        v___y_5759_,
        v___y_5760_,
        v___y_5761_,
        v___y_5762_,
        v___y_5763_,
    );
    crate::leanh::lean_dec(v___y_5763_);
    crate::leanh::lean_dec_ref(v___y_5762_);
    crate::leanh::lean_dec(v___y_5761_);
    crate::leanh::lean_dec_ref(v___y_5760_);
    crate::leanh::lean_dec(v___y_5759_);
    crate::leanh::lean_dec_ref(v___y_5758_);
    crate::leanh::lean_dec(v___y_5757_);
    crate::leanh::lean_dec_ref(v___y_5756_);
    crate::leanh::lean_dec(v___y_5755_);
    crate::leanh::lean_dec(v___y_5754_);
    return v_res_5765_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__1_spec__1_spec__3_spec__6_spec__7___redArg(
    mut v_x_5766_: *mut crate::leanh::LeanObject,
    mut v_x_5767_: *mut crate::leanh::LeanObject,
    mut v_x_5768_: *mut crate::leanh::LeanObject,
    mut v_x_5769_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_ks_5770_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_vs_5771_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5773_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5774_: u8 = 0;
    let mut v___x_5775_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5776_: u8 = 0;
    let mut v___x_5777_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5778_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5780_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5781_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_x27_5782_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5783_: u8 = 0;
    let mut v___x_5785_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5786_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5787_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5789_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5790_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5791_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5793_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5794_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5795_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ks_5770_ = crate::leanh::lean_ctor_get(v_x_5766_, 0);
                v_vs_5771_ = crate::leanh::lean_ctor_get(v_x_5766_, 1);
                v_isSharedCheck_5795_ = (!crate::leanh::lean_is_exclusive(v_x_5766_)) as u8;
                if v_isSharedCheck_5795_ == 0 {
                    v___x_5773_ = v_x_5766_;
                    v_isShared_5774_ = v_isSharedCheck_5795_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_vs_5771_);
                    crate::leanh::lean_inc(v_ks_5770_);
                    crate::leanh::lean_dec(v_x_5766_);
                    v___x_5773_ = crate::leanh::lean_box(0);
                    v_isShared_5774_ = v_isSharedCheck_5795_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_5775_ = lean_array_get_size(v_ks_5770_);
                v___x_5776_ = lean_nat_dec_lt(v_x_5767_, v___x_5775_);
                if v___x_5776_ == 0 {
                    crate::leanh::lean_dec(v_x_5767_);
                    v___x_5777_ = lean_array_push(v_ks_5770_, v_x_5768_);
                    v___x_5778_ = lean_array_push(v_vs_5771_, v_x_5769_);
                    if v_isShared_5774_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_5773_, 1, v___x_5778_);
                        crate::leanh::lean_ctor_set(v___x_5773_, 0, v___x_5777_);
                        v___x_5780_ = v___x_5773_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_5781_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_5781_, 0, v___x_5777_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_5781_, 1, v___x_5778_);
                        v___x_5780_ = v_reuseFailAlloc_5781_;
                        state = 2;
                        continue;
                    }
                } else {
                    v_k_x27_5782_ = lean_array_fget_borrowed(v_ks_5770_, v_x_5767_);
                    v___x_5783_ = l_Lean_instBEqMVarId_beq(v_x_5768_, v_k_x27_5782_);
                    if v___x_5783_ == 0 {
                        if v_isShared_5774_ == 0 {
                            v___x_5785_ = v___x_5773_;
                            state = 3;
                            continue;
                        } else {
                            v_reuseFailAlloc_5789_ =
                                crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_5789_, 0, v_ks_5770_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_5789_, 1, v_vs_5771_);
                            v___x_5785_ = v_reuseFailAlloc_5789_;
                            state = 3;
                            continue;
                        }
                    } else {
                        v___x_5790_ = lean_array_fset(v_ks_5770_, v_x_5767_, v_x_5768_);
                        v___x_5791_ = lean_array_fset(v_vs_5771_, v_x_5767_, v_x_5769_);
                        crate::leanh::lean_dec(v_x_5767_);
                        if v_isShared_5774_ == 0 {
                            crate::leanh::lean_ctor_set(v___x_5773_, 1, v___x_5791_);
                            crate::leanh::lean_ctor_set(v___x_5773_, 0, v___x_5790_);
                            v___x_5793_ = v___x_5773_;
                            state = 4;
                            continue;
                        } else {
                            v_reuseFailAlloc_5794_ =
                                crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_5794_, 0, v___x_5790_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_5794_, 1, v___x_5791_);
                            v___x_5793_ = v_reuseFailAlloc_5794_;
                            state = 4;
                            continue;
                        }
                    }
                }
            }
            2 => {
                return v___x_5780_;
            }
            3 => {
                v___x_5786_ = crate::leanh::lean_unsigned_to_nat(1);
                v___x_5787_ = lean_nat_add(v_x_5767_, v___x_5786_);
                crate::leanh::lean_dec(v_x_5767_);
                v_x_5766_ = v___x_5785_;
                v_x_5767_ = v___x_5787_;
                state = 0;
                continue;
            }
            4 => {
                return v___x_5793_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__1_spec__1_spec__3_spec__6___redArg(
    mut v_n_5796_: *mut crate::leanh::LeanObject,
    mut v_k_5797_: *mut crate::leanh::LeanObject,
    mut v_v_5798_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5799_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5800_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5799_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_5800_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__1_spec__1_spec__3_spec__6_spec__7___redArg(v_n_5796_, v___x_5799_, v_k_5797_, v_v_5798_);
    return v___x_5800_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__1_spec__1_spec__3___redArg(
    mut v_x_5801_: *mut crate::leanh::LeanObject,
    mut v_x_5802_: usize,
    mut v_x_5803_: usize,
    mut v_x_5804_: *mut crate::leanh::LeanObject,
    mut v_x_5805_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_es_5806_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5807_: usize = 0;
    let mut v___x_5808_: usize = 0;
    let mut v___x_5809_: usize = 0;
    let mut v___x_5810_: usize = 0;
    let mut v_j_5811_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5812_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5813_: u8 = 0;
    let mut v___x_5815_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5816_: u8 = 0;
    let mut v_v_5817_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5818_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_xs_x27_5819_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5821_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5822_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5824_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5825_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_key_5826_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_5827_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5829_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5830_: u8 = 0;
    let mut v___x_5831_: u8 = 0;
    let mut v___x_5832_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5833_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5835_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5836_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5837_: u8 = 0;
    let mut v_node_5838_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5840_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5841_: u8 = 0;
    let mut v___x_5842_: usize = 0;
    let mut v___x_5843_: usize = 0;
    let mut v___x_5844_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5846_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5847_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5848_: u8 = 0;
    let mut v___x_5849_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5850_: u8 = 0;
    let mut v_unused_5851_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ks_5852_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_vs_5853_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5855_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5856_: u8 = 0;
    let mut v___x_5858_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_newNode_5859_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5861_: u8 = 0;
    let mut v_ks_5862_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_vs_5863_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5864_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5865_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5866_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5867_: usize = 0;
    let mut v___x_5868_: u8 = 0;
    let mut v___x_5869_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5870_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5871_: u8 = 0;
    let mut v_reuseFailAlloc_5872_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5873_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_5801_) == 0 {
                    v_es_5806_ = crate::leanh::lean_ctor_get(v_x_5801_, 0);
                    v___x_5807_ = 5usize;
                    v___x_5808_ = 1usize;
                    v___x_5809_ = crate::leanh::lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__1_spec__2___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__1_spec__2___redArg___closed__1_once), _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__1_spec__2___redArg___closed__1);
                    v___x_5810_ = lean_usize_land(v_x_5802_, v___x_5809_);
                    v_j_5811_ = lean_usize_to_nat(v___x_5810_);
                    v___x_5812_ = lean_array_get_size(v_es_5806_);
                    v___x_5813_ = lean_nat_dec_lt(v_j_5811_, v___x_5812_);
                    if v___x_5813_ == 0 {
                        crate::leanh::lean_dec(v_j_5811_);
                        crate::leanh::lean_dec(v_x_5805_);
                        crate::leanh::lean_dec(v_x_5804_);
                        return v_x_5801_;
                    } else {
                        crate::leanh::lean_inc_ref(v_es_5806_);
                        v_isSharedCheck_5850_ = (!crate::leanh::lean_is_exclusive(v_x_5801_)) as u8;
                        if v_isSharedCheck_5850_ == 0 {
                            v_unused_5851_ = crate::leanh::lean_ctor_get(v_x_5801_, 0);
                            crate::leanh::lean_dec(v_unused_5851_);
                            v___x_5815_ = v_x_5801_;
                            v_isShared_5816_ = v_isSharedCheck_5850_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_dec(v_x_5801_);
                            v___x_5815_ = crate::leanh::lean_box(0);
                            v_isShared_5816_ = v_isSharedCheck_5850_;
                            state = 1;
                            continue;
                        }
                    }
                } else {
                    v_ks_5852_ = crate::leanh::lean_ctor_get(v_x_5801_, 0);
                    v_vs_5853_ = crate::leanh::lean_ctor_get(v_x_5801_, 1);
                    v_isSharedCheck_5873_ = (!crate::leanh::lean_is_exclusive(v_x_5801_)) as u8;
                    if v_isSharedCheck_5873_ == 0 {
                        v___x_5855_ = v_x_5801_;
                        v_isShared_5856_ = v_isSharedCheck_5873_;
                        state = 8;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_vs_5853_);
                        crate::leanh::lean_inc(v_ks_5852_);
                        crate::leanh::lean_dec(v_x_5801_);
                        v___x_5855_ = crate::leanh::lean_box(0);
                        v_isShared_5856_ = v_isSharedCheck_5873_;
                        state = 8;
                        continue;
                    }
                }
            }
            1 => {
                v_v_5817_ = lean_array_fget(v_es_5806_, v_j_5811_);
                v___x_5818_ = crate::leanh::lean_box(0);
                v_xs_x27_5819_ = lean_array_fset(v_es_5806_, v_j_5811_, v___x_5818_);
                match crate::leanh::lean_obj_tag(v_v_5817_) {
                    0 => {
                        v_key_5826_ = crate::leanh::lean_ctor_get(v_v_5817_, 0);
                        v_val_5827_ = crate::leanh::lean_ctor_get(v_v_5817_, 1);
                        v_isSharedCheck_5837_ = (!crate::leanh::lean_is_exclusive(v_v_5817_)) as u8;
                        if v_isSharedCheck_5837_ == 0 {
                            v___x_5829_ = v_v_5817_;
                            v_isShared_5830_ = v_isSharedCheck_5837_;
                            state = 4;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_val_5827_);
                            crate::leanh::lean_inc(v_key_5826_);
                            crate::leanh::lean_dec(v_v_5817_);
                            v___x_5829_ = crate::leanh::lean_box(0);
                            v_isShared_5830_ = v_isSharedCheck_5837_;
                            state = 4;
                            continue;
                        }
                    }
                    1 => {
                        v_node_5838_ = crate::leanh::lean_ctor_get(v_v_5817_, 0);
                        v_isSharedCheck_5848_ = (!crate::leanh::lean_is_exclusive(v_v_5817_)) as u8;
                        if v_isSharedCheck_5848_ == 0 {
                            v___x_5840_ = v_v_5817_;
                            v_isShared_5841_ = v_isSharedCheck_5848_;
                            state = 6;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_node_5838_);
                            crate::leanh::lean_dec(v_v_5817_);
                            v___x_5840_ = crate::leanh::lean_box(0);
                            v_isShared_5841_ = v_isSharedCheck_5848_;
                            state = 6;
                            continue;
                        }
                    }
                    _ => {
                        v___x_5849_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_5849_, 0, v_x_5804_);
                        crate::leanh::lean_ctor_set(v___x_5849_, 1, v_x_5805_);
                        v___y_5821_ = v___x_5849_;
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                v___x_5822_ = lean_array_fset(v_xs_x27_5819_, v_j_5811_, v___y_5821_);
                crate::leanh::lean_dec(v_j_5811_);
                if v_isShared_5816_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5815_, 0, v___x_5822_);
                    v___x_5824_ = v___x_5815_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_5825_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5825_, 0, v___x_5822_);
                    v___x_5824_ = v_reuseFailAlloc_5825_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_5824_;
            }
            4 => {
                v___x_5831_ = l_Lean_instBEqMVarId_beq(v_x_5804_, v_key_5826_);
                if v___x_5831_ == 0 {
                    crate::leanh::lean_del_object(v___x_5829_);
                    v___x_5832_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(
                        v_key_5826_,
                        v_val_5827_,
                        v_x_5804_,
                        v_x_5805_,
                    );
                    v___x_5833_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_5833_, 0, v___x_5832_);
                    v___y_5821_ = v___x_5833_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_dec(v_val_5827_);
                    crate::leanh::lean_dec(v_key_5826_);
                    if v_isShared_5830_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_5829_, 1, v_x_5805_);
                        crate::leanh::lean_ctor_set(v___x_5829_, 0, v_x_5804_);
                        v___x_5835_ = v___x_5829_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_5836_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_5836_, 0, v_x_5804_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_5836_, 1, v_x_5805_);
                        v___x_5835_ = v_reuseFailAlloc_5836_;
                        state = 5;
                        continue;
                    }
                }
            }
            5 => {
                v___y_5821_ = v___x_5835_;
                state = 2;
                continue;
            }
            6 => {
                v___x_5842_ = lean_usize_shift_right(v_x_5802_, v___x_5807_);
                v___x_5843_ = lean_usize_add(v_x_5803_, v___x_5808_);
                v___x_5844_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__1_spec__1_spec__3___redArg(v_node_5838_, v___x_5842_, v___x_5843_, v_x_5804_, v_x_5805_);
                if v_isShared_5841_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5840_, 0, v___x_5844_);
                    v___x_5846_ = v___x_5840_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_5847_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5847_, 0, v___x_5844_);
                    v___x_5846_ = v_reuseFailAlloc_5847_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                v___y_5821_ = v___x_5846_;
                state = 2;
                continue;
            }
            8 => {
                if v_isShared_5856_ == 0 {
                    v___x_5858_ = v___x_5855_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_5872_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5872_, 0, v_ks_5852_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5872_, 1, v_vs_5853_);
                    v___x_5858_ = v_reuseFailAlloc_5872_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                v_newNode_5859_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__1_spec__1_spec__3_spec__6___redArg(v___x_5858_, v_x_5804_, v_x_5805_);
                v___x_5867_ = 7usize;
                v___x_5868_ = lean_usize_dec_le(v___x_5867_, v_x_5803_);
                if v___x_5868_ == 0 {
                    v___x_5869_ =
                        l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_5859_);
                    v___x_5870_ = crate::leanh::lean_unsigned_to_nat(4);
                    v___x_5871_ = lean_nat_dec_lt(v___x_5869_, v___x_5870_);
                    crate::leanh::lean_dec(v___x_5869_);
                    v___y_5861_ = v___x_5871_;
                    state = 10;
                    continue;
                } else {
                    v___y_5861_ = v___x_5868_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                if v___y_5861_ == 0 {
                    v_ks_5862_ = crate::leanh::lean_ctor_get(v_newNode_5859_, 0);
                    crate::leanh::lean_inc_ref(v_ks_5862_);
                    v_vs_5863_ = crate::leanh::lean_ctor_get(v_newNode_5859_, 1);
                    crate::leanh::lean_inc_ref(v_vs_5863_);
                    crate::leanh::lean_dec_ref(v_newNode_5859_);
                    v___x_5864_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___x_5865_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__0_spec__0___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__0_spec__0___redArg___closed__0_once), _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__0_spec__0___redArg___closed__0);
                    v___x_5866_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__1_spec__1_spec__3_spec__7___redArg(v_x_5803_, v_ks_5862_, v_vs_5863_, v___x_5864_, v___x_5865_);
                    crate::leanh::lean_dec_ref(v_vs_5863_);
                    crate::leanh::lean_dec_ref(v_ks_5862_);
                    return v___x_5866_;
                } else {
                    return v_newNode_5859_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__1_spec__1_spec__3_spec__7___redArg(
    mut v_depth_5874_: usize,
    mut v_keys_5875_: *mut crate::leanh::LeanObject,
    mut v_vals_5876_: *mut crate::leanh::LeanObject,
    mut v_i_5877_: *mut crate::leanh::LeanObject,
    mut v_entries_5878_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5879_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5880_: u8 = 0;
    let mut v_k_5881_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_5882_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5883_: u64 = 0;
    let mut v_h_5884_: usize = 0;
    let mut v___x_5885_: usize = 0;
    let mut v___x_5886_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5887_: usize = 0;
    let mut v___x_5888_: usize = 0;
    let mut v___x_5889_: usize = 0;
    let mut v_h_5890_: usize = 0;
    let mut v___x_5891_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5892_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5879_ = lean_array_get_size(v_keys_5875_);
                v___x_5880_ = lean_nat_dec_lt(v_i_5877_, v___x_5879_);
                if v___x_5880_ == 0 {
                    crate::leanh::lean_dec(v_i_5877_);
                    return v_entries_5878_;
                } else {
                    v_k_5881_ = lean_array_fget_borrowed(v_keys_5875_, v_i_5877_);
                    v_v_5882_ = lean_array_fget_borrowed(v_vals_5876_, v_i_5877_);
                    v___x_5883_ = l_Lean_instHashableMVarId_hash(v_k_5881_);
                    v_h_5884_ = lean_uint64_to_usize(v___x_5883_);
                    v___x_5885_ = 5usize;
                    v___x_5886_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_5887_ = 1usize;
                    v___x_5888_ = lean_usize_sub(v_depth_5874_, v___x_5887_);
                    v___x_5889_ = lean_usize_mul(v___x_5885_, v___x_5888_);
                    v_h_5890_ = lean_usize_shift_right(v_h_5884_, v___x_5889_);
                    v___x_5891_ = lean_nat_add(v_i_5877_, v___x_5886_);
                    crate::leanh::lean_dec(v_i_5877_);
                    crate::leanh::lean_inc(v_v_5882_);
                    crate::leanh::lean_inc(v_k_5881_);
                    v___x_5892_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__1_spec__1_spec__3___redArg(v_entries_5878_, v_h_5890_, v_depth_5874_, v_k_5881_, v_v_5882_);
                    v_i_5877_ = v___x_5891_;
                    v_entries_5878_ = v___x_5892_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__1_spec__1_spec__3_spec__7___redArg___boxed(
    mut v_depth_5894_: *mut crate::leanh::LeanObject,
    mut v_keys_5895_: *mut crate::leanh::LeanObject,
    mut v_vals_5896_: *mut crate::leanh::LeanObject,
    mut v_i_5897_: *mut crate::leanh::LeanObject,
    mut v_entries_5898_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_depth_boxed_5899_: usize = 0;
    let mut v_res_5900_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_depth_boxed_5899_ = crate::leanh::lean_unbox_usize(v_depth_5894_);
    crate::leanh::lean_dec(v_depth_5894_);
    v_res_5900_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__1_spec__1_spec__3_spec__7___redArg(v_depth_boxed_5899_, v_keys_5895_, v_vals_5896_, v_i_5897_, v_entries_5898_);
    crate::leanh::lean_dec_ref(v_vals_5896_);
    crate::leanh::lean_dec_ref(v_keys_5895_);
    return v_res_5900_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__1_spec__1_spec__3___redArg___boxed(
    mut v_x_5901_: *mut crate::leanh::LeanObject,
    mut v_x_5902_: *mut crate::leanh::LeanObject,
    mut v_x_5903_: *mut crate::leanh::LeanObject,
    mut v_x_5904_: *mut crate::leanh::LeanObject,
    mut v_x_5905_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_195298__boxed_5906_: usize = 0;
    let mut v_x_195299__boxed_5907_: usize = 0;
    let mut v_res_5908_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_195298__boxed_5906_ = crate::leanh::lean_unbox_usize(v_x_5902_);
    crate::leanh::lean_dec(v_x_5902_);
    v_x_195299__boxed_5907_ = crate::leanh::lean_unbox_usize(v_x_5903_);
    crate::leanh::lean_dec(v_x_5903_);
    v_res_5908_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__1_spec__1_spec__3___redArg(v_x_5901_, v_x_195298__boxed_5906_, v_x_195299__boxed_5907_, v_x_5904_, v_x_5905_);
    return v_res_5908_;
}
pub unsafe fn l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__1_spec__1___redArg(
    mut v_x_5909_: *mut crate::leanh::LeanObject,
    mut v_x_5910_: *mut crate::leanh::LeanObject,
    mut v_x_5911_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5912_: u64 = 0;
    let mut v___x_5913_: usize = 0;
    let mut v___x_5914_: usize = 0;
    let mut v___x_5915_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5912_ = l_Lean_instHashableMVarId_hash(v_x_5910_);
    v___x_5913_ = lean_uint64_to_usize(v___x_5912_);
    v___x_5914_ = 1usize;
    v___x_5915_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__1_spec__1_spec__3___redArg(v_x_5909_, v___x_5913_, v___x_5914_, v_x_5910_, v_x_5911_);
    return v___x_5915_;
}
pub unsafe fn l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__1___redArg(
    mut v_mvarId_5916_: *mut crate::leanh::LeanObject,
    mut v_val_5917_: *mut crate::leanh::LeanObject,
    mut v___y_5918_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5920_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_5921_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_cache_5922_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_zetaDeltaFVarIds_5923_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_postponed_5924_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_diag_5925_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5927_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5928_: u8 = 0;
    let mut v_depth_5929_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_levelAssignDepth_5930_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_lmvarCounter_5931_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mvarCounter_5932_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_lDecls_5933_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_decls_5934_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_userNames_5935_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_lAssignment_5936_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_eAssignment_5937_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_dAssignment_5938_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5940_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5941_: u8 = 0;
    let mut v___x_5942_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5944_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5946_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5947_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5948_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5949_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5950_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5951_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5952_: u8 = 0;
    let mut v_isSharedCheck_5953_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5920_ = lean_st_ref_take(v___y_5918_);
                v_mctx_5921_ = crate::leanh::lean_ctor_get(v___x_5920_, 0);
                v_cache_5922_ = crate::leanh::lean_ctor_get(v___x_5920_, 1);
                v_zetaDeltaFVarIds_5923_ = crate::leanh::lean_ctor_get(v___x_5920_, 2);
                v_postponed_5924_ = crate::leanh::lean_ctor_get(v___x_5920_, 3);
                v_diag_5925_ = crate::leanh::lean_ctor_get(v___x_5920_, 4);
                v_isSharedCheck_5953_ = (!crate::leanh::lean_is_exclusive(v___x_5920_)) as u8;
                if v_isSharedCheck_5953_ == 0 {
                    v___x_5927_ = v___x_5920_;
                    v_isShared_5928_ = v_isSharedCheck_5953_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_diag_5925_);
                    crate::leanh::lean_inc(v_postponed_5924_);
                    crate::leanh::lean_inc(v_zetaDeltaFVarIds_5923_);
                    crate::leanh::lean_inc(v_cache_5922_);
                    crate::leanh::lean_inc(v_mctx_5921_);
                    crate::leanh::lean_dec(v___x_5920_);
                    v___x_5927_ = crate::leanh::lean_box(0);
                    v_isShared_5928_ = v_isSharedCheck_5953_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_depth_5929_ = crate::leanh::lean_ctor_get(v_mctx_5921_, 0);
                v_levelAssignDepth_5930_ = crate::leanh::lean_ctor_get(v_mctx_5921_, 1);
                v_lmvarCounter_5931_ = crate::leanh::lean_ctor_get(v_mctx_5921_, 2);
                v_mvarCounter_5932_ = crate::leanh::lean_ctor_get(v_mctx_5921_, 3);
                v_lDecls_5933_ = crate::leanh::lean_ctor_get(v_mctx_5921_, 4);
                v_decls_5934_ = crate::leanh::lean_ctor_get(v_mctx_5921_, 5);
                v_userNames_5935_ = crate::leanh::lean_ctor_get(v_mctx_5921_, 6);
                v_lAssignment_5936_ = crate::leanh::lean_ctor_get(v_mctx_5921_, 7);
                v_eAssignment_5937_ = crate::leanh::lean_ctor_get(v_mctx_5921_, 8);
                v_dAssignment_5938_ = crate::leanh::lean_ctor_get(v_mctx_5921_, 9);
                v_isSharedCheck_5952_ = (!crate::leanh::lean_is_exclusive(v_mctx_5921_)) as u8;
                if v_isSharedCheck_5952_ == 0 {
                    v___x_5940_ = v_mctx_5921_;
                    v_isShared_5941_ = v_isSharedCheck_5952_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_dAssignment_5938_);
                    crate::leanh::lean_inc(v_eAssignment_5937_);
                    crate::leanh::lean_inc(v_lAssignment_5936_);
                    crate::leanh::lean_inc(v_userNames_5935_);
                    crate::leanh::lean_inc(v_decls_5934_);
                    crate::leanh::lean_inc(v_lDecls_5933_);
                    crate::leanh::lean_inc(v_mvarCounter_5932_);
                    crate::leanh::lean_inc(v_lmvarCounter_5931_);
                    crate::leanh::lean_inc(v_levelAssignDepth_5930_);
                    crate::leanh::lean_inc(v_depth_5929_);
                    crate::leanh::lean_dec(v_mctx_5921_);
                    v___x_5940_ = crate::leanh::lean_box(0);
                    v_isShared_5941_ = v_isSharedCheck_5952_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_5942_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__1_spec__1___redArg(v_eAssignment_5937_, v_mvarId_5916_, v_val_5917_);
                if v_isShared_5941_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5940_, 8, v___x_5942_);
                    v___x_5944_ = v___x_5940_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_5951_ = crate::leanh::lean_alloc_ctor(0, 10, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5951_, 0, v_depth_5929_);
                    crate::leanh::lean_ctor_set(
                        v_reuseFailAlloc_5951_,
                        1,
                        v_levelAssignDepth_5930_,
                    );
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5951_, 2, v_lmvarCounter_5931_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5951_, 3, v_mvarCounter_5932_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5951_, 4, v_lDecls_5933_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5951_, 5, v_decls_5934_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5951_, 6, v_userNames_5935_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5951_, 7, v_lAssignment_5936_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5951_, 8, v___x_5942_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5951_, 9, v_dAssignment_5938_);
                    v___x_5944_ = v_reuseFailAlloc_5951_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_5928_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5927_, 0, v___x_5944_);
                    v___x_5946_ = v___x_5927_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_5950_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5950_, 0, v___x_5944_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5950_, 1, v_cache_5922_);
                    crate::leanh::lean_ctor_set(
                        v_reuseFailAlloc_5950_,
                        2,
                        v_zetaDeltaFVarIds_5923_,
                    );
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5950_, 3, v_postponed_5924_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5950_, 4, v_diag_5925_);
                    v___x_5946_ = v_reuseFailAlloc_5950_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_5947_ = lean_st_ref_set(v___y_5918_, v___x_5946_);
                v___x_5948_ = crate::leanh::lean_box(0);
                v___x_5949_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_5949_, 0, v___x_5948_);
                return v___x_5949_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__1___redArg___boxed(
    mut v_mvarId_5954_: *mut crate::leanh::LeanObject,
    mut v_val_5955_: *mut crate::leanh::LeanObject,
    mut v___y_5956_: *mut crate::leanh::LeanObject,
    mut v___y_5957_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5958_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5958_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__1___redArg(v_mvarId_5954_, v_val_5955_, v___y_5956_);
    crate::leanh::lean_dec(v___y_5956_);
    return v_res_5958_;
}
pub unsafe fn l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__2_spec__3___redArg(
    mut v___y_5959_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5961_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ngen_5962_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_namePrefix_5963_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_idx_5964_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5966_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5967_: u8 = 0;
    let mut v___x_5968_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_5969_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_5970_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_5971_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_traceState_5972_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_cache_5973_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_messages_5974_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_infoState_5975_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_5976_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5978_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5979_: u8 = 0;
    let mut v_r_5980_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5981_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5982_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5984_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5986_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5987_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5988_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5989_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5990_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5991_: u8 = 0;
    let mut v_unused_5992_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5993_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5961_ = lean_st_ref_get(v___y_5959_);
                v_ngen_5962_ = crate::leanh::lean_ctor_get(v___x_5961_, 2);
                crate::leanh::lean_inc_ref(v_ngen_5962_);
                crate::leanh::lean_dec(v___x_5961_);
                v_namePrefix_5963_ = crate::leanh::lean_ctor_get(v_ngen_5962_, 0);
                v_idx_5964_ = crate::leanh::lean_ctor_get(v_ngen_5962_, 1);
                v_isSharedCheck_5993_ = (!crate::leanh::lean_is_exclusive(v_ngen_5962_)) as u8;
                if v_isSharedCheck_5993_ == 0 {
                    v___x_5966_ = v_ngen_5962_;
                    v_isShared_5967_ = v_isSharedCheck_5993_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_idx_5964_);
                    crate::leanh::lean_inc(v_namePrefix_5963_);
                    crate::leanh::lean_dec(v_ngen_5962_);
                    v___x_5966_ = crate::leanh::lean_box(0);
                    v_isShared_5967_ = v_isSharedCheck_5993_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_5968_ = lean_st_ref_take(v___y_5959_);
                v_env_5969_ = crate::leanh::lean_ctor_get(v___x_5968_, 0);
                v_nextMacroScope_5970_ = crate::leanh::lean_ctor_get(v___x_5968_, 1);
                v_auxDeclNGen_5971_ = crate::leanh::lean_ctor_get(v___x_5968_, 3);
                v_traceState_5972_ = crate::leanh::lean_ctor_get(v___x_5968_, 4);
                v_cache_5973_ = crate::leanh::lean_ctor_get(v___x_5968_, 5);
                v_messages_5974_ = crate::leanh::lean_ctor_get(v___x_5968_, 6);
                v_infoState_5975_ = crate::leanh::lean_ctor_get(v___x_5968_, 7);
                v_snapshotTasks_5976_ = crate::leanh::lean_ctor_get(v___x_5968_, 8);
                v_isSharedCheck_5991_ = (!crate::leanh::lean_is_exclusive(v___x_5968_)) as u8;
                if v_isSharedCheck_5991_ == 0 {
                    v_unused_5992_ = crate::leanh::lean_ctor_get(v___x_5968_, 2);
                    crate::leanh::lean_dec(v_unused_5992_);
                    v___x_5978_ = v___x_5968_;
                    v_isShared_5979_ = v_isSharedCheck_5991_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snapshotTasks_5976_);
                    crate::leanh::lean_inc(v_infoState_5975_);
                    crate::leanh::lean_inc(v_messages_5974_);
                    crate::leanh::lean_inc(v_cache_5973_);
                    crate::leanh::lean_inc(v_traceState_5972_);
                    crate::leanh::lean_inc(v_auxDeclNGen_5971_);
                    crate::leanh::lean_inc(v_nextMacroScope_5970_);
                    crate::leanh::lean_inc(v_env_5969_);
                    crate::leanh::lean_dec(v___x_5968_);
                    v___x_5978_ = crate::leanh::lean_box(0);
                    v_isShared_5979_ = v_isSharedCheck_5991_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                crate::leanh::lean_inc(v_idx_5964_);
                crate::leanh::lean_inc(v_namePrefix_5963_);
                v_r_5980_ = l_Lean_Name_num___override(v_namePrefix_5963_, v_idx_5964_);
                v___x_5981_ = crate::leanh::lean_unsigned_to_nat(1);
                v___x_5982_ = lean_nat_add(v_idx_5964_, v___x_5981_);
                crate::leanh::lean_dec(v_idx_5964_);
                if v_isShared_5967_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5966_, 1, v___x_5982_);
                    v___x_5984_ = v___x_5966_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_5990_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5990_, 0, v_namePrefix_5963_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5990_, 1, v___x_5982_);
                    v___x_5984_ = v_reuseFailAlloc_5990_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_5979_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5978_, 2, v___x_5984_);
                    v___x_5986_ = v___x_5978_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_5989_ = crate::leanh::lean_alloc_ctor(0, 9, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5989_, 0, v_env_5969_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5989_, 1, v_nextMacroScope_5970_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5989_, 2, v___x_5984_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5989_, 3, v_auxDeclNGen_5971_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5989_, 4, v_traceState_5972_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5989_, 5, v_cache_5973_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5989_, 6, v_messages_5974_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5989_, 7, v_infoState_5975_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5989_, 8, v_snapshotTasks_5976_);
                    v___x_5986_ = v_reuseFailAlloc_5989_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_5987_ = lean_st_ref_set(v___y_5959_, v___x_5986_);
                v___x_5988_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_5988_, 0, v_r_5980_);
                return v___x_5988_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__2_spec__3___redArg___boxed(
    mut v___y_5994_: *mut crate::leanh::LeanObject,
    mut v___y_5995_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5996_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5996_ = l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__2_spec__3___redArg(v___y_5994_);
    crate::leanh::lean_dec(v___y_5994_);
    return v_res_5996_;
}
pub unsafe fn l_Lean_mkFreshFVarId___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__2(
    mut v___y_5997_: *mut crate::leanh::LeanObject,
    mut v___y_5998_: *mut crate::leanh::LeanObject,
    mut v___y_5999_: *mut crate::leanh::LeanObject,
    mut v___y_6000_: *mut crate::leanh::LeanObject,
    mut v___y_6001_: *mut crate::leanh::LeanObject,
    mut v___y_6002_: *mut crate::leanh::LeanObject,
    mut v___y_6003_: *mut crate::leanh::LeanObject,
    mut v___y_6004_: *mut crate::leanh::LeanObject,
    mut v___y_6005_: *mut crate::leanh::LeanObject,
    mut v___y_6006_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6008_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6009_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6011_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6012_: u8 = 0;
    let mut v___x_6014_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6015_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6016_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_6008_ = l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__2_spec__3___redArg(v___y_6006_);
                v_a_6009_ = crate::leanh::lean_ctor_get(v___x_6008_, 0);
                v_isSharedCheck_6016_ = (!crate::leanh::lean_is_exclusive(v___x_6008_)) as u8;
                if v_isSharedCheck_6016_ == 0 {
                    v___x_6011_ = v___x_6008_;
                    v_isShared_6012_ = v_isSharedCheck_6016_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_a_6009_);
                    crate::leanh::lean_dec(v___x_6008_);
                    v___x_6011_ = crate::leanh::lean_box(0);
                    v_isShared_6012_ = v_isSharedCheck_6016_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                if v_isShared_6012_ == 0 {
                    v___x_6014_ = v___x_6011_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_6015_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6015_, 0, v_a_6009_);
                    v___x_6014_ = v_reuseFailAlloc_6015_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_6014_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_mkFreshFVarId___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__2___boxed(
    mut v___y_6017_: *mut crate::leanh::LeanObject,
    mut v___y_6018_: *mut crate::leanh::LeanObject,
    mut v___y_6019_: *mut crate::leanh::LeanObject,
    mut v___y_6020_: *mut crate::leanh::LeanObject,
    mut v___y_6021_: *mut crate::leanh::LeanObject,
    mut v___y_6022_: *mut crate::leanh::LeanObject,
    mut v___y_6023_: *mut crate::leanh::LeanObject,
    mut v___y_6024_: *mut crate::leanh::LeanObject,
    mut v___y_6025_: *mut crate::leanh::LeanObject,
    mut v___y_6026_: *mut crate::leanh::LeanObject,
    mut v___y_6027_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6028_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6028_ = l_Lean_mkFreshFVarId___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__2(v___y_6017_, v___y_6018_, v___y_6019_, v___y_6020_, v___y_6021_, v___y_6022_, v___y_6023_, v___y_6024_, v___y_6025_, v___y_6026_);
    crate::leanh::lean_dec(v___y_6026_);
    crate::leanh::lean_dec_ref(v___y_6025_);
    crate::leanh::lean_dec(v___y_6024_);
    crate::leanh::lean_dec_ref(v___y_6023_);
    crate::leanh::lean_dec(v___y_6022_);
    crate::leanh::lean_dec_ref(v___y_6021_);
    crate::leanh::lean_dec(v___y_6020_);
    crate::leanh::lean_dec_ref(v___y_6019_);
    crate::leanh::lean_dec(v___y_6018_);
    crate::leanh::lean_dec(v___y_6017_);
    return v_res_6028_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lam__4(
    mut v___x_6034_: *mut crate::leanh::LeanObject,
    mut v_a_6035_: *mut crate::leanh::LeanObject,
    mut v___y_6036_: u8,
    mut v___x_6037_: u8,
    mut v___x_6038_: u8,
    mut v_a_6039_: *mut crate::leanh::LeanObject,
    mut v___x_6040_: *mut crate::leanh::LeanObject,
    mut v_expr_6041_: *mut crate::leanh::LeanObject,
    mut v___x_6042_: *mut crate::leanh::LeanObject,
    mut v_val_6043_: *mut crate::leanh::LeanObject,
    mut v_mvarId_6044_: *mut crate::leanh::LeanObject,
    mut v___x_6045_: *mut crate::leanh::LeanObject,
    mut v_a_6046_: *mut crate::leanh::LeanObject,
    mut v___y_6047_: *mut crate::leanh::LeanObject,
    mut v___y_6048_: *mut crate::leanh::LeanObject,
    mut v___y_6049_: *mut crate::leanh::LeanObject,
    mut v___y_6050_: *mut crate::leanh::LeanObject,
    mut v___y_6051_: *mut crate::leanh::LeanObject,
    mut v___y_6052_: *mut crate::leanh::LeanObject,
    mut v___y_6053_: *mut crate::leanh::LeanObject,
    mut v___y_6054_: *mut crate::leanh::LeanObject,
    mut v___y_6055_: *mut crate::leanh::LeanObject,
    mut v___y_6056_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6058_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6059_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6060_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6061_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6062_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6063_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6064_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6065_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6066_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6067_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6068_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6069_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6070_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6071_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6072_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6074_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6075_: u8 = 0;
    let mut v___x_6076_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toGoalState_6077_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6079_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6080_: u8 = 0;
    let mut v___x_6082_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6083_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6085_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6086_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6087_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6088_: u8 = 0;
    let mut v_unused_6089_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6090_: u8 = 0;
    let mut v_unused_6091_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6092_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6094_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6095_: u8 = 0;
    let mut v___x_6097_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6098_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6099_: u8 = 0;
    let mut v_a_6100_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6102_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6103_: u8 = 0;
    let mut v___x_6105_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6106_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6107_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_6058_ = l_Lean_Meta_mkLambdaFVars(
                    v___x_6034_,
                    v_a_6035_,
                    v___y_6036_,
                    v___x_6037_,
                    v___y_6036_,
                    v___x_6037_,
                    v___x_6038_,
                    v___y_6053_,
                    v___y_6054_,
                    v___y_6055_,
                    v___y_6056_,
                );
                if crate::leanh::lean_obj_tag(v___x_6058_) == 0 {
                    v_a_6059_ = crate::leanh::lean_ctor_get(v___x_6058_, 0);
                    crate::leanh::lean_inc(v_a_6059_);
                    crate::leanh::lean_dec_ref_known(v___x_6058_, 1);
                    v___x_6060_ = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lam__4___closed__1;
                    v___x_6061_ = crate::leanh::lean_box(0);
                    v___x_6062_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_6062_, 0, v_a_6039_);
                    crate::leanh::lean_ctor_set(v___x_6062_, 1, v___x_6061_);
                    v___x_6063_ = l_Lean_mkConst(v___x_6060_, v___x_6062_);
                    v___x_6064_ = crate::leanh::lean_unsigned_to_nat(5);
                    v___x_6065_ = lean_mk_empty_array_with_capacity(v___x_6064_);
                    v___x_6066_ = lean_array_push(v___x_6065_, v___x_6040_);
                    v___x_6067_ = lean_array_push(v___x_6066_, v_expr_6041_);
                    v___x_6068_ = lean_array_push(v___x_6067_, v___x_6042_);
                    v___x_6069_ = lean_array_push(v___x_6068_, v_val_6043_);
                    v___x_6070_ = lean_array_push(v___x_6069_, v_a_6059_);
                    v___x_6071_ = l_Lean_mkAppN(v___x_6063_, v___x_6070_);
                    crate::leanh::lean_dec_ref(v___x_6070_);
                    v___x_6072_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__1___redArg(v_mvarId_6044_, v___x_6071_, v___y_6054_);
                    if crate::leanh::lean_obj_tag(v___x_6072_) == 0 {
                        v_isSharedCheck_6090_ =
                            (!crate::leanh::lean_is_exclusive(v___x_6072_)) as u8;
                        if v_isSharedCheck_6090_ == 0 {
                            v_unused_6091_ = crate::leanh::lean_ctor_get(v___x_6072_, 0);
                            crate::leanh::lean_dec(v_unused_6091_);
                            v___x_6074_ = v___x_6072_;
                            v_isShared_6075_ = v_isSharedCheck_6090_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_dec(v___x_6072_);
                            v___x_6074_ = crate::leanh::lean_box(0);
                            v_isShared_6075_ = v_isSharedCheck_6090_;
                            state = 1;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec(v_a_6046_);
                        crate::leanh::lean_dec(v___x_6045_);
                        v_a_6092_ = crate::leanh::lean_ctor_get(v___x_6072_, 0);
                        v_isSharedCheck_6099_ =
                            (!crate::leanh::lean_is_exclusive(v___x_6072_)) as u8;
                        if v_isSharedCheck_6099_ == 0 {
                            v___x_6094_ = v___x_6072_;
                            v_isShared_6095_ = v_isSharedCheck_6099_;
                            state = 5;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_6092_);
                            crate::leanh::lean_dec(v___x_6072_);
                            v___x_6094_ = crate::leanh::lean_box(0);
                            v_isShared_6095_ = v_isSharedCheck_6099_;
                            state = 5;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec(v_a_6046_);
                    crate::leanh::lean_dec(v___x_6045_);
                    crate::leanh::lean_dec(v_mvarId_6044_);
                    crate::leanh::lean_dec_ref(v_val_6043_);
                    crate::leanh::lean_dec_ref(v___x_6042_);
                    crate::leanh::lean_dec_ref(v_expr_6041_);
                    crate::leanh::lean_dec_ref(v___x_6040_);
                    crate::leanh::lean_dec(v_a_6039_);
                    v_a_6100_ = crate::leanh::lean_ctor_get(v___x_6058_, 0);
                    v_isSharedCheck_6107_ = (!crate::leanh::lean_is_exclusive(v___x_6058_)) as u8;
                    if v_isSharedCheck_6107_ == 0 {
                        v___x_6102_ = v___x_6058_;
                        v_isShared_6103_ = v_isSharedCheck_6107_;
                        state = 7;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_6100_);
                        crate::leanh::lean_dec(v___x_6058_);
                        v___x_6102_ = crate::leanh::lean_box(0);
                        v_isShared_6103_ = v_isSharedCheck_6107_;
                        state = 7;
                        continue;
                    }
                }
            }
            1 => {
                v___x_6076_ = lean_st_ref_get(v___y_6047_);
                v_toGoalState_6077_ = crate::leanh::lean_ctor_get(v___x_6076_, 0);
                v_isSharedCheck_6088_ = (!crate::leanh::lean_is_exclusive(v___x_6076_)) as u8;
                if v_isSharedCheck_6088_ == 0 {
                    v_unused_6089_ = crate::leanh::lean_ctor_get(v___x_6076_, 1);
                    crate::leanh::lean_dec(v_unused_6089_);
                    v___x_6079_ = v___x_6076_;
                    v_isShared_6080_ = v_isSharedCheck_6088_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_toGoalState_6077_);
                    crate::leanh::lean_dec(v___x_6076_);
                    v___x_6079_ = crate::leanh::lean_box(0);
                    v_isShared_6080_ = v_isSharedCheck_6088_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                if v_isShared_6080_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_6079_, 1, v___x_6045_);
                    v___x_6082_ = v___x_6079_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_6087_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6087_, 0, v_toGoalState_6077_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6087_, 1, v___x_6045_);
                    v___x_6082_ = v_reuseFailAlloc_6087_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_6083_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_6083_, 0, v_a_6046_);
                crate::leanh::lean_ctor_set(v___x_6083_, 1, v___x_6082_);
                if v_isShared_6075_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_6074_, 0, v___x_6083_);
                    v___x_6085_ = v___x_6074_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_6086_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6086_, 0, v___x_6083_);
                    v___x_6085_ = v_reuseFailAlloc_6086_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_6085_;
            }
            5 => {
                if v_isShared_6095_ == 0 {
                    v___x_6097_ = v___x_6094_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_6098_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6098_, 0, v_a_6092_);
                    v___x_6097_ = v_reuseFailAlloc_6098_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_6097_;
            }
            7 => {
                if v_isShared_6103_ == 0 {
                    v___x_6105_ = v___x_6102_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_6106_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6106_, 0, v_a_6100_);
                    v___x_6105_ = v_reuseFailAlloc_6106_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_6105_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lam__4___boxed(
    _args: *mut *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6108_: *mut crate::leanh::LeanObject = *_args.add(0);
    let mut v_a_6109_: *mut crate::leanh::LeanObject = *_args.add(1);
    let mut v___y_6110_: *mut crate::leanh::LeanObject = *_args.add(2);
    let mut v___x_6111_: *mut crate::leanh::LeanObject = *_args.add(3);
    let mut v___x_6112_: *mut crate::leanh::LeanObject = *_args.add(4);
    let mut v_a_6113_: *mut crate::leanh::LeanObject = *_args.add(5);
    let mut v___x_6114_: *mut crate::leanh::LeanObject = *_args.add(6);
    let mut v_expr_6115_: *mut crate::leanh::LeanObject = *_args.add(7);
    let mut v___x_6116_: *mut crate::leanh::LeanObject = *_args.add(8);
    let mut v_val_6117_: *mut crate::leanh::LeanObject = *_args.add(9);
    let mut v_mvarId_6118_: *mut crate::leanh::LeanObject = *_args.add(10);
    let mut v___x_6119_: *mut crate::leanh::LeanObject = *_args.add(11);
    let mut v_a_6120_: *mut crate::leanh::LeanObject = *_args.add(12);
    let mut v___y_6121_: *mut crate::leanh::LeanObject = *_args.add(13);
    let mut v___y_6122_: *mut crate::leanh::LeanObject = *_args.add(14);
    let mut v___y_6123_: *mut crate::leanh::LeanObject = *_args.add(15);
    let mut v___y_6124_: *mut crate::leanh::LeanObject = *_args.add(16);
    let mut v___y_6125_: *mut crate::leanh::LeanObject = *_args.add(17);
    let mut v___y_6126_: *mut crate::leanh::LeanObject = *_args.add(18);
    let mut v___y_6127_: *mut crate::leanh::LeanObject = *_args.add(19);
    let mut v___y_6128_: *mut crate::leanh::LeanObject = *_args.add(20);
    let mut v___y_6129_: *mut crate::leanh::LeanObject = *_args.add(21);
    let mut v___y_6130_: *mut crate::leanh::LeanObject = *_args.add(22);
    let mut v___y_6131_: *mut crate::leanh::LeanObject = *_args.add(23);
    let mut v___y_195625__boxed_6132_: u8 = 0;
    let mut v___x_195626__boxed_6133_: u8 = 0;
    let mut v___x_195627__boxed_6134_: u8 = 0;
    let mut v_res_6135_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___y_195625__boxed_6132_ = (crate::leanh::lean_unbox(v___y_6110_) as u8);
    v___x_195626__boxed_6133_ = (crate::leanh::lean_unbox(v___x_6111_) as u8);
    v___x_195627__boxed_6134_ = (crate::leanh::lean_unbox(v___x_6112_) as u8);
    v_res_6135_ = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lam__4(
        v___x_6108_,
        v_a_6109_,
        v___y_195625__boxed_6132_,
        v___x_195626__boxed_6133_,
        v___x_195627__boxed_6134_,
        v_a_6113_,
        v___x_6114_,
        v_expr_6115_,
        v___x_6116_,
        v_val_6117_,
        v_mvarId_6118_,
        v___x_6119_,
        v_a_6120_,
        v___y_6121_,
        v___y_6122_,
        v___y_6123_,
        v___y_6124_,
        v___y_6125_,
        v___y_6126_,
        v___y_6127_,
        v___y_6128_,
        v___y_6129_,
        v___y_6130_,
    );
    crate::leanh::lean_dec(v___y_6130_);
    crate::leanh::lean_dec_ref(v___y_6129_);
    crate::leanh::lean_dec(v___y_6128_);
    crate::leanh::lean_dec_ref(v___y_6127_);
    crate::leanh::lean_dec(v___y_6126_);
    crate::leanh::lean_dec_ref(v___y_6125_);
    crate::leanh::lean_dec(v___y_6124_);
    crate::leanh::lean_dec_ref(v___y_6123_);
    crate::leanh::lean_dec(v___y_6122_);
    crate::leanh::lean_dec(v___y_6121_);
    crate::leanh::lean_dec_ref(v___x_6108_);
    return v_res_6135_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lam__3(
    mut v___x_6141_: *mut crate::leanh::LeanObject,
    mut v_a_6142_: *mut crate::leanh::LeanObject,
    mut v___x_6143_: u8,
    mut v___x_6144_: u8,
    mut v___x_6145_: u8,
    mut v_a_6146_: *mut crate::leanh::LeanObject,
    mut v___x_6147_: *mut crate::leanh::LeanObject,
    mut v___x_6148_: *mut crate::leanh::LeanObject,
    mut v_expr_6149_: *mut crate::leanh::LeanObject,
    mut v___x_6150_: *mut crate::leanh::LeanObject,
    mut v_val_6151_: *mut crate::leanh::LeanObject,
    mut v_mvarId_6152_: *mut crate::leanh::LeanObject,
    mut v___x_6153_: *mut crate::leanh::LeanObject,
    mut v_a_6154_: *mut crate::leanh::LeanObject,
    mut v___y_6155_: *mut crate::leanh::LeanObject,
    mut v___y_6156_: *mut crate::leanh::LeanObject,
    mut v___y_6157_: *mut crate::leanh::LeanObject,
    mut v___y_6158_: *mut crate::leanh::LeanObject,
    mut v___y_6159_: *mut crate::leanh::LeanObject,
    mut v___y_6160_: *mut crate::leanh::LeanObject,
    mut v___y_6161_: *mut crate::leanh::LeanObject,
    mut v___y_6162_: *mut crate::leanh::LeanObject,
    mut v___y_6163_: *mut crate::leanh::LeanObject,
    mut v___y_6164_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6166_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6167_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6168_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6169_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6170_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6171_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6172_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6173_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6174_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6175_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6176_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6177_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6178_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6179_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6181_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6182_: u8 = 0;
    let mut v___x_6183_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toGoalState_6184_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6186_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6187_: u8 = 0;
    let mut v___x_6189_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6190_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6192_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6193_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6194_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6195_: u8 = 0;
    let mut v_unused_6196_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6197_: u8 = 0;
    let mut v_unused_6198_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6199_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6201_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6202_: u8 = 0;
    let mut v___x_6204_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6205_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6206_: u8 = 0;
    let mut v_a_6207_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6209_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6210_: u8 = 0;
    let mut v___x_6212_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6213_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6214_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_6166_ = l_Lean_Meta_mkLambdaFVars(
                    v___x_6141_,
                    v_a_6142_,
                    v___x_6143_,
                    v___x_6144_,
                    v___x_6143_,
                    v___x_6144_,
                    v___x_6145_,
                    v___y_6161_,
                    v___y_6162_,
                    v___y_6163_,
                    v___y_6164_,
                );
                if crate::leanh::lean_obj_tag(v___x_6166_) == 0 {
                    v_a_6167_ = crate::leanh::lean_ctor_get(v___x_6166_, 0);
                    crate::leanh::lean_inc(v_a_6167_);
                    crate::leanh::lean_dec_ref_known(v___x_6166_, 1);
                    v___x_6168_ = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lam__3___closed__1;
                    v___x_6169_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_6169_, 0, v_a_6146_);
                    crate::leanh::lean_ctor_set(v___x_6169_, 1, v___x_6147_);
                    v___x_6170_ = l_Lean_mkConst(v___x_6168_, v___x_6169_);
                    v___x_6171_ = crate::leanh::lean_unsigned_to_nat(5);
                    v___x_6172_ = lean_mk_empty_array_with_capacity(v___x_6171_);
                    v___x_6173_ = lean_array_push(v___x_6172_, v___x_6148_);
                    v___x_6174_ = lean_array_push(v___x_6173_, v_expr_6149_);
                    v___x_6175_ = lean_array_push(v___x_6174_, v___x_6150_);
                    v___x_6176_ = lean_array_push(v___x_6175_, v_val_6151_);
                    v___x_6177_ = lean_array_push(v___x_6176_, v_a_6167_);
                    v___x_6178_ = l_Lean_mkAppN(v___x_6170_, v___x_6177_);
                    crate::leanh::lean_dec_ref(v___x_6177_);
                    v___x_6179_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__1___redArg(v_mvarId_6152_, v___x_6178_, v___y_6162_);
                    if crate::leanh::lean_obj_tag(v___x_6179_) == 0 {
                        v_isSharedCheck_6197_ =
                            (!crate::leanh::lean_is_exclusive(v___x_6179_)) as u8;
                        if v_isSharedCheck_6197_ == 0 {
                            v_unused_6198_ = crate::leanh::lean_ctor_get(v___x_6179_, 0);
                            crate::leanh::lean_dec(v_unused_6198_);
                            v___x_6181_ = v___x_6179_;
                            v_isShared_6182_ = v_isSharedCheck_6197_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_dec(v___x_6179_);
                            v___x_6181_ = crate::leanh::lean_box(0);
                            v_isShared_6182_ = v_isSharedCheck_6197_;
                            state = 1;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec(v_a_6154_);
                        crate::leanh::lean_dec(v___x_6153_);
                        v_a_6199_ = crate::leanh::lean_ctor_get(v___x_6179_, 0);
                        v_isSharedCheck_6206_ =
                            (!crate::leanh::lean_is_exclusive(v___x_6179_)) as u8;
                        if v_isSharedCheck_6206_ == 0 {
                            v___x_6201_ = v___x_6179_;
                            v_isShared_6202_ = v_isSharedCheck_6206_;
                            state = 5;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_6199_);
                            crate::leanh::lean_dec(v___x_6179_);
                            v___x_6201_ = crate::leanh::lean_box(0);
                            v_isShared_6202_ = v_isSharedCheck_6206_;
                            state = 5;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec(v_a_6154_);
                    crate::leanh::lean_dec(v___x_6153_);
                    crate::leanh::lean_dec(v_mvarId_6152_);
                    crate::leanh::lean_dec_ref(v_val_6151_);
                    crate::leanh::lean_dec_ref(v___x_6150_);
                    crate::leanh::lean_dec_ref(v_expr_6149_);
                    crate::leanh::lean_dec_ref(v___x_6148_);
                    crate::leanh::lean_dec(v___x_6147_);
                    crate::leanh::lean_dec(v_a_6146_);
                    v_a_6207_ = crate::leanh::lean_ctor_get(v___x_6166_, 0);
                    v_isSharedCheck_6214_ = (!crate::leanh::lean_is_exclusive(v___x_6166_)) as u8;
                    if v_isSharedCheck_6214_ == 0 {
                        v___x_6209_ = v___x_6166_;
                        v_isShared_6210_ = v_isSharedCheck_6214_;
                        state = 7;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_6207_);
                        crate::leanh::lean_dec(v___x_6166_);
                        v___x_6209_ = crate::leanh::lean_box(0);
                        v_isShared_6210_ = v_isSharedCheck_6214_;
                        state = 7;
                        continue;
                    }
                }
            }
            1 => {
                v___x_6183_ = lean_st_ref_get(v___y_6155_);
                v_toGoalState_6184_ = crate::leanh::lean_ctor_get(v___x_6183_, 0);
                v_isSharedCheck_6195_ = (!crate::leanh::lean_is_exclusive(v___x_6183_)) as u8;
                if v_isSharedCheck_6195_ == 0 {
                    v_unused_6196_ = crate::leanh::lean_ctor_get(v___x_6183_, 1);
                    crate::leanh::lean_dec(v_unused_6196_);
                    v___x_6186_ = v___x_6183_;
                    v_isShared_6187_ = v_isSharedCheck_6195_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_toGoalState_6184_);
                    crate::leanh::lean_dec(v___x_6183_);
                    v___x_6186_ = crate::leanh::lean_box(0);
                    v_isShared_6187_ = v_isSharedCheck_6195_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                if v_isShared_6187_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_6186_, 1, v___x_6153_);
                    v___x_6189_ = v___x_6186_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_6194_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6194_, 0, v_toGoalState_6184_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6194_, 1, v___x_6153_);
                    v___x_6189_ = v_reuseFailAlloc_6194_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_6190_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_6190_, 0, v_a_6154_);
                crate::leanh::lean_ctor_set(v___x_6190_, 1, v___x_6189_);
                if v_isShared_6182_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_6181_, 0, v___x_6190_);
                    v___x_6192_ = v___x_6181_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_6193_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6193_, 0, v___x_6190_);
                    v___x_6192_ = v_reuseFailAlloc_6193_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_6192_;
            }
            5 => {
                if v_isShared_6202_ == 0 {
                    v___x_6204_ = v___x_6201_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_6205_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6205_, 0, v_a_6199_);
                    v___x_6204_ = v_reuseFailAlloc_6205_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_6204_;
            }
            7 => {
                if v_isShared_6210_ == 0 {
                    v___x_6212_ = v___x_6209_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_6213_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6213_, 0, v_a_6207_);
                    v___x_6212_ = v_reuseFailAlloc_6213_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_6212_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lam__3___boxed(
    _args: *mut *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6215_: *mut crate::leanh::LeanObject = *_args.add(0);
    let mut v_a_6216_: *mut crate::leanh::LeanObject = *_args.add(1);
    let mut v___x_6217_: *mut crate::leanh::LeanObject = *_args.add(2);
    let mut v___x_6218_: *mut crate::leanh::LeanObject = *_args.add(3);
    let mut v___x_6219_: *mut crate::leanh::LeanObject = *_args.add(4);
    let mut v_a_6220_: *mut crate::leanh::LeanObject = *_args.add(5);
    let mut v___x_6221_: *mut crate::leanh::LeanObject = *_args.add(6);
    let mut v___x_6222_: *mut crate::leanh::LeanObject = *_args.add(7);
    let mut v_expr_6223_: *mut crate::leanh::LeanObject = *_args.add(8);
    let mut v___x_6224_: *mut crate::leanh::LeanObject = *_args.add(9);
    let mut v_val_6225_: *mut crate::leanh::LeanObject = *_args.add(10);
    let mut v_mvarId_6226_: *mut crate::leanh::LeanObject = *_args.add(11);
    let mut v___x_6227_: *mut crate::leanh::LeanObject = *_args.add(12);
    let mut v_a_6228_: *mut crate::leanh::LeanObject = *_args.add(13);
    let mut v___y_6229_: *mut crate::leanh::LeanObject = *_args.add(14);
    let mut v___y_6230_: *mut crate::leanh::LeanObject = *_args.add(15);
    let mut v___y_6231_: *mut crate::leanh::LeanObject = *_args.add(16);
    let mut v___y_6232_: *mut crate::leanh::LeanObject = *_args.add(17);
    let mut v___y_6233_: *mut crate::leanh::LeanObject = *_args.add(18);
    let mut v___y_6234_: *mut crate::leanh::LeanObject = *_args.add(19);
    let mut v___y_6235_: *mut crate::leanh::LeanObject = *_args.add(20);
    let mut v___y_6236_: *mut crate::leanh::LeanObject = *_args.add(21);
    let mut v___y_6237_: *mut crate::leanh::LeanObject = *_args.add(22);
    let mut v___y_6238_: *mut crate::leanh::LeanObject = *_args.add(23);
    let mut v___y_6239_: *mut crate::leanh::LeanObject = *_args.add(24);
    let mut v___x_195807__boxed_6240_: u8 = 0;
    let mut v___x_195808__boxed_6241_: u8 = 0;
    let mut v___x_195809__boxed_6242_: u8 = 0;
    let mut v_res_6243_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_195807__boxed_6240_ = (crate::leanh::lean_unbox(v___x_6217_) as u8);
    v___x_195808__boxed_6241_ = (crate::leanh::lean_unbox(v___x_6218_) as u8);
    v___x_195809__boxed_6242_ = (crate::leanh::lean_unbox(v___x_6219_) as u8);
    v_res_6243_ = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lam__3(
        v___x_6215_,
        v_a_6216_,
        v___x_195807__boxed_6240_,
        v___x_195808__boxed_6241_,
        v___x_195809__boxed_6242_,
        v_a_6220_,
        v___x_6221_,
        v___x_6222_,
        v_expr_6223_,
        v___x_6224_,
        v_val_6225_,
        v_mvarId_6226_,
        v___x_6227_,
        v_a_6228_,
        v___y_6229_,
        v___y_6230_,
        v___y_6231_,
        v___y_6232_,
        v___y_6233_,
        v___y_6234_,
        v___y_6235_,
        v___y_6236_,
        v___y_6237_,
        v___y_6238_,
    );
    crate::leanh::lean_dec(v___y_6238_);
    crate::leanh::lean_dec_ref(v___y_6237_);
    crate::leanh::lean_dec(v___y_6236_);
    crate::leanh::lean_dec_ref(v___y_6235_);
    crate::leanh::lean_dec(v___y_6234_);
    crate::leanh::lean_dec_ref(v___y_6233_);
    crate::leanh::lean_dec(v___y_6232_);
    crate::leanh::lean_dec_ref(v___y_6231_);
    crate::leanh::lean_dec(v___y_6230_);
    crate::leanh::lean_dec(v___y_6229_);
    crate::leanh::lean_dec_ref(v___x_6215_);
    return v_res_6243_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lam__2(
    mut v___x_6244_: *mut crate::leanh::LeanObject,
    mut v_a_6245_: *mut crate::leanh::LeanObject,
    mut v___y_6246_: u8,
    mut v___x_6247_: u8,
    mut v___x_6248_: u8,
    mut v_mvarId_6249_: *mut crate::leanh::LeanObject,
    mut v___x_6250_: *mut crate::leanh::LeanObject,
    mut v_a_6251_: *mut crate::leanh::LeanObject,
    mut v___y_6252_: *mut crate::leanh::LeanObject,
    mut v___y_6253_: *mut crate::leanh::LeanObject,
    mut v___y_6254_: *mut crate::leanh::LeanObject,
    mut v___y_6255_: *mut crate::leanh::LeanObject,
    mut v___y_6256_: *mut crate::leanh::LeanObject,
    mut v___y_6257_: *mut crate::leanh::LeanObject,
    mut v___y_6258_: *mut crate::leanh::LeanObject,
    mut v___y_6259_: *mut crate::leanh::LeanObject,
    mut v___y_6260_: *mut crate::leanh::LeanObject,
    mut v___y_6261_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6263_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6264_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6265_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6267_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6268_: u8 = 0;
    let mut v___x_6269_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toGoalState_6270_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6272_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6273_: u8 = 0;
    let mut v___x_6275_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6276_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6278_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6279_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6280_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6281_: u8 = 0;
    let mut v_unused_6282_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6283_: u8 = 0;
    let mut v_unused_6284_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6285_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6287_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6288_: u8 = 0;
    let mut v___x_6290_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6291_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6292_: u8 = 0;
    let mut v_a_6293_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6295_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6296_: u8 = 0;
    let mut v___x_6298_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6299_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6300_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_6263_ = l_Lean_Meta_mkLambdaFVars(
                    v___x_6244_,
                    v_a_6245_,
                    v___y_6246_,
                    v___x_6247_,
                    v___y_6246_,
                    v___x_6247_,
                    v___x_6248_,
                    v___y_6258_,
                    v___y_6259_,
                    v___y_6260_,
                    v___y_6261_,
                );
                if crate::leanh::lean_obj_tag(v___x_6263_) == 0 {
                    v_a_6264_ = crate::leanh::lean_ctor_get(v___x_6263_, 0);
                    crate::leanh::lean_inc(v_a_6264_);
                    crate::leanh::lean_dec_ref_known(v___x_6263_, 1);
                    v___x_6265_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__1___redArg(v_mvarId_6249_, v_a_6264_, v___y_6259_);
                    if crate::leanh::lean_obj_tag(v___x_6265_) == 0 {
                        v_isSharedCheck_6283_ =
                            (!crate::leanh::lean_is_exclusive(v___x_6265_)) as u8;
                        if v_isSharedCheck_6283_ == 0 {
                            v_unused_6284_ = crate::leanh::lean_ctor_get(v___x_6265_, 0);
                            crate::leanh::lean_dec(v_unused_6284_);
                            v___x_6267_ = v___x_6265_;
                            v_isShared_6268_ = v_isSharedCheck_6283_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_dec(v___x_6265_);
                            v___x_6267_ = crate::leanh::lean_box(0);
                            v_isShared_6268_ = v_isSharedCheck_6283_;
                            state = 1;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec(v_a_6251_);
                        crate::leanh::lean_dec(v___x_6250_);
                        v_a_6285_ = crate::leanh::lean_ctor_get(v___x_6265_, 0);
                        v_isSharedCheck_6292_ =
                            (!crate::leanh::lean_is_exclusive(v___x_6265_)) as u8;
                        if v_isSharedCheck_6292_ == 0 {
                            v___x_6287_ = v___x_6265_;
                            v_isShared_6288_ = v_isSharedCheck_6292_;
                            state = 5;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_6285_);
                            crate::leanh::lean_dec(v___x_6265_);
                            v___x_6287_ = crate::leanh::lean_box(0);
                            v_isShared_6288_ = v_isSharedCheck_6292_;
                            state = 5;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec(v_a_6251_);
                    crate::leanh::lean_dec(v___x_6250_);
                    crate::leanh::lean_dec(v_mvarId_6249_);
                    v_a_6293_ = crate::leanh::lean_ctor_get(v___x_6263_, 0);
                    v_isSharedCheck_6300_ = (!crate::leanh::lean_is_exclusive(v___x_6263_)) as u8;
                    if v_isSharedCheck_6300_ == 0 {
                        v___x_6295_ = v___x_6263_;
                        v_isShared_6296_ = v_isSharedCheck_6300_;
                        state = 7;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_6293_);
                        crate::leanh::lean_dec(v___x_6263_);
                        v___x_6295_ = crate::leanh::lean_box(0);
                        v_isShared_6296_ = v_isSharedCheck_6300_;
                        state = 7;
                        continue;
                    }
                }
            }
            1 => {
                v___x_6269_ = lean_st_ref_get(v___y_6252_);
                v_toGoalState_6270_ = crate::leanh::lean_ctor_get(v___x_6269_, 0);
                v_isSharedCheck_6281_ = (!crate::leanh::lean_is_exclusive(v___x_6269_)) as u8;
                if v_isSharedCheck_6281_ == 0 {
                    v_unused_6282_ = crate::leanh::lean_ctor_get(v___x_6269_, 1);
                    crate::leanh::lean_dec(v_unused_6282_);
                    v___x_6272_ = v___x_6269_;
                    v_isShared_6273_ = v_isSharedCheck_6281_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_toGoalState_6270_);
                    crate::leanh::lean_dec(v___x_6269_);
                    v___x_6272_ = crate::leanh::lean_box(0);
                    v_isShared_6273_ = v_isSharedCheck_6281_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                if v_isShared_6273_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_6272_, 1, v___x_6250_);
                    v___x_6275_ = v___x_6272_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_6280_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6280_, 0, v_toGoalState_6270_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6280_, 1, v___x_6250_);
                    v___x_6275_ = v_reuseFailAlloc_6280_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_6276_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_6276_, 0, v_a_6251_);
                crate::leanh::lean_ctor_set(v___x_6276_, 1, v___x_6275_);
                if v_isShared_6268_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_6267_, 0, v___x_6276_);
                    v___x_6278_ = v___x_6267_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_6279_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6279_, 0, v___x_6276_);
                    v___x_6278_ = v_reuseFailAlloc_6279_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_6278_;
            }
            5 => {
                if v_isShared_6288_ == 0 {
                    v___x_6290_ = v___x_6287_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_6291_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6291_, 0, v_a_6285_);
                    v___x_6290_ = v_reuseFailAlloc_6291_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_6290_;
            }
            7 => {
                if v_isShared_6296_ == 0 {
                    v___x_6298_ = v___x_6295_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_6299_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6299_, 0, v_a_6293_);
                    v___x_6298_ = v_reuseFailAlloc_6299_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_6298_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lam__2___boxed(
    _args: *mut *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6301_: *mut crate::leanh::LeanObject = *_args.add(0);
    let mut v_a_6302_: *mut crate::leanh::LeanObject = *_args.add(1);
    let mut v___y_6303_: *mut crate::leanh::LeanObject = *_args.add(2);
    let mut v___x_6304_: *mut crate::leanh::LeanObject = *_args.add(3);
    let mut v___x_6305_: *mut crate::leanh::LeanObject = *_args.add(4);
    let mut v_mvarId_6306_: *mut crate::leanh::LeanObject = *_args.add(5);
    let mut v___x_6307_: *mut crate::leanh::LeanObject = *_args.add(6);
    let mut v_a_6308_: *mut crate::leanh::LeanObject = *_args.add(7);
    let mut v___y_6309_: *mut crate::leanh::LeanObject = *_args.add(8);
    let mut v___y_6310_: *mut crate::leanh::LeanObject = *_args.add(9);
    let mut v___y_6311_: *mut crate::leanh::LeanObject = *_args.add(10);
    let mut v___y_6312_: *mut crate::leanh::LeanObject = *_args.add(11);
    let mut v___y_6313_: *mut crate::leanh::LeanObject = *_args.add(12);
    let mut v___y_6314_: *mut crate::leanh::LeanObject = *_args.add(13);
    let mut v___y_6315_: *mut crate::leanh::LeanObject = *_args.add(14);
    let mut v___y_6316_: *mut crate::leanh::LeanObject = *_args.add(15);
    let mut v___y_6317_: *mut crate::leanh::LeanObject = *_args.add(16);
    let mut v___y_6318_: *mut crate::leanh::LeanObject = *_args.add(17);
    let mut v___y_6319_: *mut crate::leanh::LeanObject = *_args.add(18);
    let mut v___y_195978__boxed_6320_: u8 = 0;
    let mut v___x_195979__boxed_6321_: u8 = 0;
    let mut v___x_195980__boxed_6322_: u8 = 0;
    let mut v_res_6323_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___y_195978__boxed_6320_ = (crate::leanh::lean_unbox(v___y_6303_) as u8);
    v___x_195979__boxed_6321_ = (crate::leanh::lean_unbox(v___x_6304_) as u8);
    v___x_195980__boxed_6322_ = (crate::leanh::lean_unbox(v___x_6305_) as u8);
    v_res_6323_ = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lam__2(
        v___x_6301_,
        v_a_6302_,
        v___y_195978__boxed_6320_,
        v___x_195979__boxed_6321_,
        v___x_195980__boxed_6322_,
        v_mvarId_6306_,
        v___x_6307_,
        v_a_6308_,
        v___y_6309_,
        v___y_6310_,
        v___y_6311_,
        v___y_6312_,
        v___y_6313_,
        v___y_6314_,
        v___y_6315_,
        v___y_6316_,
        v___y_6317_,
        v___y_6318_,
    );
    crate::leanh::lean_dec(v___y_6318_);
    crate::leanh::lean_dec_ref(v___y_6317_);
    crate::leanh::lean_dec(v___y_6316_);
    crate::leanh::lean_dec_ref(v___y_6315_);
    crate::leanh::lean_dec(v___y_6314_);
    crate::leanh::lean_dec_ref(v___y_6313_);
    crate::leanh::lean_dec(v___y_6312_);
    crate::leanh::lean_dec_ref(v___y_6311_);
    crate::leanh::lean_dec(v___y_6310_);
    crate::leanh::lean_dec(v___y_6309_);
    crate::leanh::lean_dec_ref(v___x_6301_);
    return v_res_6323_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lam__1(
    mut v_mvarId_6326_: *mut crate::leanh::LeanObject,
    mut v___x_6327_: *mut crate::leanh::LeanObject,
    mut v_generation_6328_: *mut crate::leanh::LeanObject,
    mut v___y_6329_: *mut crate::leanh::LeanObject,
    mut v___y_6330_: *mut crate::leanh::LeanObject,
    mut v___y_6331_: *mut crate::leanh::LeanObject,
    mut v___y_6332_: *mut crate::leanh::LeanObject,
    mut v___y_6333_: *mut crate::leanh::LeanObject,
    mut v___y_6334_: *mut crate::leanh::LeanObject,
    mut v___y_6335_: *mut crate::leanh::LeanObject,
    mut v___y_6336_: *mut crate::leanh::LeanObject,
    mut v___y_6337_: *mut crate::leanh::LeanObject,
    mut v___y_6338_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6340_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6341_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6342_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6343_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6344_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6345_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toGoalState_6346_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6348_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6349_: u8 = 0;
    let mut v___x_6350_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6352_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6353_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6354_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6355_: u8 = 0;
    let mut v_unused_6356_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6357_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6359_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6360_: u8 = 0;
    let mut v___x_6362_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6363_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6364_: u8 = 0;
    let mut v_a_6365_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6367_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6368_: u8 = 0;
    let mut v___x_6370_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6371_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6372_: u8 = 0;
    let mut v_a_6373_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6375_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6376_: u8 = 0;
    let mut v___x_6378_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6379_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6380_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                crate::leanh::lean_inc(v_mvarId_6326_);
                v___x_6340_ = l_Lean_MVarId_getTag(
                    v_mvarId_6326_,
                    v___y_6335_,
                    v___y_6336_,
                    v___y_6337_,
                    v___y_6338_,
                );
                if crate::leanh::lean_obj_tag(v___x_6340_) == 0 {
                    v_a_6341_ = crate::leanh::lean_ctor_get(v___x_6340_, 0);
                    crate::leanh::lean_inc(v_a_6341_);
                    crate::leanh::lean_dec_ref_known(v___x_6340_, 1);
                    v___x_6342_ = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(
                        v___x_6327_,
                        v_a_6341_,
                        v___y_6335_,
                        v___y_6336_,
                        v___y_6337_,
                        v___y_6338_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_6342_) == 0 {
                        v_a_6343_ = crate::leanh::lean_ctor_get(v___x_6342_, 0);
                        crate::leanh::lean_inc_n(v_a_6343_, 2);
                        crate::leanh::lean_dec_ref_known(v___x_6342_, 1);
                        v___x_6344_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__1___redArg(v_mvarId_6326_, v_a_6343_, v___y_6336_);
                        if crate::leanh::lean_obj_tag(v___x_6344_) == 0 {
                            crate::leanh::lean_dec_ref_known(v___x_6344_, 1);
                            v___x_6345_ = lean_st_ref_get(v___y_6329_);
                            v_toGoalState_6346_ = crate::leanh::lean_ctor_get(v___x_6345_, 0);
                            v_isSharedCheck_6355_ =
                                (!crate::leanh::lean_is_exclusive(v___x_6345_)) as u8;
                            if v_isSharedCheck_6355_ == 0 {
                                v_unused_6356_ = crate::leanh::lean_ctor_get(v___x_6345_, 1);
                                crate::leanh::lean_dec(v_unused_6356_);
                                v___x_6348_ = v___x_6345_;
                                v_isShared_6349_ = v_isSharedCheck_6355_;
                                state = 1;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_toGoalState_6346_);
                                crate::leanh::lean_dec(v___x_6345_);
                                v___x_6348_ = crate::leanh::lean_box(0);
                                v_isShared_6349_ = v_isSharedCheck_6355_;
                                state = 1;
                                continue;
                            }
                        } else {
                            crate::leanh::lean_dec(v_a_6343_);
                            crate::leanh::lean_dec(v_generation_6328_);
                            v_a_6357_ = crate::leanh::lean_ctor_get(v___x_6344_, 0);
                            v_isSharedCheck_6364_ =
                                (!crate::leanh::lean_is_exclusive(v___x_6344_)) as u8;
                            if v_isSharedCheck_6364_ == 0 {
                                v___x_6359_ = v___x_6344_;
                                v_isShared_6360_ = v_isSharedCheck_6364_;
                                state = 3;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_6357_);
                                crate::leanh::lean_dec(v___x_6344_);
                                v___x_6359_ = crate::leanh::lean_box(0);
                                v_isShared_6360_ = v_isSharedCheck_6364_;
                                state = 3;
                                continue;
                            }
                        }
                    } else {
                        crate::leanh::lean_dec(v_generation_6328_);
                        crate::leanh::lean_dec(v_mvarId_6326_);
                        v_a_6365_ = crate::leanh::lean_ctor_get(v___x_6342_, 0);
                        v_isSharedCheck_6372_ =
                            (!crate::leanh::lean_is_exclusive(v___x_6342_)) as u8;
                        if v_isSharedCheck_6372_ == 0 {
                            v___x_6367_ = v___x_6342_;
                            v_isShared_6368_ = v_isSharedCheck_6372_;
                            state = 5;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_6365_);
                            crate::leanh::lean_dec(v___x_6342_);
                            v___x_6367_ = crate::leanh::lean_box(0);
                            v_isShared_6368_ = v_isSharedCheck_6372_;
                            state = 5;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec(v_generation_6328_);
                    crate::leanh::lean_dec_ref(v___x_6327_);
                    crate::leanh::lean_dec(v_mvarId_6326_);
                    v_a_6373_ = crate::leanh::lean_ctor_get(v___x_6340_, 0);
                    v_isSharedCheck_6380_ = (!crate::leanh::lean_is_exclusive(v___x_6340_)) as u8;
                    if v_isSharedCheck_6380_ == 0 {
                        v___x_6375_ = v___x_6340_;
                        v_isShared_6376_ = v_isSharedCheck_6380_;
                        state = 7;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_6373_);
                        crate::leanh::lean_dec(v___x_6340_);
                        v___x_6375_ = crate::leanh::lean_box(0);
                        v_isShared_6376_ = v_isSharedCheck_6380_;
                        state = 7;
                        continue;
                    }
                }
            }
            1 => {
                v___x_6350_ = l_Lean_Expr_mvarId_x21(v_a_6343_);
                crate::leanh::lean_dec(v_a_6343_);
                if v_isShared_6349_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_6348_, 1, v___x_6350_);
                    v___x_6352_ = v___x_6348_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_6354_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6354_, 0, v_toGoalState_6346_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6354_, 1, v___x_6350_);
                    v___x_6352_ = v_reuseFailAlloc_6354_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_6353_ = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext(
                    v___x_6352_,
                    v_generation_6328_,
                    v___y_6330_,
                    v___y_6331_,
                    v___y_6332_,
                    v___y_6333_,
                    v___y_6334_,
                    v___y_6335_,
                    v___y_6336_,
                    v___y_6337_,
                    v___y_6338_,
                );
                return v___x_6353_;
            }
            3 => {
                if v_isShared_6360_ == 0 {
                    v___x_6362_ = v___x_6359_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_6363_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6363_, 0, v_a_6357_);
                    v___x_6362_ = v_reuseFailAlloc_6363_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_6362_;
            }
            5 => {
                if v_isShared_6368_ == 0 {
                    v___x_6370_ = v___x_6367_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_6371_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6371_, 0, v_a_6365_);
                    v___x_6370_ = v_reuseFailAlloc_6371_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_6370_;
            }
            7 => {
                if v_isShared_6376_ == 0 {
                    v___x_6378_ = v___x_6375_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_6379_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6379_, 0, v_a_6373_);
                    v___x_6378_ = v_reuseFailAlloc_6379_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_6378_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lam__1___boxed(
    mut v_mvarId_6381_: *mut crate::leanh::LeanObject,
    mut v___x_6382_: *mut crate::leanh::LeanObject,
    mut v_generation_6383_: *mut crate::leanh::LeanObject,
    mut v___y_6384_: *mut crate::leanh::LeanObject,
    mut v___y_6385_: *mut crate::leanh::LeanObject,
    mut v___y_6386_: *mut crate::leanh::LeanObject,
    mut v___y_6387_: *mut crate::leanh::LeanObject,
    mut v___y_6388_: *mut crate::leanh::LeanObject,
    mut v___y_6389_: *mut crate::leanh::LeanObject,
    mut v___y_6390_: *mut crate::leanh::LeanObject,
    mut v___y_6391_: *mut crate::leanh::LeanObject,
    mut v___y_6392_: *mut crate::leanh::LeanObject,
    mut v___y_6393_: *mut crate::leanh::LeanObject,
    mut v___y_6394_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6395_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6395_ = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lam__1(
        v_mvarId_6381_,
        v___x_6382_,
        v_generation_6383_,
        v___y_6384_,
        v___y_6385_,
        v___y_6386_,
        v___y_6387_,
        v___y_6388_,
        v___y_6389_,
        v___y_6390_,
        v___y_6391_,
        v___y_6392_,
        v___y_6393_,
    );
    crate::leanh::lean_dec(v___y_6393_);
    crate::leanh::lean_dec_ref(v___y_6392_);
    crate::leanh::lean_dec(v___y_6391_);
    crate::leanh::lean_dec_ref(v___y_6390_);
    crate::leanh::lean_dec(v___y_6389_);
    crate::leanh::lean_dec_ref(v___y_6388_);
    crate::leanh::lean_dec(v___y_6387_);
    crate::leanh::lean_dec_ref(v___y_6386_);
    crate::leanh::lean_dec(v___y_6385_);
    crate::leanh::lean_dec(v___y_6384_);
    return v_res_6395_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lam__5___closed__4()
-> *mut crate::leanh::LeanObject {
    let mut v___x_6401_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6402_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6403_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6401_ = crate::leanh::lean_box(0);
    v___x_6402_ =
        l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lam__5___closed__3;
    v___x_6403_ = l_Lean_mkConst(v___x_6402_, v___x_6401_);
    return v___x_6403_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lam__5(
    mut v_goal_6404_: *mut crate::leanh::LeanObject,
    mut v_generation_6405_: *mut crate::leanh::LeanObject,
    mut v___y_6406_: *mut crate::leanh::LeanObject,
    mut v___y_6407_: *mut crate::leanh::LeanObject,
    mut v___y_6408_: *mut crate::leanh::LeanObject,
    mut v___y_6409_: *mut crate::leanh::LeanObject,
    mut v___y_6410_: *mut crate::leanh::LeanObject,
    mut v___y_6411_: *mut crate::leanh::LeanObject,
    mut v___y_6412_: *mut crate::leanh::LeanObject,
    mut v___y_6413_: *mut crate::leanh::LeanObject,
    mut v___y_6414_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6416_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6418_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6419_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6420_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6421_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6423_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6424_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6425_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6427_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6428_: u8 = 0;
    let mut v___x_6430_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6431_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6432_: u8 = 0;
    let mut v___x_6433_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mvarId_6434_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6436_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6437_: u8 = 0;
    let mut v___x_6438_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6439_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6440_: u8 = 0;
    let mut v___x_6441_: u8 = 0;
    let mut v___y_6443_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6444_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6445_: u8 = 0;
    let mut v___y_6446_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6447_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6448_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6449_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6450_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6451_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6452_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6453_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6454_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6455_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6456_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6457_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6458_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6459_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6460_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6461_: u8 = 0;
    let mut v___x_6462_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6463_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6464_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6465_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6466_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6467_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6468_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6469_: u8 = 0;
    let mut v___x_6470_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6471_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6472_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_6473_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6474_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6475_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6477_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6478_: u8 = 0;
    let mut v___x_6480_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6481_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6482_: u8 = 0;
    let mut v___x_6483_: u8 = 0;
    let mut v___x_6484_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6485_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6486_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_zetaDelta_6487_: u8 = 0;
    let mut v___x_6488_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6489_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6490_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mvarId_6491_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_6492_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6493_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6494_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6496_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6497_: u8 = 0;
    let mut v___x_6499_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6500_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6501_: u8 = 0;
    let mut v___x_6502_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mvarId_6503_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6504_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6505_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_6506_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6507_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6508_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6510_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6511_: u8 = 0;
    let mut v___x_6513_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6514_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6515_: u8 = 0;
    let mut v___x_6516_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6518_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6519_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6520_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6521_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6522_: u8 = 0;
    let mut v___y_6523_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6524_: u8 = 0;
    let mut v___y_6525_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6526_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6527_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6528_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6529_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_localInsts_6530_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6531_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6532_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6533_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6534_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6535_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6536_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6537_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6538_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6539_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6540_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6541_: u8 = 0;
    let mut v___x_6542_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_6543_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6544_: u8 = 0;
    let mut v___x_6545_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6546_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6547_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6548_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6549_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6550_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6551_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6552_: u8 = 0;
    let mut v___x_6553_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6554_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6555_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6556_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6557_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6558_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6559_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6560_: u8 = 0;
    let mut v___x_6561_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6562_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6563_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_6564_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6565_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6566_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6568_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6569_: u8 = 0;
    let mut v___x_6571_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6572_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6573_: u8 = 0;
    let mut v_a_6574_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6576_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6577_: u8 = 0;
    let mut v___x_6579_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6580_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6581_: u8 = 0;
    let mut v___x_6582_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6583_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6584_: u8 = 0;
    let mut v___x_6585_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6586_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6587_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6588_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6589_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6590_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6591_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6592_: u8 = 0;
    let mut v___x_6593_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6594_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6595_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_6596_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6597_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6598_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6600_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6601_: u8 = 0;
    let mut v___x_6603_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6604_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6605_: u8 = 0;
    let mut v_a_6606_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6608_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6609_: u8 = 0;
    let mut v___x_6611_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6612_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6613_: u8 = 0;
    let mut v___x_6614_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6615_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6617_: u8 = 0;
    let mut v___x_6618_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mvarId_6619_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6621_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6622_: u8 = 0;
    let mut v___x_6623_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6624_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6625_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6626_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6627_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6628_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_expr_6629_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_proof_x3f_6630_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6631_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6632_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6633_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_lctx_6634_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_localInstances_6635_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6636_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6637_: u8 = 0;
    let mut v___x_6638_: u8 = 0;
    let mut v___x_6639_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6640_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6641_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6642_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_6643_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6645_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6646_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6647_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6648_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6650_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6651_: u8 = 0;
    let mut v___x_6653_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6654_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6655_: u8 = 0;
    let mut v_a_6656_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6658_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6659_: u8 = 0;
    let mut v___x_6661_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6662_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6663_: u8 = 0;
    let mut v_a_6664_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6666_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6667_: u8 = 0;
    let mut v___x_6669_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6670_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6671_: u8 = 0;
    let mut v_a_6672_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6674_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6675_: u8 = 0;
    let mut v___x_6677_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6678_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6679_: u8 = 0;
    let mut v_a_6680_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6682_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6683_: u8 = 0;
    let mut v___x_6685_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6686_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6687_: u8 = 0;
    let mut v_isSharedCheck_6688_: u8 = 0;
    let mut v_unused_6689_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6690_: u8 = 0;
    let mut v___x_6691_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6692_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6693_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6695_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6696_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6697_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6699_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6700_: u8 = 0;
    let mut v___x_6702_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6703_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6704_: u8 = 0;
    let mut v___x_6705_: u8 = 0;
    let mut v_a_6706_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6708_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6709_: u8 = 0;
    let mut v___x_6711_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6712_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6713_: u8 = 0;
    let mut v_a_6714_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6716_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6717_: u8 = 0;
    let mut v___x_6719_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6720_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6721_: u8 = 0;
    let mut v_isSharedCheck_6722_: u8 = 0;
    let mut v_unused_6723_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                crate::leanh::lean_inc_ref(v_goal_6404_);
                v___x_6416_ = lean_st_mk_ref(v_goal_6404_);
                v___x_6433_ = lean_st_ref_get(v___x_6416_);
                v_mvarId_6434_ = crate::leanh::lean_ctor_get(v___x_6433_, 1);
                v_isSharedCheck_6722_ = (!crate::leanh::lean_is_exclusive(v___x_6433_)) as u8;
                if v_isSharedCheck_6722_ == 0 {
                    v_unused_6723_ = crate::leanh::lean_ctor_get(v___x_6433_, 0);
                    crate::leanh::lean_dec(v_unused_6723_);
                    v___x_6436_ = v___x_6433_;
                    v_isShared_6437_ = v_isSharedCheck_6722_;
                    state = 5;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_mvarId_6434_);
                    crate::leanh::lean_dec(v___x_6433_);
                    v___x_6436_ = crate::leanh::lean_box(0);
                    v_isShared_6437_ = v_isSharedCheck_6722_;
                    state = 5;
                    continue;
                }
            }
            1 => {
                v___x_6419_ = lean_st_ref_get(v___x_6416_);
                crate::leanh::lean_dec(v___x_6416_);
                v___x_6420_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_6420_, 0, v_a_6418_);
                crate::leanh::lean_ctor_set(v___x_6420_, 1, v___x_6419_);
                v___x_6421_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_6421_, 0, v___x_6420_);
                return v___x_6421_;
            }
            2 => {
                if crate::leanh::lean_obj_tag(v___y_6423_) == 0 {
                    v_a_6424_ = crate::leanh::lean_ctor_get(v___y_6423_, 0);
                    crate::leanh::lean_inc(v_a_6424_);
                    crate::leanh::lean_dec_ref_known(v___y_6423_, 1);
                    v_a_6418_ = v_a_6424_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_dec(v___x_6416_);
                    v_a_6425_ = crate::leanh::lean_ctor_get(v___y_6423_, 0);
                    v_isSharedCheck_6432_ = (!crate::leanh::lean_is_exclusive(v___y_6423_)) as u8;
                    if v_isSharedCheck_6432_ == 0 {
                        v___x_6427_ = v___y_6423_;
                        v_isShared_6428_ = v_isSharedCheck_6432_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_6425_);
                        crate::leanh::lean_dec(v___y_6423_);
                        v___x_6427_ = crate::leanh::lean_box(0);
                        v_isShared_6428_ = v_isSharedCheck_6432_;
                        state = 3;
                        continue;
                    }
                }
            }
            3 => {
                if v_isShared_6428_ == 0 {
                    v___x_6430_ = v___x_6427_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_6431_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6431_, 0, v_a_6425_);
                    v___x_6430_ = v_reuseFailAlloc_6431_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_6430_;
            }
            5 => {
                v___x_6438_ = l_Lean_MVarId_getType(
                    v_mvarId_6434_,
                    v___y_6411_,
                    v___y_6412_,
                    v___y_6413_,
                    v___y_6414_,
                );
                if crate::leanh::lean_obj_tag(v___x_6438_) == 0 {
                    v_a_6439_ = crate::leanh::lean_ctor_get(v___x_6438_, 0);
                    crate::leanh::lean_inc(v_a_6439_);
                    crate::leanh::lean_dec_ref_known(v___x_6438_, 1);
                    v___x_6440_ = l_Lean_Expr_isForall(v_a_6439_);
                    v___x_6441_ = 1;
                    if v___x_6440_ == 0 {
                        crate::leanh::lean_del_object(v___x_6436_);
                        v___x_6483_ = l_Lean_Expr_isLet(v_a_6439_);
                        if v___x_6483_ == 0 {
                            crate::leanh::lean_dec(v_a_6439_);
                            crate::leanh::lean_dec_ref(v___y_6411_);
                            crate::leanh::lean_dec(v_generation_6405_);
                            v___x_6484_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_6484_, 0, v_goal_6404_);
                            v_a_6418_ = v___x_6484_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_dec_ref(v_goal_6404_);
                            v___x_6485_ = l_Lean_Meta_Grind_getConfig___redArg(v___y_6407_);
                            if crate::leanh::lean_obj_tag(v___x_6485_) == 0 {
                                v_a_6486_ = crate::leanh::lean_ctor_get(v___x_6485_, 0);
                                crate::leanh::lean_inc(v_a_6486_);
                                crate::leanh::lean_dec_ref_known(v___x_6485_, 1);
                                v_zetaDelta_6487_ = crate::leanh::lean_ctor_get_uint8(
                                    v_a_6486_,
                                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 13
                                        + 19) as u32,
                                );
                                crate::leanh::lean_dec(v_a_6486_);
                                if v_zetaDelta_6487_ == 0 {
                                    crate::leanh::lean_dec(v_a_6439_);
                                    v___x_6488_ = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_intro1(v___x_6416_, v___y_6406_, v___y_6407_, v___y_6408_, v___y_6409_, v___y_6410_, v___y_6411_, v___y_6412_, v___y_6413_, v___y_6414_);
                                    if crate::leanh::lean_obj_tag(v___x_6488_) == 0 {
                                        v_a_6489_ = crate::leanh::lean_ctor_get(v___x_6488_, 0);
                                        crate::leanh::lean_inc(v_a_6489_);
                                        crate::leanh::lean_dec_ref_known(v___x_6488_, 1);
                                        v___x_6490_ = lean_st_ref_get(v___x_6416_);
                                        v_mvarId_6491_ =
                                            crate::leanh::lean_ctor_get(v___x_6490_, 1);
                                        crate::leanh::lean_inc(v_mvarId_6491_);
                                        crate::leanh::lean_dec(v___x_6490_);
                                        v___f_6492_ = crate::leanh::lean_alloc_closure(l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lam__0___boxed as *mut core::ffi::c_void, 13, 2);
                                        crate::leanh::lean_closure_set(v___f_6492_, 0, v_a_6489_);
                                        crate::leanh::lean_closure_set(
                                            v___f_6492_,
                                            1,
                                            v_generation_6405_,
                                        );
                                        v___x_6493_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__0___redArg(v_mvarId_6491_, v___f_6492_, v___x_6416_, v___y_6406_, v___y_6407_, v___y_6408_, v___y_6409_, v___y_6410_, v___y_6411_, v___y_6412_, v___y_6413_, v___y_6414_);
                                        crate::leanh::lean_dec_ref(v___y_6411_);
                                        v___y_6423_ = v___x_6493_;
                                        state = 2;
                                        continue;
                                    } else {
                                        crate::leanh::lean_dec(v___x_6416_);
                                        crate::leanh::lean_dec_ref(v___y_6411_);
                                        crate::leanh::lean_dec(v_generation_6405_);
                                        v_a_6494_ = crate::leanh::lean_ctor_get(v___x_6488_, 0);
                                        v_isSharedCheck_6501_ =
                                            (!crate::leanh::lean_is_exclusive(v___x_6488_)) as u8;
                                        if v_isSharedCheck_6501_ == 0 {
                                            v___x_6496_ = v___x_6488_;
                                            v_isShared_6497_ = v_isSharedCheck_6501_;
                                            state = 9;
                                            continue;
                                        } else {
                                            crate::leanh::lean_inc(v_a_6494_);
                                            crate::leanh::lean_dec(v___x_6488_);
                                            v___x_6496_ = crate::leanh::lean_box(0);
                                            v_isShared_6497_ = v_isSharedCheck_6501_;
                                            state = 9;
                                            continue;
                                        }
                                    }
                                } else {
                                    v___x_6502_ = lean_st_ref_get(v___x_6416_);
                                    v_mvarId_6503_ = crate::leanh::lean_ctor_get(v___x_6502_, 1);
                                    crate::leanh::lean_inc_n(v_mvarId_6503_, 2);
                                    crate::leanh::lean_dec(v___x_6502_);
                                    v___x_6504_ = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lam__5___closed__0;
                                    v___x_6505_ =
                                        l_Lean_Meta_expandLet(v_a_6439_, v___x_6504_, v___x_6441_);
                                    crate::leanh::lean_dec(v_a_6439_);
                                    v___f_6506_ = crate::leanh::lean_alloc_closure(l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lam__1___boxed as *mut core::ffi::c_void, 14, 3);
                                    crate::leanh::lean_closure_set(v___f_6506_, 0, v_mvarId_6503_);
                                    crate::leanh::lean_closure_set(v___f_6506_, 1, v___x_6505_);
                                    crate::leanh::lean_closure_set(
                                        v___f_6506_,
                                        2,
                                        v_generation_6405_,
                                    );
                                    v___x_6507_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__0___redArg(v_mvarId_6503_, v___f_6506_, v___x_6416_, v___y_6406_, v___y_6407_, v___y_6408_, v___y_6409_, v___y_6410_, v___y_6411_, v___y_6412_, v___y_6413_, v___y_6414_);
                                    crate::leanh::lean_dec_ref(v___y_6411_);
                                    v___y_6423_ = v___x_6507_;
                                    state = 2;
                                    continue;
                                }
                            } else {
                                crate::leanh::lean_dec(v_a_6439_);
                                crate::leanh::lean_dec(v___x_6416_);
                                crate::leanh::lean_dec_ref(v___y_6411_);
                                crate::leanh::lean_dec(v_generation_6405_);
                                v_a_6508_ = crate::leanh::lean_ctor_get(v___x_6485_, 0);
                                v_isSharedCheck_6515_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_6485_)) as u8;
                                if v_isSharedCheck_6515_ == 0 {
                                    v___x_6510_ = v___x_6485_;
                                    v_isShared_6511_ = v_isSharedCheck_6515_;
                                    state = 11;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_a_6508_);
                                    crate::leanh::lean_dec(v___x_6485_);
                                    v___x_6510_ = crate::leanh::lean_box(0);
                                    v_isShared_6511_ = v_isSharedCheck_6515_;
                                    state = 11;
                                    continue;
                                }
                            }
                        }
                    } else {
                        crate::leanh::lean_dec(v_generation_6405_);
                        crate::leanh::lean_dec_ref(v_goal_6404_);
                        v___x_6516_ = l_Lean_Expr_bindingDomain_x21(v_a_6439_);
                        crate::leanh::lean_inc_ref(v___x_6516_);
                        v___x_6614_ = l_Lean_Meta_isProp(
                            v___x_6516_,
                            v___y_6411_,
                            v___y_6412_,
                            v___y_6413_,
                            v___y_6414_,
                        );
                        if crate::leanh::lean_obj_tag(v___x_6614_) == 0 {
                            v_a_6615_ = crate::leanh::lean_ctor_get(v___x_6614_, 0);
                            crate::leanh::lean_inc(v_a_6615_);
                            crate::leanh::lean_dec_ref_known(v___x_6614_, 1);
                            v___x_6690_ = (crate::leanh::lean_unbox(v_a_6615_) as u8);
                            crate::leanh::lean_dec(v_a_6615_);
                            if v___x_6690_ == 0 {
                                if v___x_6440_ == 0 {
                                    crate::leanh::lean_del_object(v___x_6436_);
                                    v___y_6617_ = v___x_6440_;
                                    state = 22;
                                    continue;
                                } else {
                                    crate::leanh::lean_dec_ref(v___x_6516_);
                                    crate::leanh::lean_dec(v_a_6439_);
                                    v___x_6691_ = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_intro1(v___x_6416_, v___y_6406_, v___y_6407_, v___y_6408_, v___y_6409_, v___y_6410_, v___y_6411_, v___y_6412_, v___y_6413_, v___y_6414_);
                                    crate::leanh::lean_dec_ref(v___y_6411_);
                                    if crate::leanh::lean_obj_tag(v___x_6691_) == 0 {
                                        v_a_6692_ = crate::leanh::lean_ctor_get(v___x_6691_, 0);
                                        crate::leanh::lean_inc(v_a_6692_);
                                        crate::leanh::lean_dec_ref_known(v___x_6691_, 1);
                                        v___x_6693_ = lean_st_ref_get(v___x_6416_);
                                        if v_isShared_6437_ == 0 {
                                            crate::leanh::lean_ctor_set_tag(v___x_6436_, 3);
                                            crate::leanh::lean_ctor_set(
                                                v___x_6436_,
                                                1,
                                                v___x_6693_,
                                            );
                                            crate::leanh::lean_ctor_set(v___x_6436_, 0, v_a_6692_);
                                            v___x_6695_ = v___x_6436_;
                                            state = 35;
                                            continue;
                                        } else {
                                            v_reuseFailAlloc_6696_ =
                                                crate::leanh::lean_alloc_ctor(3, 2, (0) as u32);
                                            crate::leanh::lean_ctor_set(
                                                v_reuseFailAlloc_6696_,
                                                0,
                                                v_a_6692_,
                                            );
                                            crate::leanh::lean_ctor_set(
                                                v_reuseFailAlloc_6696_,
                                                1,
                                                v___x_6693_,
                                            );
                                            v___x_6695_ = v_reuseFailAlloc_6696_;
                                            state = 35;
                                            continue;
                                        }
                                    } else {
                                        crate::leanh::lean_del_object(v___x_6436_);
                                        crate::leanh::lean_dec(v___x_6416_);
                                        v_a_6697_ = crate::leanh::lean_ctor_get(v___x_6691_, 0);
                                        v_isSharedCheck_6704_ =
                                            (!crate::leanh::lean_is_exclusive(v___x_6691_)) as u8;
                                        if v_isSharedCheck_6704_ == 0 {
                                            v___x_6699_ = v___x_6691_;
                                            v_isShared_6700_ = v_isSharedCheck_6704_;
                                            state = 36;
                                            continue;
                                        } else {
                                            crate::leanh::lean_inc(v_a_6697_);
                                            crate::leanh::lean_dec(v___x_6691_);
                                            v___x_6699_ = crate::leanh::lean_box(0);
                                            v_isShared_6700_ = v_isSharedCheck_6704_;
                                            state = 36;
                                            continue;
                                        }
                                    }
                                }
                            } else {
                                crate::leanh::lean_del_object(v___x_6436_);
                                v___x_6705_ = 0;
                                v___y_6617_ = v___x_6705_;
                                state = 22;
                                continue;
                            }
                        } else {
                            crate::leanh::lean_dec_ref(v___x_6516_);
                            crate::leanh::lean_dec(v_a_6439_);
                            crate::leanh::lean_del_object(v___x_6436_);
                            crate::leanh::lean_dec(v___x_6416_);
                            crate::leanh::lean_dec_ref(v___y_6411_);
                            v_a_6706_ = crate::leanh::lean_ctor_get(v___x_6614_, 0);
                            v_isSharedCheck_6713_ =
                                (!crate::leanh::lean_is_exclusive(v___x_6614_)) as u8;
                            if v_isSharedCheck_6713_ == 0 {
                                v___x_6708_ = v___x_6614_;
                                v_isShared_6709_ = v_isSharedCheck_6713_;
                                state = 38;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_6706_);
                                crate::leanh::lean_dec(v___x_6614_);
                                v___x_6708_ = crate::leanh::lean_box(0);
                                v_isShared_6709_ = v_isSharedCheck_6713_;
                                state = 38;
                                continue;
                            }
                        }
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_6436_);
                    crate::leanh::lean_dec(v___x_6416_);
                    crate::leanh::lean_dec_ref(v___y_6411_);
                    crate::leanh::lean_dec(v_generation_6405_);
                    crate::leanh::lean_dec_ref(v_goal_6404_);
                    v_a_6714_ = crate::leanh::lean_ctor_get(v___x_6438_, 0);
                    v_isSharedCheck_6721_ = (!crate::leanh::lean_is_exclusive(v___x_6438_)) as u8;
                    if v_isSharedCheck_6721_ == 0 {
                        v___x_6716_ = v___x_6438_;
                        v_isShared_6717_ = v_isSharedCheck_6721_;
                        state = 40;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_6714_);
                        crate::leanh::lean_dec(v___x_6438_);
                        v___x_6716_ = crate::leanh::lean_box(0);
                        v_isShared_6717_ = v_isSharedCheck_6721_;
                        state = 40;
                        continue;
                    }
                }
            }
            6 => {
                v___x_6461_ = 2;
                v___x_6462_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_6463_ = l_Lean_Meta_mkFreshExprMVarAt(
                    v___y_6447_,
                    v___y_6448_,
                    v___y_6460_,
                    v___x_6461_,
                    v___y_6454_,
                    v___x_6462_,
                    v___y_6459_,
                    v___y_6456_,
                    v___y_6455_,
                    v___y_6449_,
                );
                if crate::leanh::lean_obj_tag(v___x_6463_) == 0 {
                    v_a_6464_ = crate::leanh::lean_ctor_get(v___x_6463_, 0);
                    crate::leanh::lean_inc(v_a_6464_);
                    crate::leanh::lean_dec_ref_known(v___x_6463_, 1);
                    v___x_6465_ = l_Lean_Expr_mvarId_x21(v_a_6464_);
                    v___x_6466_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_6467_ = lean_mk_empty_array_with_capacity(v___x_6466_);
                    v___x_6468_ = lean_array_push(v___x_6467_, v___y_6451_);
                    v___x_6469_ = 1;
                    v___x_6470_ = crate::leanh::lean_box((v___y_6445_) as usize);
                    v___x_6471_ = crate::leanh::lean_box((v___x_6441_) as usize);
                    v___x_6472_ = crate::leanh::lean_box((v___x_6469_) as usize);
                    crate::leanh::lean_inc(v___x_6465_);
                    v___f_6473_ = crate::leanh::lean_alloc_closure(l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lam__2___boxed as *mut core::ffi::c_void, 19, 8);
                    crate::leanh::lean_closure_set(v___f_6473_, 0, v___x_6468_);
                    crate::leanh::lean_closure_set(v___f_6473_, 1, v_a_6464_);
                    crate::leanh::lean_closure_set(v___f_6473_, 2, v___x_6470_);
                    crate::leanh::lean_closure_set(v___f_6473_, 3, v___x_6471_);
                    crate::leanh::lean_closure_set(v___f_6473_, 4, v___x_6472_);
                    crate::leanh::lean_closure_set(v___f_6473_, 5, v___y_6444_);
                    crate::leanh::lean_closure_set(v___f_6473_, 6, v___x_6465_);
                    crate::leanh::lean_closure_set(v___f_6473_, 7, v___y_6443_);
                    v___x_6474_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__0___redArg(v___x_6465_, v___f_6473_, v___y_6452_, v___y_6457_, v___y_6453_, v___y_6458_, v___y_6446_, v___y_6450_, v___y_6459_, v___y_6456_, v___y_6455_, v___y_6449_);
                    crate::leanh::lean_dec_ref(v___y_6459_);
                    crate::leanh::lean_dec(v___y_6452_);
                    v___y_6423_ = v___x_6474_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_dec_ref(v___y_6459_);
                    crate::leanh::lean_dec(v___y_6452_);
                    crate::leanh::lean_dec_ref(v___y_6451_);
                    crate::leanh::lean_dec(v___y_6444_);
                    crate::leanh::lean_dec(v___y_6443_);
                    crate::leanh::lean_dec(v___x_6416_);
                    v_a_6475_ = crate::leanh::lean_ctor_get(v___x_6463_, 0);
                    v_isSharedCheck_6482_ = (!crate::leanh::lean_is_exclusive(v___x_6463_)) as u8;
                    if v_isSharedCheck_6482_ == 0 {
                        v___x_6477_ = v___x_6463_;
                        v_isShared_6478_ = v_isSharedCheck_6482_;
                        state = 7;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_6475_);
                        crate::leanh::lean_dec(v___x_6463_);
                        v___x_6477_ = crate::leanh::lean_box(0);
                        v_isShared_6478_ = v_isSharedCheck_6482_;
                        state = 7;
                        continue;
                    }
                }
            }
            7 => {
                if v_isShared_6478_ == 0 {
                    v___x_6480_ = v___x_6477_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_6481_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6481_, 0, v_a_6475_);
                    v___x_6480_ = v_reuseFailAlloc_6481_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_6480_;
            }
            9 => {
                if v_isShared_6497_ == 0 {
                    v___x_6499_ = v___x_6496_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_6500_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6500_, 0, v_a_6494_);
                    v___x_6499_ = v_reuseFailAlloc_6500_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_6499_;
            }
            11 => {
                if v_isShared_6511_ == 0 {
                    v___x_6513_ = v___x_6510_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_6514_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6514_, 0, v_a_6508_);
                    v___x_6513_ = v_reuseFailAlloc_6514_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                return v___x_6513_;
            }
            13 => {
                if crate::leanh::lean_obj_tag(v___y_6525_) == 0 {
                    crate::leanh::lean_dec_ref(v___y_6528_);
                    crate::leanh::lean_dec(v___y_6527_);
                    crate::leanh::lean_dec_ref(v___y_6519_);
                    crate::leanh::lean_dec_ref(v___x_6516_);
                    v___x_6541_ = l_Lean_Expr_isArrow(v_a_6439_);
                    crate::leanh::lean_dec(v_a_6439_);
                    if v___x_6541_ == 0 {
                        v___x_6542_ = lean_expr_instantiate1(v___y_6520_, v___y_6526_);
                        crate::leanh::lean_dec_ref(v___y_6520_);
                        v___y_6443_ = v___y_6518_;
                        v___y_6444_ = v___y_6521_;
                        v___y_6445_ = v___y_6522_;
                        v___y_6446_ = v___y_6535_;
                        v___y_6447_ = v___y_6523_;
                        v___y_6448_ = v_localInsts_6530_;
                        v___y_6449_ = v___y_6540_;
                        v___y_6450_ = v___y_6536_;
                        v___y_6451_ = v___y_6526_;
                        v___y_6452_ = v___y_6531_;
                        v___y_6453_ = v___y_6533_;
                        v___y_6454_ = v___y_6529_;
                        v___y_6455_ = v___y_6539_;
                        v___y_6456_ = v___y_6538_;
                        v___y_6457_ = v___y_6532_;
                        v___y_6458_ = v___y_6534_;
                        v___y_6459_ = v___y_6537_;
                        v___y_6460_ = v___x_6542_;
                        state = 6;
                        continue;
                    } else {
                        v___y_6443_ = v___y_6518_;
                        v___y_6444_ = v___y_6521_;
                        v___y_6445_ = v___y_6522_;
                        v___y_6446_ = v___y_6535_;
                        v___y_6447_ = v___y_6523_;
                        v___y_6448_ = v_localInsts_6530_;
                        v___y_6449_ = v___y_6540_;
                        v___y_6450_ = v___y_6536_;
                        v___y_6451_ = v___y_6526_;
                        v___y_6452_ = v___y_6531_;
                        v___y_6453_ = v___y_6533_;
                        v___y_6454_ = v___y_6529_;
                        v___y_6455_ = v___y_6539_;
                        v___y_6456_ = v___y_6538_;
                        v___y_6457_ = v___y_6532_;
                        v___y_6458_ = v___y_6534_;
                        v___y_6459_ = v___y_6537_;
                        v___y_6460_ = v___y_6520_;
                        state = 6;
                        continue;
                    }
                } else {
                    v_val_6543_ = crate::leanh::lean_ctor_get(v___y_6525_, 0);
                    crate::leanh::lean_inc(v_val_6543_);
                    crate::leanh::lean_dec_ref_known(v___y_6525_, 1);
                    v___x_6544_ = l_Lean_Expr_isArrow(v_a_6439_);
                    crate::leanh::lean_dec(v_a_6439_);
                    if v___x_6544_ == 0 {
                        crate::leanh::lean_inc_ref(v___y_6520_);
                        crate::leanh::lean_inc_ref_n(v___x_6516_, 2);
                        v___x_6545_ =
                            l_Lean_mkLambda(v___y_6527_, v___y_6524_, v___x_6516_, v___y_6520_);
                        v___x_6546_ = crate::leanh::lean_box(0);
                        v___x_6547_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lam__5___closed__4), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lam__5___closed__4_once), _init_l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lam__5___closed__4);
                        crate::leanh::lean_inc_ref(v___y_6526_);
                        crate::leanh::lean_inc(v_val_6543_);
                        v___x_6548_ = l_Lean_mkApp4(
                            v___x_6547_,
                            v___x_6516_,
                            v___y_6528_,
                            v_val_6543_,
                            v___y_6526_,
                        );
                        v___x_6549_ = lean_expr_instantiate1(v___y_6520_, v___x_6548_);
                        crate::leanh::lean_dec_ref(v___x_6548_);
                        crate::leanh::lean_dec_ref(v___y_6520_);
                        crate::leanh::lean_inc_ref(v___x_6549_);
                        v___x_6550_ = l_Lean_Meta_getLevel(
                            v___x_6549_,
                            v___y_6537_,
                            v___y_6538_,
                            v___y_6539_,
                            v___y_6540_,
                        );
                        if crate::leanh::lean_obj_tag(v___x_6550_) == 0 {
                            v_a_6551_ = crate::leanh::lean_ctor_get(v___x_6550_, 0);
                            crate::leanh::lean_inc(v_a_6551_);
                            crate::leanh::lean_dec_ref_known(v___x_6550_, 1);
                            v___x_6552_ = 2;
                            v___x_6553_ = crate::leanh::lean_unsigned_to_nat(0);
                            v___x_6554_ = l_Lean_Meta_mkFreshExprMVarAt(
                                v___y_6523_,
                                v_localInsts_6530_,
                                v___x_6549_,
                                v___x_6552_,
                                v___y_6529_,
                                v___x_6553_,
                                v___y_6537_,
                                v___y_6538_,
                                v___y_6539_,
                                v___y_6540_,
                            );
                            if crate::leanh::lean_obj_tag(v___x_6554_) == 0 {
                                v_a_6555_ = crate::leanh::lean_ctor_get(v___x_6554_, 0);
                                crate::leanh::lean_inc(v_a_6555_);
                                crate::leanh::lean_dec_ref_known(v___x_6554_, 1);
                                v___x_6556_ = l_Lean_Expr_mvarId_x21(v_a_6555_);
                                v___x_6557_ = crate::leanh::lean_unsigned_to_nat(1);
                                v___x_6558_ = lean_mk_empty_array_with_capacity(v___x_6557_);
                                v___x_6559_ = lean_array_push(v___x_6558_, v___y_6526_);
                                v___x_6560_ = 1;
                                v___x_6561_ = crate::leanh::lean_box((v___x_6544_) as usize);
                                v___x_6562_ = crate::leanh::lean_box((v___x_6441_) as usize);
                                v___x_6563_ = crate::leanh::lean_box((v___x_6560_) as usize);
                                crate::leanh::lean_inc(v___x_6556_);
                                v___f_6564_ = crate::leanh::lean_alloc_closure(l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lam__3___boxed as *mut core::ffi::c_void, 25, 14);
                                crate::leanh::lean_closure_set(v___f_6564_, 0, v___x_6559_);
                                crate::leanh::lean_closure_set(v___f_6564_, 1, v_a_6555_);
                                crate::leanh::lean_closure_set(v___f_6564_, 2, v___x_6561_);
                                crate::leanh::lean_closure_set(v___f_6564_, 3, v___x_6562_);
                                crate::leanh::lean_closure_set(v___f_6564_, 4, v___x_6563_);
                                crate::leanh::lean_closure_set(v___f_6564_, 5, v_a_6551_);
                                crate::leanh::lean_closure_set(v___f_6564_, 6, v___x_6546_);
                                crate::leanh::lean_closure_set(v___f_6564_, 7, v___x_6516_);
                                crate::leanh::lean_closure_set(v___f_6564_, 8, v___y_6519_);
                                crate::leanh::lean_closure_set(v___f_6564_, 9, v___x_6545_);
                                crate::leanh::lean_closure_set(v___f_6564_, 10, v_val_6543_);
                                crate::leanh::lean_closure_set(v___f_6564_, 11, v___y_6521_);
                                crate::leanh::lean_closure_set(v___f_6564_, 12, v___x_6556_);
                                crate::leanh::lean_closure_set(v___f_6564_, 13, v___y_6518_);
                                v___x_6565_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__0___redArg(v___x_6556_, v___f_6564_, v___y_6531_, v___y_6532_, v___y_6533_, v___y_6534_, v___y_6535_, v___y_6536_, v___y_6537_, v___y_6538_, v___y_6539_, v___y_6540_);
                                crate::leanh::lean_dec_ref(v___y_6537_);
                                crate::leanh::lean_dec(v___y_6531_);
                                v___y_6423_ = v___x_6565_;
                                state = 2;
                                continue;
                            } else {
                                crate::leanh::lean_dec(v_a_6551_);
                                crate::leanh::lean_dec_ref(v___x_6545_);
                                crate::leanh::lean_dec(v_val_6543_);
                                crate::leanh::lean_dec_ref(v___y_6537_);
                                crate::leanh::lean_dec(v___y_6531_);
                                crate::leanh::lean_dec_ref(v___y_6526_);
                                crate::leanh::lean_dec(v___y_6521_);
                                crate::leanh::lean_dec_ref(v___y_6519_);
                                crate::leanh::lean_dec(v___y_6518_);
                                crate::leanh::lean_dec_ref(v___x_6516_);
                                crate::leanh::lean_dec(v___x_6416_);
                                v_a_6566_ = crate::leanh::lean_ctor_get(v___x_6554_, 0);
                                v_isSharedCheck_6573_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_6554_)) as u8;
                                if v_isSharedCheck_6573_ == 0 {
                                    v___x_6568_ = v___x_6554_;
                                    v_isShared_6569_ = v_isSharedCheck_6573_;
                                    state = 14;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_a_6566_);
                                    crate::leanh::lean_dec(v___x_6554_);
                                    v___x_6568_ = crate::leanh::lean_box(0);
                                    v_isShared_6569_ = v_isSharedCheck_6573_;
                                    state = 14;
                                    continue;
                                }
                            }
                        } else {
                            crate::leanh::lean_dec_ref(v___x_6549_);
                            crate::leanh::lean_dec_ref(v___x_6545_);
                            crate::leanh::lean_dec(v_val_6543_);
                            crate::leanh::lean_dec_ref(v___y_6537_);
                            crate::leanh::lean_dec(v___y_6531_);
                            crate::leanh::lean_dec_ref(v_localInsts_6530_);
                            crate::leanh::lean_dec(v___y_6529_);
                            crate::leanh::lean_dec_ref(v___y_6526_);
                            crate::leanh::lean_dec_ref(v___y_6523_);
                            crate::leanh::lean_dec(v___y_6521_);
                            crate::leanh::lean_dec_ref(v___y_6519_);
                            crate::leanh::lean_dec(v___y_6518_);
                            crate::leanh::lean_dec_ref(v___x_6516_);
                            crate::leanh::lean_dec(v___x_6416_);
                            v_a_6574_ = crate::leanh::lean_ctor_get(v___x_6550_, 0);
                            v_isSharedCheck_6581_ =
                                (!crate::leanh::lean_is_exclusive(v___x_6550_)) as u8;
                            if v_isSharedCheck_6581_ == 0 {
                                v___x_6576_ = v___x_6550_;
                                v_isShared_6577_ = v_isSharedCheck_6581_;
                                state = 16;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_6574_);
                                crate::leanh::lean_dec(v___x_6550_);
                                v___x_6576_ = crate::leanh::lean_box(0);
                                v_isShared_6577_ = v_isSharedCheck_6581_;
                                state = 16;
                                continue;
                            }
                        }
                    } else {
                        crate::leanh::lean_dec_ref(v___y_6528_);
                        crate::leanh::lean_dec(v___y_6527_);
                        crate::leanh::lean_inc_ref(v___y_6520_);
                        v___x_6582_ = l_Lean_Meta_getLevel(
                            v___y_6520_,
                            v___y_6537_,
                            v___y_6538_,
                            v___y_6539_,
                            v___y_6540_,
                        );
                        if crate::leanh::lean_obj_tag(v___x_6582_) == 0 {
                            v_a_6583_ = crate::leanh::lean_ctor_get(v___x_6582_, 0);
                            crate::leanh::lean_inc(v_a_6583_);
                            crate::leanh::lean_dec_ref_known(v___x_6582_, 1);
                            v___x_6584_ = 2;
                            v___x_6585_ = crate::leanh::lean_unsigned_to_nat(0);
                            crate::leanh::lean_inc_ref(v___y_6520_);
                            v___x_6586_ = l_Lean_Meta_mkFreshExprMVarAt(
                                v___y_6523_,
                                v_localInsts_6530_,
                                v___y_6520_,
                                v___x_6584_,
                                v___y_6529_,
                                v___x_6585_,
                                v___y_6537_,
                                v___y_6538_,
                                v___y_6539_,
                                v___y_6540_,
                            );
                            if crate::leanh::lean_obj_tag(v___x_6586_) == 0 {
                                v_a_6587_ = crate::leanh::lean_ctor_get(v___x_6586_, 0);
                                crate::leanh::lean_inc(v_a_6587_);
                                crate::leanh::lean_dec_ref_known(v___x_6586_, 1);
                                v___x_6588_ = l_Lean_Expr_mvarId_x21(v_a_6587_);
                                v___x_6589_ = crate::leanh::lean_unsigned_to_nat(1);
                                v___x_6590_ = lean_mk_empty_array_with_capacity(v___x_6589_);
                                v___x_6591_ = lean_array_push(v___x_6590_, v___y_6526_);
                                v___x_6592_ = 1;
                                v___x_6593_ = crate::leanh::lean_box((v___y_6522_) as usize);
                                v___x_6594_ = crate::leanh::lean_box((v___x_6441_) as usize);
                                v___x_6595_ = crate::leanh::lean_box((v___x_6592_) as usize);
                                crate::leanh::lean_inc(v___x_6588_);
                                v___f_6596_ = crate::leanh::lean_alloc_closure(l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lam__4___boxed as *mut core::ffi::c_void, 24, 13);
                                crate::leanh::lean_closure_set(v___f_6596_, 0, v___x_6591_);
                                crate::leanh::lean_closure_set(v___f_6596_, 1, v_a_6587_);
                                crate::leanh::lean_closure_set(v___f_6596_, 2, v___x_6593_);
                                crate::leanh::lean_closure_set(v___f_6596_, 3, v___x_6594_);
                                crate::leanh::lean_closure_set(v___f_6596_, 4, v___x_6595_);
                                crate::leanh::lean_closure_set(v___f_6596_, 5, v_a_6583_);
                                crate::leanh::lean_closure_set(v___f_6596_, 6, v___x_6516_);
                                crate::leanh::lean_closure_set(v___f_6596_, 7, v___y_6519_);
                                crate::leanh::lean_closure_set(v___f_6596_, 8, v___y_6520_);
                                crate::leanh::lean_closure_set(v___f_6596_, 9, v_val_6543_);
                                crate::leanh::lean_closure_set(v___f_6596_, 10, v___y_6521_);
                                crate::leanh::lean_closure_set(v___f_6596_, 11, v___x_6588_);
                                crate::leanh::lean_closure_set(v___f_6596_, 12, v___y_6518_);
                                v___x_6597_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__0___redArg(v___x_6588_, v___f_6596_, v___y_6531_, v___y_6532_, v___y_6533_, v___y_6534_, v___y_6535_, v___y_6536_, v___y_6537_, v___y_6538_, v___y_6539_, v___y_6540_);
                                crate::leanh::lean_dec_ref(v___y_6537_);
                                crate::leanh::lean_dec(v___y_6531_);
                                v___y_6423_ = v___x_6597_;
                                state = 2;
                                continue;
                            } else {
                                crate::leanh::lean_dec(v_a_6583_);
                                crate::leanh::lean_dec(v_val_6543_);
                                crate::leanh::lean_dec_ref(v___y_6537_);
                                crate::leanh::lean_dec(v___y_6531_);
                                crate::leanh::lean_dec_ref(v___y_6526_);
                                crate::leanh::lean_dec(v___y_6521_);
                                crate::leanh::lean_dec_ref(v___y_6520_);
                                crate::leanh::lean_dec_ref(v___y_6519_);
                                crate::leanh::lean_dec(v___y_6518_);
                                crate::leanh::lean_dec_ref(v___x_6516_);
                                crate::leanh::lean_dec(v___x_6416_);
                                v_a_6598_ = crate::leanh::lean_ctor_get(v___x_6586_, 0);
                                v_isSharedCheck_6605_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_6586_)) as u8;
                                if v_isSharedCheck_6605_ == 0 {
                                    v___x_6600_ = v___x_6586_;
                                    v_isShared_6601_ = v_isSharedCheck_6605_;
                                    state = 18;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_a_6598_);
                                    crate::leanh::lean_dec(v___x_6586_);
                                    v___x_6600_ = crate::leanh::lean_box(0);
                                    v_isShared_6601_ = v_isSharedCheck_6605_;
                                    state = 18;
                                    continue;
                                }
                            }
                        } else {
                            crate::leanh::lean_dec(v_val_6543_);
                            crate::leanh::lean_dec_ref(v___y_6537_);
                            crate::leanh::lean_dec(v___y_6531_);
                            crate::leanh::lean_dec_ref(v_localInsts_6530_);
                            crate::leanh::lean_dec(v___y_6529_);
                            crate::leanh::lean_dec_ref(v___y_6526_);
                            crate::leanh::lean_dec_ref(v___y_6523_);
                            crate::leanh::lean_dec(v___y_6521_);
                            crate::leanh::lean_dec_ref(v___y_6520_);
                            crate::leanh::lean_dec_ref(v___y_6519_);
                            crate::leanh::lean_dec(v___y_6518_);
                            crate::leanh::lean_dec_ref(v___x_6516_);
                            crate::leanh::lean_dec(v___x_6416_);
                            v_a_6606_ = crate::leanh::lean_ctor_get(v___x_6582_, 0);
                            v_isSharedCheck_6613_ =
                                (!crate::leanh::lean_is_exclusive(v___x_6582_)) as u8;
                            if v_isSharedCheck_6613_ == 0 {
                                v___x_6608_ = v___x_6582_;
                                v_isShared_6609_ = v_isSharedCheck_6613_;
                                state = 20;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_6606_);
                                crate::leanh::lean_dec(v___x_6582_);
                                v___x_6608_ = crate::leanh::lean_box(0);
                                v_isShared_6609_ = v_isSharedCheck_6613_;
                                state = 20;
                                continue;
                            }
                        }
                    }
                }
            }
            14 => {
                if v_isShared_6569_ == 0 {
                    v___x_6571_ = v___x_6568_;
                    state = 15;
                    continue;
                } else {
                    v_reuseFailAlloc_6572_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6572_, 0, v_a_6566_);
                    v___x_6571_ = v_reuseFailAlloc_6572_;
                    state = 15;
                    continue;
                }
            }
            15 => {
                return v___x_6571_;
            }
            16 => {
                if v_isShared_6577_ == 0 {
                    v___x_6579_ = v___x_6576_;
                    state = 17;
                    continue;
                } else {
                    v_reuseFailAlloc_6580_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6580_, 0, v_a_6574_);
                    v___x_6579_ = v_reuseFailAlloc_6580_;
                    state = 17;
                    continue;
                }
            }
            17 => {
                return v___x_6579_;
            }
            18 => {
                if v_isShared_6601_ == 0 {
                    v___x_6603_ = v___x_6600_;
                    state = 19;
                    continue;
                } else {
                    v_reuseFailAlloc_6604_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6604_, 0, v_a_6598_);
                    v___x_6603_ = v_reuseFailAlloc_6604_;
                    state = 19;
                    continue;
                }
            }
            19 => {
                return v___x_6603_;
            }
            20 => {
                if v_isShared_6609_ == 0 {
                    v___x_6611_ = v___x_6608_;
                    state = 21;
                    continue;
                } else {
                    v_reuseFailAlloc_6612_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6612_, 0, v_a_6606_);
                    v___x_6611_ = v_reuseFailAlloc_6612_;
                    state = 21;
                    continue;
                }
            }
            21 => {
                return v___x_6611_;
            }
            22 => {
                v___x_6618_ = lean_st_ref_get(v___x_6416_);
                v_mvarId_6619_ = crate::leanh::lean_ctor_get(v___x_6618_, 1);
                v_isSharedCheck_6688_ = (!crate::leanh::lean_is_exclusive(v___x_6618_)) as u8;
                if v_isSharedCheck_6688_ == 0 {
                    v_unused_6689_ = crate::leanh::lean_ctor_get(v___x_6618_, 0);
                    crate::leanh::lean_dec(v_unused_6689_);
                    v___x_6621_ = v___x_6618_;
                    v_isShared_6622_ = v_isSharedCheck_6688_;
                    state = 23;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_mvarId_6619_);
                    crate::leanh::lean_dec(v___x_6618_);
                    v___x_6621_ = crate::leanh::lean_box(0);
                    v_isShared_6622_ = v_isSharedCheck_6688_;
                    state = 23;
                    continue;
                }
            }
            23 => {
                crate::leanh::lean_inc(v_mvarId_6619_);
                v___x_6623_ = l_Lean_MVarId_getTag(
                    v_mvarId_6619_,
                    v___y_6411_,
                    v___y_6412_,
                    v___y_6413_,
                    v___y_6414_,
                );
                if crate::leanh::lean_obj_tag(v___x_6623_) == 0 {
                    v_a_6624_ = crate::leanh::lean_ctor_get(v___x_6623_, 0);
                    crate::leanh::lean_inc(v_a_6624_);
                    crate::leanh::lean_dec_ref_known(v___x_6623_, 1);
                    v___x_6625_ = l_Lean_mkFreshFVarId___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__2(v___x_6416_, v___y_6406_, v___y_6407_, v___y_6408_, v___y_6409_, v___y_6410_, v___y_6411_, v___y_6412_, v___y_6413_, v___y_6414_);
                    if crate::leanh::lean_obj_tag(v___x_6625_) == 0 {
                        v_a_6626_ = crate::leanh::lean_ctor_get(v___x_6625_, 0);
                        crate::leanh::lean_inc(v_a_6626_);
                        crate::leanh::lean_dec_ref_known(v___x_6625_, 1);
                        crate::leanh::lean_inc_ref(v___x_6516_);
                        v___x_6627_ = l_Lean_Meta_Grind_preprocessHypothesis(
                            v___x_6516_,
                            v___x_6416_,
                            v___y_6406_,
                            v___y_6407_,
                            v___y_6408_,
                            v___y_6409_,
                            v___y_6410_,
                            v___y_6411_,
                            v___y_6412_,
                            v___y_6413_,
                            v___y_6414_,
                        );
                        if crate::leanh::lean_obj_tag(v___x_6627_) == 0 {
                            v_a_6628_ = crate::leanh::lean_ctor_get(v___x_6627_, 0);
                            crate::leanh::lean_inc(v_a_6628_);
                            crate::leanh::lean_dec_ref_known(v___x_6627_, 1);
                            v_expr_6629_ = crate::leanh::lean_ctor_get(v_a_6628_, 0);
                            crate::leanh::lean_inc_ref_n(v_expr_6629_, 2);
                            v_proof_x3f_6630_ = crate::leanh::lean_ctor_get(v_a_6628_, 1);
                            crate::leanh::lean_inc(v_proof_x3f_6630_);
                            crate::leanh::lean_dec(v_a_6628_);
                            v___x_6631_ = l_Lean_Expr_bindingName_x21(v_a_6439_);
                            crate::leanh::lean_inc(v___x_6631_);
                            v___x_6632_ = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName(v___x_6631_, v_expr_6629_, v___x_6416_, v___y_6406_, v___y_6407_, v___y_6408_, v___y_6409_, v___y_6410_, v___y_6411_, v___y_6412_, v___y_6413_, v___y_6414_);
                            if crate::leanh::lean_obj_tag(v___x_6632_) == 0 {
                                v_a_6633_ = crate::leanh::lean_ctor_get(v___x_6632_, 0);
                                crate::leanh::lean_inc(v_a_6633_);
                                crate::leanh::lean_dec_ref_known(v___x_6632_, 1);
                                v_lctx_6634_ = crate::leanh::lean_ctor_get(v___y_6411_, 2);
                                v_localInstances_6635_ =
                                    crate::leanh::lean_ctor_get(v___y_6411_, 3);
                                crate::leanh::lean_inc_n(v_a_6626_, 2);
                                v___x_6636_ = l_Lean_mkFVar(v_a_6626_);
                                v___x_6637_ = l_Lean_Expr_bindingInfo_x21(v_a_6439_);
                                v___x_6638_ = 0;
                                crate::leanh::lean_inc_ref_n(v_expr_6629_, 2);
                                crate::leanh::lean_inc_ref(v_lctx_6634_);
                                v___x_6639_ = l_Lean_LocalContext_mkLocalDecl(
                                    v_lctx_6634_,
                                    v_a_6626_,
                                    v_a_6633_,
                                    v_expr_6629_,
                                    v___x_6637_,
                                    v___x_6638_,
                                );
                                v___x_6640_ = l_Lean_Meta_isClass_x3f(
                                    v_expr_6629_,
                                    v___y_6411_,
                                    v___y_6412_,
                                    v___y_6413_,
                                    v___y_6414_,
                                );
                                if crate::leanh::lean_obj_tag(v___x_6640_) == 0 {
                                    v_a_6641_ = crate::leanh::lean_ctor_get(v___x_6640_, 0);
                                    crate::leanh::lean_inc(v_a_6641_);
                                    crate::leanh::lean_dec_ref_known(v___x_6640_, 1);
                                    v___x_6642_ = l_Lean_Expr_bindingBody_x21(v_a_6439_);
                                    if crate::leanh::lean_obj_tag(v_a_6641_) == 1 {
                                        v_val_6643_ = crate::leanh::lean_ctor_get(v_a_6641_, 0);
                                        crate::leanh::lean_inc(v_val_6643_);
                                        crate::leanh::lean_dec_ref_known(v_a_6641_, 1);
                                        crate::leanh::lean_inc_ref(v___x_6636_);
                                        if v_isShared_6622_ == 0 {
                                            crate::leanh::lean_ctor_set(
                                                v___x_6621_,
                                                1,
                                                v___x_6636_,
                                            );
                                            crate::leanh::lean_ctor_set(
                                                v___x_6621_,
                                                0,
                                                v_val_6643_,
                                            );
                                            v___x_6645_ = v___x_6621_;
                                            state = 24;
                                            continue;
                                        } else {
                                            v_reuseFailAlloc_6647_ =
                                                crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                                            crate::leanh::lean_ctor_set(
                                                v_reuseFailAlloc_6647_,
                                                0,
                                                v_val_6643_,
                                            );
                                            crate::leanh::lean_ctor_set(
                                                v_reuseFailAlloc_6647_,
                                                1,
                                                v___x_6636_,
                                            );
                                            v___x_6645_ = v_reuseFailAlloc_6647_;
                                            state = 24;
                                            continue;
                                        }
                                    } else {
                                        crate::leanh::lean_inc_ref(v_localInstances_6635_);
                                        crate::leanh::lean_dec(v_a_6641_);
                                        crate::leanh::lean_del_object(v___x_6621_);
                                        crate::leanh::lean_inc(v___x_6416_);
                                        crate::leanh::lean_inc_ref(v_expr_6629_);
                                        v___y_6518_ = v_a_6626_;
                                        v___y_6519_ = v_expr_6629_;
                                        v___y_6520_ = v___x_6642_;
                                        v___y_6521_ = v_mvarId_6619_;
                                        v___y_6522_ = v___y_6617_;
                                        v___y_6523_ = v___x_6639_;
                                        v___y_6524_ = v___x_6637_;
                                        v___y_6525_ = v_proof_x3f_6630_;
                                        v___y_6526_ = v___x_6636_;
                                        v___y_6527_ = v___x_6631_;
                                        v___y_6528_ = v_expr_6629_;
                                        v___y_6529_ = v_a_6624_;
                                        v_localInsts_6530_ = v_localInstances_6635_;
                                        v___y_6531_ = v___x_6416_;
                                        v___y_6532_ = v___y_6406_;
                                        v___y_6533_ = v___y_6407_;
                                        v___y_6534_ = v___y_6408_;
                                        v___y_6535_ = v___y_6409_;
                                        v___y_6536_ = v___y_6410_;
                                        v___y_6537_ = v___y_6411_;
                                        v___y_6538_ = v___y_6412_;
                                        v___y_6539_ = v___y_6413_;
                                        v___y_6540_ = v___y_6414_;
                                        state = 13;
                                        continue;
                                    }
                                } else {
                                    crate::leanh::lean_dec_ref(v___x_6639_);
                                    crate::leanh::lean_dec_ref(v___x_6636_);
                                    crate::leanh::lean_dec(v___x_6631_);
                                    crate::leanh::lean_dec(v_proof_x3f_6630_);
                                    crate::leanh::lean_dec_ref(v_expr_6629_);
                                    crate::leanh::lean_dec(v_a_6626_);
                                    crate::leanh::lean_dec(v_a_6624_);
                                    crate::leanh::lean_del_object(v___x_6621_);
                                    crate::leanh::lean_dec(v_mvarId_6619_);
                                    crate::leanh::lean_dec_ref(v___x_6516_);
                                    crate::leanh::lean_dec(v_a_6439_);
                                    crate::leanh::lean_dec(v___x_6416_);
                                    crate::leanh::lean_dec_ref(v___y_6411_);
                                    v_a_6648_ = crate::leanh::lean_ctor_get(v___x_6640_, 0);
                                    v_isSharedCheck_6655_ =
                                        (!crate::leanh::lean_is_exclusive(v___x_6640_)) as u8;
                                    if v_isSharedCheck_6655_ == 0 {
                                        v___x_6650_ = v___x_6640_;
                                        v_isShared_6651_ = v_isSharedCheck_6655_;
                                        state = 25;
                                        continue;
                                    } else {
                                        crate::leanh::lean_inc(v_a_6648_);
                                        crate::leanh::lean_dec(v___x_6640_);
                                        v___x_6650_ = crate::leanh::lean_box(0);
                                        v_isShared_6651_ = v_isSharedCheck_6655_;
                                        state = 25;
                                        continue;
                                    }
                                }
                            } else {
                                crate::leanh::lean_dec(v___x_6631_);
                                crate::leanh::lean_dec(v_proof_x3f_6630_);
                                crate::leanh::lean_dec_ref(v_expr_6629_);
                                crate::leanh::lean_dec(v_a_6626_);
                                crate::leanh::lean_dec(v_a_6624_);
                                crate::leanh::lean_del_object(v___x_6621_);
                                crate::leanh::lean_dec(v_mvarId_6619_);
                                crate::leanh::lean_dec_ref(v___x_6516_);
                                crate::leanh::lean_dec(v_a_6439_);
                                crate::leanh::lean_dec(v___x_6416_);
                                crate::leanh::lean_dec_ref(v___y_6411_);
                                v_a_6656_ = crate::leanh::lean_ctor_get(v___x_6632_, 0);
                                v_isSharedCheck_6663_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_6632_)) as u8;
                                if v_isSharedCheck_6663_ == 0 {
                                    v___x_6658_ = v___x_6632_;
                                    v_isShared_6659_ = v_isSharedCheck_6663_;
                                    state = 27;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_a_6656_);
                                    crate::leanh::lean_dec(v___x_6632_);
                                    v___x_6658_ = crate::leanh::lean_box(0);
                                    v_isShared_6659_ = v_isSharedCheck_6663_;
                                    state = 27;
                                    continue;
                                }
                            }
                        } else {
                            crate::leanh::lean_dec(v_a_6626_);
                            crate::leanh::lean_dec(v_a_6624_);
                            crate::leanh::lean_del_object(v___x_6621_);
                            crate::leanh::lean_dec(v_mvarId_6619_);
                            crate::leanh::lean_dec_ref(v___x_6516_);
                            crate::leanh::lean_dec(v_a_6439_);
                            crate::leanh::lean_dec(v___x_6416_);
                            crate::leanh::lean_dec_ref(v___y_6411_);
                            v_a_6664_ = crate::leanh::lean_ctor_get(v___x_6627_, 0);
                            v_isSharedCheck_6671_ =
                                (!crate::leanh::lean_is_exclusive(v___x_6627_)) as u8;
                            if v_isSharedCheck_6671_ == 0 {
                                v___x_6666_ = v___x_6627_;
                                v_isShared_6667_ = v_isSharedCheck_6671_;
                                state = 29;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_6664_);
                                crate::leanh::lean_dec(v___x_6627_);
                                v___x_6666_ = crate::leanh::lean_box(0);
                                v_isShared_6667_ = v_isSharedCheck_6671_;
                                state = 29;
                                continue;
                            }
                        }
                    } else {
                        crate::leanh::lean_dec(v_a_6624_);
                        crate::leanh::lean_del_object(v___x_6621_);
                        crate::leanh::lean_dec(v_mvarId_6619_);
                        crate::leanh::lean_dec_ref(v___x_6516_);
                        crate::leanh::lean_dec(v_a_6439_);
                        crate::leanh::lean_dec(v___x_6416_);
                        crate::leanh::lean_dec_ref(v___y_6411_);
                        v_a_6672_ = crate::leanh::lean_ctor_get(v___x_6625_, 0);
                        v_isSharedCheck_6679_ =
                            (!crate::leanh::lean_is_exclusive(v___x_6625_)) as u8;
                        if v_isSharedCheck_6679_ == 0 {
                            v___x_6674_ = v___x_6625_;
                            v_isShared_6675_ = v_isSharedCheck_6679_;
                            state = 31;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_6672_);
                            crate::leanh::lean_dec(v___x_6625_);
                            v___x_6674_ = crate::leanh::lean_box(0);
                            v_isShared_6675_ = v_isSharedCheck_6679_;
                            state = 31;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_6621_);
                    crate::leanh::lean_dec(v_mvarId_6619_);
                    crate::leanh::lean_dec_ref(v___x_6516_);
                    crate::leanh::lean_dec(v_a_6439_);
                    crate::leanh::lean_dec(v___x_6416_);
                    crate::leanh::lean_dec_ref(v___y_6411_);
                    v_a_6680_ = crate::leanh::lean_ctor_get(v___x_6623_, 0);
                    v_isSharedCheck_6687_ = (!crate::leanh::lean_is_exclusive(v___x_6623_)) as u8;
                    if v_isSharedCheck_6687_ == 0 {
                        v___x_6682_ = v___x_6623_;
                        v_isShared_6683_ = v_isSharedCheck_6687_;
                        state = 33;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_6680_);
                        crate::leanh::lean_dec(v___x_6623_);
                        v___x_6682_ = crate::leanh::lean_box(0);
                        v_isShared_6683_ = v_isSharedCheck_6687_;
                        state = 33;
                        continue;
                    }
                }
            }
            24 => {
                crate::leanh::lean_inc_ref(v_localInstances_6635_);
                v___x_6646_ = lean_array_push(v_localInstances_6635_, v___x_6645_);
                crate::leanh::lean_inc(v___x_6416_);
                crate::leanh::lean_inc_ref(v_expr_6629_);
                v___y_6518_ = v_a_6626_;
                v___y_6519_ = v_expr_6629_;
                v___y_6520_ = v___x_6642_;
                v___y_6521_ = v_mvarId_6619_;
                v___y_6522_ = v___y_6617_;
                v___y_6523_ = v___x_6639_;
                v___y_6524_ = v___x_6637_;
                v___y_6525_ = v_proof_x3f_6630_;
                v___y_6526_ = v___x_6636_;
                v___y_6527_ = v___x_6631_;
                v___y_6528_ = v_expr_6629_;
                v___y_6529_ = v_a_6624_;
                v_localInsts_6530_ = v___x_6646_;
                v___y_6531_ = v___x_6416_;
                v___y_6532_ = v___y_6406_;
                v___y_6533_ = v___y_6407_;
                v___y_6534_ = v___y_6408_;
                v___y_6535_ = v___y_6409_;
                v___y_6536_ = v___y_6410_;
                v___y_6537_ = v___y_6411_;
                v___y_6538_ = v___y_6412_;
                v___y_6539_ = v___y_6413_;
                v___y_6540_ = v___y_6414_;
                state = 13;
                continue;
            }
            25 => {
                if v_isShared_6651_ == 0 {
                    v___x_6653_ = v___x_6650_;
                    state = 26;
                    continue;
                } else {
                    v_reuseFailAlloc_6654_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6654_, 0, v_a_6648_);
                    v___x_6653_ = v_reuseFailAlloc_6654_;
                    state = 26;
                    continue;
                }
            }
            26 => {
                return v___x_6653_;
            }
            27 => {
                if v_isShared_6659_ == 0 {
                    v___x_6661_ = v___x_6658_;
                    state = 28;
                    continue;
                } else {
                    v_reuseFailAlloc_6662_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6662_, 0, v_a_6656_);
                    v___x_6661_ = v_reuseFailAlloc_6662_;
                    state = 28;
                    continue;
                }
            }
            28 => {
                return v___x_6661_;
            }
            29 => {
                if v_isShared_6667_ == 0 {
                    v___x_6669_ = v___x_6666_;
                    state = 30;
                    continue;
                } else {
                    v_reuseFailAlloc_6670_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6670_, 0, v_a_6664_);
                    v___x_6669_ = v_reuseFailAlloc_6670_;
                    state = 30;
                    continue;
                }
            }
            30 => {
                return v___x_6669_;
            }
            31 => {
                if v_isShared_6675_ == 0 {
                    v___x_6677_ = v___x_6674_;
                    state = 32;
                    continue;
                } else {
                    v_reuseFailAlloc_6678_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6678_, 0, v_a_6672_);
                    v___x_6677_ = v_reuseFailAlloc_6678_;
                    state = 32;
                    continue;
                }
            }
            32 => {
                return v___x_6677_;
            }
            33 => {
                if v_isShared_6683_ == 0 {
                    v___x_6685_ = v___x_6682_;
                    state = 34;
                    continue;
                } else {
                    v_reuseFailAlloc_6686_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6686_, 0, v_a_6680_);
                    v___x_6685_ = v_reuseFailAlloc_6686_;
                    state = 34;
                    continue;
                }
            }
            34 => {
                return v___x_6685_;
            }
            35 => {
                v_a_6418_ = v___x_6695_;
                state = 1;
                continue;
            }
            36 => {
                if v_isShared_6700_ == 0 {
                    v___x_6702_ = v___x_6699_;
                    state = 37;
                    continue;
                } else {
                    v_reuseFailAlloc_6703_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6703_, 0, v_a_6697_);
                    v___x_6702_ = v_reuseFailAlloc_6703_;
                    state = 37;
                    continue;
                }
            }
            37 => {
                return v___x_6702_;
            }
            38 => {
                if v_isShared_6709_ == 0 {
                    v___x_6711_ = v___x_6708_;
                    state = 39;
                    continue;
                } else {
                    v_reuseFailAlloc_6712_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6712_, 0, v_a_6706_);
                    v___x_6711_ = v_reuseFailAlloc_6712_;
                    state = 39;
                    continue;
                }
            }
            39 => {
                return v___x_6711_;
            }
            40 => {
                if v_isShared_6717_ == 0 {
                    v___x_6719_ = v___x_6716_;
                    state = 41;
                    continue;
                } else {
                    v_reuseFailAlloc_6720_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6720_, 0, v_a_6714_);
                    v___x_6719_ = v_reuseFailAlloc_6720_;
                    state = 41;
                    continue;
                }
            }
            41 => {
                return v___x_6719_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lam__5___boxed(
    mut v_goal_6724_: *mut crate::leanh::LeanObject,
    mut v_generation_6725_: *mut crate::leanh::LeanObject,
    mut v___y_6726_: *mut crate::leanh::LeanObject,
    mut v___y_6727_: *mut crate::leanh::LeanObject,
    mut v___y_6728_: *mut crate::leanh::LeanObject,
    mut v___y_6729_: *mut crate::leanh::LeanObject,
    mut v___y_6730_: *mut crate::leanh::LeanObject,
    mut v___y_6731_: *mut crate::leanh::LeanObject,
    mut v___y_6732_: *mut crate::leanh::LeanObject,
    mut v___y_6733_: *mut crate::leanh::LeanObject,
    mut v___y_6734_: *mut crate::leanh::LeanObject,
    mut v___y_6735_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6736_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6736_ = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lam__5(
        v_goal_6724_,
        v_generation_6725_,
        v___y_6726_,
        v___y_6727_,
        v___y_6728_,
        v___y_6729_,
        v___y_6730_,
        v___y_6731_,
        v___y_6732_,
        v___y_6733_,
        v___y_6734_,
    );
    crate::leanh::lean_dec(v___y_6734_);
    crate::leanh::lean_dec_ref(v___y_6733_);
    crate::leanh::lean_dec(v___y_6732_);
    crate::leanh::lean_dec(v___y_6730_);
    crate::leanh::lean_dec_ref(v___y_6729_);
    crate::leanh::lean_dec(v___y_6728_);
    crate::leanh::lean_dec_ref(v___y_6727_);
    crate::leanh::lean_dec(v___y_6726_);
    return v_res_6736_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext(
    mut v_goal_6737_: *mut crate::leanh::LeanObject,
    mut v_generation_6738_: *mut crate::leanh::LeanObject,
    mut v_a_6739_: *mut crate::leanh::LeanObject,
    mut v_a_6740_: *mut crate::leanh::LeanObject,
    mut v_a_6741_: *mut crate::leanh::LeanObject,
    mut v_a_6742_: *mut crate::leanh::LeanObject,
    mut v_a_6743_: *mut crate::leanh::LeanObject,
    mut v_a_6744_: *mut crate::leanh::LeanObject,
    mut v_a_6745_: *mut crate::leanh::LeanObject,
    mut v_a_6746_: *mut crate::leanh::LeanObject,
    mut v_a_6747_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_mvarId_6749_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_6750_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6751_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6752_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6754_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6755_: u8 = 0;
    let mut v_fst_6756_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6758_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6759_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6760_: u8 = 0;
    let mut v_a_6761_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6763_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6764_: u8 = 0;
    let mut v___x_6766_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6767_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6768_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_mvarId_6749_ = crate::leanh::lean_ctor_get(v_goal_6737_, 1);
                crate::leanh::lean_inc(v_mvarId_6749_);
                v___f_6750_ = crate::leanh::lean_alloc_closure(l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lam__5___boxed as *mut core::ffi::c_void, 12, 2);
                crate::leanh::lean_closure_set(v___f_6750_, 0, v_goal_6737_);
                crate::leanh::lean_closure_set(v___f_6750_, 1, v_generation_6738_);
                v___x_6751_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__3___redArg(v_mvarId_6749_, v___f_6750_, v_a_6739_, v_a_6740_, v_a_6741_, v_a_6742_, v_a_6743_, v_a_6744_, v_a_6745_, v_a_6746_, v_a_6747_);
                if crate::leanh::lean_obj_tag(v___x_6751_) == 0 {
                    v_a_6752_ = crate::leanh::lean_ctor_get(v___x_6751_, 0);
                    v_isSharedCheck_6760_ = (!crate::leanh::lean_is_exclusive(v___x_6751_)) as u8;
                    if v_isSharedCheck_6760_ == 0 {
                        v___x_6754_ = v___x_6751_;
                        v_isShared_6755_ = v_isSharedCheck_6760_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_6752_);
                        crate::leanh::lean_dec(v___x_6751_);
                        v___x_6754_ = crate::leanh::lean_box(0);
                        v_isShared_6755_ = v_isSharedCheck_6760_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_6761_ = crate::leanh::lean_ctor_get(v___x_6751_, 0);
                    v_isSharedCheck_6768_ = (!crate::leanh::lean_is_exclusive(v___x_6751_)) as u8;
                    if v_isSharedCheck_6768_ == 0 {
                        v___x_6763_ = v___x_6751_;
                        v_isShared_6764_ = v_isSharedCheck_6768_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_6761_);
                        crate::leanh::lean_dec(v___x_6751_);
                        v___x_6763_ = crate::leanh::lean_box(0);
                        v_isShared_6764_ = v_isSharedCheck_6768_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v_fst_6756_ = crate::leanh::lean_ctor_get(v_a_6752_, 0);
                crate::leanh::lean_inc(v_fst_6756_);
                crate::leanh::lean_dec(v_a_6752_);
                if v_isShared_6755_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_6754_, 0, v_fst_6756_);
                    v___x_6758_ = v___x_6754_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_6759_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6759_, 0, v_fst_6756_);
                    v___x_6758_ = v_reuseFailAlloc_6759_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_6758_;
            }
            3 => {
                if v_isShared_6764_ == 0 {
                    v___x_6766_ = v___x_6763_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_6767_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6767_, 0, v_a_6761_);
                    v___x_6766_ = v_reuseFailAlloc_6767_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_6766_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___boxed(
    mut v_goal_6769_: *mut crate::leanh::LeanObject,
    mut v_generation_6770_: *mut crate::leanh::LeanObject,
    mut v_a_6771_: *mut crate::leanh::LeanObject,
    mut v_a_6772_: *mut crate::leanh::LeanObject,
    mut v_a_6773_: *mut crate::leanh::LeanObject,
    mut v_a_6774_: *mut crate::leanh::LeanObject,
    mut v_a_6775_: *mut crate::leanh::LeanObject,
    mut v_a_6776_: *mut crate::leanh::LeanObject,
    mut v_a_6777_: *mut crate::leanh::LeanObject,
    mut v_a_6778_: *mut crate::leanh::LeanObject,
    mut v_a_6779_: *mut crate::leanh::LeanObject,
    mut v_a_6780_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6781_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6781_ = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext(
        v_goal_6769_,
        v_generation_6770_,
        v_a_6771_,
        v_a_6772_,
        v_a_6773_,
        v_a_6774_,
        v_a_6775_,
        v_a_6776_,
        v_a_6777_,
        v_a_6778_,
        v_a_6779_,
    );
    crate::leanh::lean_dec(v_a_6779_);
    crate::leanh::lean_dec_ref(v_a_6778_);
    crate::leanh::lean_dec(v_a_6777_);
    crate::leanh::lean_dec_ref(v_a_6776_);
    crate::leanh::lean_dec(v_a_6775_);
    crate::leanh::lean_dec_ref(v_a_6774_);
    crate::leanh::lean_dec(v_a_6773_);
    crate::leanh::lean_dec_ref(v_a_6772_);
    crate::leanh::lean_dec(v_a_6771_);
    return v_res_6781_;
}
pub unsafe fn l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__1(
    mut v_mvarId_6782_: *mut crate::leanh::LeanObject,
    mut v_val_6783_: *mut crate::leanh::LeanObject,
    mut v___y_6784_: *mut crate::leanh::LeanObject,
    mut v___y_6785_: *mut crate::leanh::LeanObject,
    mut v___y_6786_: *mut crate::leanh::LeanObject,
    mut v___y_6787_: *mut crate::leanh::LeanObject,
    mut v___y_6788_: *mut crate::leanh::LeanObject,
    mut v___y_6789_: *mut crate::leanh::LeanObject,
    mut v___y_6790_: *mut crate::leanh::LeanObject,
    mut v___y_6791_: *mut crate::leanh::LeanObject,
    mut v___y_6792_: *mut crate::leanh::LeanObject,
    mut v___y_6793_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6795_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6795_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__1___redArg(v_mvarId_6782_, v_val_6783_, v___y_6791_);
    return v___x_6795_;
}
pub unsafe fn l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__1___boxed(
    mut v_mvarId_6796_: *mut crate::leanh::LeanObject,
    mut v_val_6797_: *mut crate::leanh::LeanObject,
    mut v___y_6798_: *mut crate::leanh::LeanObject,
    mut v___y_6799_: *mut crate::leanh::LeanObject,
    mut v___y_6800_: *mut crate::leanh::LeanObject,
    mut v___y_6801_: *mut crate::leanh::LeanObject,
    mut v___y_6802_: *mut crate::leanh::LeanObject,
    mut v___y_6803_: *mut crate::leanh::LeanObject,
    mut v___y_6804_: *mut crate::leanh::LeanObject,
    mut v___y_6805_: *mut crate::leanh::LeanObject,
    mut v___y_6806_: *mut crate::leanh::LeanObject,
    mut v___y_6807_: *mut crate::leanh::LeanObject,
    mut v___y_6808_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6809_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6809_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__1(v_mvarId_6796_, v_val_6797_, v___y_6798_, v___y_6799_, v___y_6800_, v___y_6801_, v___y_6802_, v___y_6803_, v___y_6804_, v___y_6805_, v___y_6806_, v___y_6807_);
    crate::leanh::lean_dec(v___y_6807_);
    crate::leanh::lean_dec_ref(v___y_6806_);
    crate::leanh::lean_dec(v___y_6805_);
    crate::leanh::lean_dec_ref(v___y_6804_);
    crate::leanh::lean_dec(v___y_6803_);
    crate::leanh::lean_dec_ref(v___y_6802_);
    crate::leanh::lean_dec(v___y_6801_);
    crate::leanh::lean_dec_ref(v___y_6800_);
    crate::leanh::lean_dec(v___y_6799_);
    crate::leanh::lean_dec(v___y_6798_);
    return v_res_6809_;
}
pub unsafe fn l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__2_spec__3(
    mut v___y_6810_: *mut crate::leanh::LeanObject,
    mut v___y_6811_: *mut crate::leanh::LeanObject,
    mut v___y_6812_: *mut crate::leanh::LeanObject,
    mut v___y_6813_: *mut crate::leanh::LeanObject,
    mut v___y_6814_: *mut crate::leanh::LeanObject,
    mut v___y_6815_: *mut crate::leanh::LeanObject,
    mut v___y_6816_: *mut crate::leanh::LeanObject,
    mut v___y_6817_: *mut crate::leanh::LeanObject,
    mut v___y_6818_: *mut crate::leanh::LeanObject,
    mut v___y_6819_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6821_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6821_ = l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__2_spec__3___redArg(v___y_6819_);
    return v___x_6821_;
}
pub unsafe fn l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__2_spec__3___boxed(
    mut v___y_6822_: *mut crate::leanh::LeanObject,
    mut v___y_6823_: *mut crate::leanh::LeanObject,
    mut v___y_6824_: *mut crate::leanh::LeanObject,
    mut v___y_6825_: *mut crate::leanh::LeanObject,
    mut v___y_6826_: *mut crate::leanh::LeanObject,
    mut v___y_6827_: *mut crate::leanh::LeanObject,
    mut v___y_6828_: *mut crate::leanh::LeanObject,
    mut v___y_6829_: *mut crate::leanh::LeanObject,
    mut v___y_6830_: *mut crate::leanh::LeanObject,
    mut v___y_6831_: *mut crate::leanh::LeanObject,
    mut v___y_6832_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6833_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6833_ = l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__2_spec__3(v___y_6822_, v___y_6823_, v___y_6824_, v___y_6825_, v___y_6826_, v___y_6827_, v___y_6828_, v___y_6829_, v___y_6830_, v___y_6831_);
    crate::leanh::lean_dec(v___y_6831_);
    crate::leanh::lean_dec_ref(v___y_6830_);
    crate::leanh::lean_dec(v___y_6829_);
    crate::leanh::lean_dec_ref(v___y_6828_);
    crate::leanh::lean_dec(v___y_6827_);
    crate::leanh::lean_dec_ref(v___y_6826_);
    crate::leanh::lean_dec(v___y_6825_);
    crate::leanh::lean_dec_ref(v___y_6824_);
    crate::leanh::lean_dec(v___y_6823_);
    crate::leanh::lean_dec(v___y_6822_);
    return v_res_6833_;
}
pub unsafe fn l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__1_spec__1(
    mut v_00_u03b2_6834_: *mut crate::leanh::LeanObject,
    mut v_x_6835_: *mut crate::leanh::LeanObject,
    mut v_x_6836_: *mut crate::leanh::LeanObject,
    mut v_x_6837_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6838_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6838_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__1_spec__1___redArg(v_x_6835_, v_x_6836_, v_x_6837_);
    return v___x_6838_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__1_spec__1_spec__3(
    mut v_00_u03b2_6839_: *mut crate::leanh::LeanObject,
    mut v_x_6840_: *mut crate::leanh::LeanObject,
    mut v_x_6841_: usize,
    mut v_x_6842_: usize,
    mut v_x_6843_: *mut crate::leanh::LeanObject,
    mut v_x_6844_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6845_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6845_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__1_spec__1_spec__3___redArg(v_x_6840_, v_x_6841_, v_x_6842_, v_x_6843_, v_x_6844_);
    return v___x_6845_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__1_spec__1_spec__3___boxed(
    mut v_00_u03b2_6846_: *mut crate::leanh::LeanObject,
    mut v_x_6847_: *mut crate::leanh::LeanObject,
    mut v_x_6848_: *mut crate::leanh::LeanObject,
    mut v_x_6849_: *mut crate::leanh::LeanObject,
    mut v_x_6850_: *mut crate::leanh::LeanObject,
    mut v_x_6851_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_197005__boxed_6852_: usize = 0;
    let mut v_x_197006__boxed_6853_: usize = 0;
    let mut v_res_6854_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_197005__boxed_6852_ = crate::leanh::lean_unbox_usize(v_x_6848_);
    crate::leanh::lean_dec(v_x_6848_);
    v_x_197006__boxed_6853_ = crate::leanh::lean_unbox_usize(v_x_6849_);
    crate::leanh::lean_dec(v_x_6849_);
    v_res_6854_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__1_spec__1_spec__3(v_00_u03b2_6846_, v_x_6847_, v_x_197005__boxed_6852_, v_x_197006__boxed_6853_, v_x_6850_, v_x_6851_);
    return v_res_6854_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__1_spec__1_spec__3_spec__6(
    mut v_00_u03b2_6855_: *mut crate::leanh::LeanObject,
    mut v_n_6856_: *mut crate::leanh::LeanObject,
    mut v_k_6857_: *mut crate::leanh::LeanObject,
    mut v_v_6858_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6859_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6859_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__1_spec__1_spec__3_spec__6___redArg(v_n_6856_, v_k_6857_, v_v_6858_);
    return v___x_6859_;
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__1_spec__1_spec__3_spec__7(
    mut v_00_u03b2_6860_: *mut crate::leanh::LeanObject,
    mut v_depth_6861_: usize,
    mut v_keys_6862_: *mut crate::leanh::LeanObject,
    mut v_vals_6863_: *mut crate::leanh::LeanObject,
    mut v_heq_6864_: *mut crate::leanh::LeanObject,
    mut v_i_6865_: *mut crate::leanh::LeanObject,
    mut v_entries_6866_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6867_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6867_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__1_spec__1_spec__3_spec__7___redArg(v_depth_6861_, v_keys_6862_, v_vals_6863_, v_i_6865_, v_entries_6866_);
    return v___x_6867_;
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__1_spec__1_spec__3_spec__7___boxed(
    mut v_00_u03b2_6868_: *mut crate::leanh::LeanObject,
    mut v_depth_6869_: *mut crate::leanh::LeanObject,
    mut v_keys_6870_: *mut crate::leanh::LeanObject,
    mut v_vals_6871_: *mut crate::leanh::LeanObject,
    mut v_heq_6872_: *mut crate::leanh::LeanObject,
    mut v_i_6873_: *mut crate::leanh::LeanObject,
    mut v_entries_6874_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_depth_boxed_6875_: usize = 0;
    let mut v_res_6876_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_depth_boxed_6875_ = crate::leanh::lean_unbox_usize(v_depth_6869_);
    crate::leanh::lean_dec(v_depth_6869_);
    v_res_6876_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__1_spec__1_spec__3_spec__7(v_00_u03b2_6868_, v_depth_boxed_6875_, v_keys_6870_, v_vals_6871_, v_heq_6872_, v_i_6873_, v_entries_6874_);
    crate::leanh::lean_dec_ref(v_vals_6871_);
    crate::leanh::lean_dec_ref(v_keys_6870_);
    return v_res_6876_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__1_spec__1_spec__3_spec__6_spec__7(
    mut v_00_u03b2_6877_: *mut crate::leanh::LeanObject,
    mut v_x_6878_: *mut crate::leanh::LeanObject,
    mut v_x_6879_: *mut crate::leanh::LeanObject,
    mut v_x_6880_: *mut crate::leanh::LeanObject,
    mut v_x_6881_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6882_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6882_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__1_spec__1_spec__3_spec__6_spec__7___redArg(v_x_6878_, v_x_6879_, v_x_6880_, v_x_6881_);
    return v___x_6882_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isEagerCasesCandidate___redArg(
    mut v_type_6883_: *mut crate::leanh::LeanObject,
    mut v_a_6884_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6886_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6886_ = l_Lean_Expr_getAppFn(v_type_6883_);
    if crate::leanh::lean_obj_tag(v___x_6886_) == 4 {
        let mut v_declName_6887_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_6888_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_declName_6887_ = crate::leanh::lean_ctor_get(v___x_6886_, 0);
        crate::leanh::lean_inc(v_declName_6887_);
        crate::leanh::lean_dec_ref_known(v___x_6886_, 2);
        v___x_6888_ = l_Lean_Meta_Grind_isEagerSplit___redArg(v_declName_6887_, v_a_6884_);
        crate::leanh::lean_dec(v_declName_6887_);
        return v___x_6888_;
    } else {
        let mut v___x_6889_: u8 = 0;
        let mut v___x_6890_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_6891_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec_ref(v___x_6886_);
        v___x_6889_ = 0;
        v___x_6890_ = crate::leanh::lean_box((v___x_6889_) as usize);
        v___x_6891_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_6891_, 0, v___x_6890_);
        return v___x_6891_;
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isEagerCasesCandidate___redArg___boxed(
    mut v_type_6892_: *mut crate::leanh::LeanObject,
    mut v_a_6893_: *mut crate::leanh::LeanObject,
    mut v_a_6894_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6895_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6895_ =
        l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isEagerCasesCandidate___redArg(
            v_type_6892_,
            v_a_6893_,
        );
    crate::leanh::lean_dec_ref(v_a_6893_);
    crate::leanh::lean_dec_ref(v_type_6892_);
    return v_res_6895_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isEagerCasesCandidate(
    mut v_type_6896_: *mut crate::leanh::LeanObject,
    mut v_a_6897_: *mut crate::leanh::LeanObject,
    mut v_a_6898_: *mut crate::leanh::LeanObject,
    mut v_a_6899_: *mut crate::leanh::LeanObject,
    mut v_a_6900_: *mut crate::leanh::LeanObject,
    mut v_a_6901_: *mut crate::leanh::LeanObject,
    mut v_a_6902_: *mut crate::leanh::LeanObject,
    mut v_a_6903_: *mut crate::leanh::LeanObject,
    mut v_a_6904_: *mut crate::leanh::LeanObject,
    mut v_a_6905_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6907_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6907_ =
        l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isEagerCasesCandidate___redArg(
            v_type_6896_,
            v_a_6898_,
        );
    return v___x_6907_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isEagerCasesCandidate___boxed(
    mut v_type_6908_: *mut crate::leanh::LeanObject,
    mut v_a_6909_: *mut crate::leanh::LeanObject,
    mut v_a_6910_: *mut crate::leanh::LeanObject,
    mut v_a_6911_: *mut crate::leanh::LeanObject,
    mut v_a_6912_: *mut crate::leanh::LeanObject,
    mut v_a_6913_: *mut crate::leanh::LeanObject,
    mut v_a_6914_: *mut crate::leanh::LeanObject,
    mut v_a_6915_: *mut crate::leanh::LeanObject,
    mut v_a_6916_: *mut crate::leanh::LeanObject,
    mut v_a_6917_: *mut crate::leanh::LeanObject,
    mut v_a_6918_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6919_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6919_ = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isEagerCasesCandidate(
        v_type_6908_,
        v_a_6909_,
        v_a_6910_,
        v_a_6911_,
        v_a_6912_,
        v_a_6913_,
        v_a_6914_,
        v_a_6915_,
        v_a_6916_,
        v_a_6917_,
    );
    crate::leanh::lean_dec(v_a_6917_);
    crate::leanh::lean_dec_ref(v_a_6916_);
    crate::leanh::lean_dec(v_a_6915_);
    crate::leanh::lean_dec_ref(v_a_6914_);
    crate::leanh::lean_dec(v_a_6913_);
    crate::leanh::lean_dec_ref(v_a_6912_);
    crate::leanh::lean_dec(v_a_6911_);
    crate::leanh::lean_dec_ref(v_a_6910_);
    crate::leanh::lean_dec(v_a_6909_);
    crate::leanh::lean_dec_ref(v_type_6908_);
    return v_res_6919_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_6920_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6920_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
    );
    return v___x_6920_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_6921_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6922_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6921_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__0_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__0);
    v___x_6922_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_6922_, 0, v___x_6921_);
    return v___x_6922_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__2()
-> *mut crate::leanh::LeanObject {
    let mut v___x_6923_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6924_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6925_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6923_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__1_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__1);
    v___x_6924_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_6925_ = crate::leanh::lean_alloc_ctor(0, 10, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_6925_, 0, v___x_6924_);
    crate::leanh::lean_ctor_set(v___x_6925_, 1, v___x_6924_);
    crate::leanh::lean_ctor_set(v___x_6925_, 2, v___x_6924_);
    crate::leanh::lean_ctor_set(v___x_6925_, 3, v___x_6924_);
    crate::leanh::lean_ctor_set(v___x_6925_, 4, v___x_6923_);
    crate::leanh::lean_ctor_set(v___x_6925_, 5, v___x_6923_);
    crate::leanh::lean_ctor_set(v___x_6925_, 6, v___x_6923_);
    crate::leanh::lean_ctor_set(v___x_6925_, 7, v___x_6923_);
    crate::leanh::lean_ctor_set(v___x_6925_, 8, v___x_6923_);
    crate::leanh::lean_ctor_set(v___x_6925_, 9, v___x_6923_);
    return v___x_6925_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_6926_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6927_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6928_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6926_ = crate::leanh::lean_unsigned_to_nat(32);
    v___x_6927_ = lean_mk_empty_array_with_capacity(v___x_6926_);
    v___x_6928_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_6928_, 0, v___x_6927_);
    return v___x_6928_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__4()
-> *mut crate::leanh::LeanObject {
    let mut v___x_6929_: usize = 0;
    let mut v___x_6930_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6931_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6932_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6933_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6934_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6929_ = 5usize;
    v___x_6930_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_6931_ = crate::leanh::lean_unsigned_to_nat(32);
    v___x_6932_ = lean_mk_empty_array_with_capacity(v___x_6931_);
    v___x_6933_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__3), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__3_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__3);
    v___x_6934_ = crate::leanh::lean_alloc_ctor(0, 4, (core::mem::size_of::<usize>() * 1) as u32);
    crate::leanh::lean_ctor_set(v___x_6934_, 0, v___x_6933_);
    crate::leanh::lean_ctor_set(v___x_6934_, 1, v___x_6932_);
    crate::leanh::lean_ctor_set(v___x_6934_, 2, v___x_6930_);
    crate::leanh::lean_ctor_set(v___x_6934_, 3, v___x_6930_);
    crate::leanh::lean_ctor_set_usize(v___x_6934_, 4, v___x_6929_);
    return v___x_6934_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__5()
-> *mut crate::leanh::LeanObject {
    let mut v___x_6935_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6936_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6937_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6938_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6935_ = crate::leanh::lean_box(1);
    v___x_6936_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__4), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__4_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__4);
    v___x_6937_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__1_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__1);
    v___x_6938_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_6938_, 0, v___x_6937_);
    crate::leanh::lean_ctor_set(v___x_6938_, 1, v___x_6936_);
    crate::leanh::lean_ctor_set(v___x_6938_, 2, v___x_6935_);
    return v___x_6938_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__7()
-> *mut crate::leanh::LeanObject {
    let mut v___x_6940_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6941_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6940_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__6;
    v___x_6941_ = l_Lean_stringToMessageData(v___x_6940_);
    return v___x_6941_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__9()
-> *mut crate::leanh::LeanObject {
    let mut v___x_6943_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6944_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6943_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__8;
    v___x_6944_ = l_Lean_stringToMessageData(v___x_6943_);
    return v___x_6944_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__11()
-> *mut crate::leanh::LeanObject {
    let mut v___x_6946_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6947_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6946_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__10;
    v___x_6947_ = l_Lean_stringToMessageData(v___x_6946_);
    return v___x_6947_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__13()
-> *mut crate::leanh::LeanObject {
    let mut v___x_6949_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6950_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6949_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__12;
    v___x_6950_ = l_Lean_stringToMessageData(v___x_6949_);
    return v___x_6950_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__15()
-> *mut crate::leanh::LeanObject {
    let mut v___x_6952_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6953_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6952_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__14;
    v___x_6953_ = l_Lean_stringToMessageData(v___x_6952_);
    return v___x_6953_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__17()
-> *mut crate::leanh::LeanObject {
    let mut v___x_6955_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6956_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6955_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__16;
    v___x_6956_ = l_Lean_stringToMessageData(v___x_6955_);
    return v___x_6956_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__19()
-> *mut crate::leanh::LeanObject {
    let mut v___x_6958_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6959_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6958_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__18;
    v___x_6959_ = l_Lean_stringToMessageData(v___x_6958_);
    return v___x_6959_;
}
pub unsafe fn l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg(
    mut v_msg_6960_: *mut crate::leanh::LeanObject,
    mut v_declHint_6961_: *mut crate::leanh::LeanObject,
    mut v___y_6962_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6964_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_6965_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6966_: u8 = 0;
    let mut v_isExporting_6967_: u8 = 0;
    let mut v___x_6968_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6969_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6970_: u8 = 0;
    let mut v___x_6971_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6972_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6973_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6974_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6975_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6976_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_c_6977_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6978_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6979_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6980_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6981_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6982_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6983_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6984_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6985_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_6986_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6988_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6989_: u8 = 0;
    let mut v___x_6990_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6991_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6992_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mod_6993_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6994_: u8 = 0;
    let mut v___x_6995_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6996_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6997_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6998_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6999_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7000_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7001_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7002_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7003_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7004_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7006_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7007_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7008_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7009_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7010_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7011_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7012_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7013_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7014_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7015_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7016_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7017_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7019_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7020_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7021_: u8 = 0;
    let mut v___x_7022_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_6964_ = lean_st_ref_get(v___y_6962_);
                v_env_6965_ = crate::leanh::lean_ctor_get(v___x_6964_, 0);
                crate::leanh::lean_inc_ref(v_env_6965_);
                crate::leanh::lean_dec(v___x_6964_);
                v___x_6966_ = l_Lean_Name_isAnonymous(v_declHint_6961_);
                if v___x_6966_ == 0 {
                    v_isExporting_6967_ = crate::leanh::lean_ctor_get_uint8(
                        v_env_6965_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 8) as u32,
                    );
                    if v_isExporting_6967_ == 0 {
                        crate::leanh::lean_dec_ref(v_env_6965_);
                        crate::leanh::lean_dec(v_declHint_6961_);
                        v___x_6968_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_6968_, 0, v_msg_6960_);
                        return v___x_6968_;
                    } else {
                        crate::leanh::lean_inc_ref(v_env_6965_);
                        v___x_6969_ = l_Lean_Environment_setExporting(v_env_6965_, v___x_6966_);
                        crate::leanh::lean_inc(v_declHint_6961_);
                        crate::leanh::lean_inc_ref(v___x_6969_);
                        v___x_6970_ = l_Lean_Environment_contains(
                            v___x_6969_,
                            v_declHint_6961_,
                            v_isExporting_6967_,
                        );
                        if v___x_6970_ == 0 {
                            crate::leanh::lean_dec_ref(v___x_6969_);
                            crate::leanh::lean_dec_ref(v_env_6965_);
                            crate::leanh::lean_dec(v_declHint_6961_);
                            v___x_6971_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_6971_, 0, v_msg_6960_);
                            return v___x_6971_;
                        } else {
                            v___x_6972_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__2), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__2_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__2);
                            v___x_6973_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__5), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__5_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__5);
                            v___x_6974_ = l_Lean_Options_empty;
                            v___x_6975_ = crate::leanh::lean_alloc_ctor(0, 4, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_6975_, 0, v___x_6969_);
                            crate::leanh::lean_ctor_set(v___x_6975_, 1, v___x_6972_);
                            crate::leanh::lean_ctor_set(v___x_6975_, 2, v___x_6973_);
                            crate::leanh::lean_ctor_set(v___x_6975_, 3, v___x_6974_);
                            crate::leanh::lean_inc(v_declHint_6961_);
                            v___x_6976_ =
                                l_Lean_MessageData_ofConstName(v_declHint_6961_, v___x_6966_);
                            v_c_6977_ = crate::leanh::lean_alloc_ctor(3, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v_c_6977_, 0, v___x_6975_);
                            crate::leanh::lean_ctor_set(v_c_6977_, 1, v___x_6976_);
                            v___x_6978_ = l_Lean_Environment_getModuleIdxFor_x3f(
                                v_env_6965_,
                                v_declHint_6961_,
                            );
                            if crate::leanh::lean_obj_tag(v___x_6978_) == 0 {
                                crate::leanh::lean_dec_ref(v_env_6965_);
                                crate::leanh::lean_dec(v_declHint_6961_);
                                v___x_6979_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__7), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__7_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__7);
                                v___x_6980_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                                crate::leanh::lean_ctor_set(v___x_6980_, 0, v___x_6979_);
                                crate::leanh::lean_ctor_set(v___x_6980_, 1, v_c_6977_);
                                v___x_6981_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__9), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__9_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__9);
                                v___x_6982_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                                crate::leanh::lean_ctor_set(v___x_6982_, 0, v___x_6980_);
                                crate::leanh::lean_ctor_set(v___x_6982_, 1, v___x_6981_);
                                v___x_6983_ = l_Lean_MessageData_note(v___x_6982_);
                                v___x_6984_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                                crate::leanh::lean_ctor_set(v___x_6984_, 0, v_msg_6960_);
                                crate::leanh::lean_ctor_set(v___x_6984_, 1, v___x_6983_);
                                v___x_6985_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                                crate::leanh::lean_ctor_set(v___x_6985_, 0, v___x_6984_);
                                return v___x_6985_;
                            } else {
                                v_val_6986_ = crate::leanh::lean_ctor_get(v___x_6978_, 0);
                                v_isSharedCheck_7021_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_6978_)) as u8;
                                if v_isSharedCheck_7021_ == 0 {
                                    v___x_6988_ = v___x_6978_;
                                    v_isShared_6989_ = v_isSharedCheck_7021_;
                                    state = 1;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_val_6986_);
                                    crate::leanh::lean_dec(v___x_6978_);
                                    v___x_6988_ = crate::leanh::lean_box(0);
                                    v_isShared_6989_ = v_isSharedCheck_7021_;
                                    state = 1;
                                    continue;
                                }
                            }
                        }
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_env_6965_);
                    crate::leanh::lean_dec(v_declHint_6961_);
                    v___x_7022_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_7022_, 0, v_msg_6960_);
                    return v___x_7022_;
                }
            }
            1 => {
                v___x_6990_ = crate::leanh::lean_box(0);
                v___x_6991_ = l_Lean_Environment_header(v_env_6965_);
                crate::leanh::lean_dec_ref(v_env_6965_);
                v___x_6992_ = l_Lean_EnvironmentHeader_moduleNames(v___x_6991_);
                v_mod_6993_ = lean_array_get(v___x_6990_, v___x_6992_, v_val_6986_);
                crate::leanh::lean_dec(v_val_6986_);
                crate::leanh::lean_dec_ref(v___x_6992_);
                v___x_6994_ = l_Lean_isPrivateName(v_declHint_6961_);
                crate::leanh::lean_dec(v_declHint_6961_);
                if v___x_6994_ == 0 {
                    v___x_6995_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__11), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__11_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__11);
                    v___x_6996_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_6996_, 0, v___x_6995_);
                    crate::leanh::lean_ctor_set(v___x_6996_, 1, v_c_6977_);
                    v___x_6997_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__13), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__13_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__13);
                    v___x_6998_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_6998_, 0, v___x_6996_);
                    crate::leanh::lean_ctor_set(v___x_6998_, 1, v___x_6997_);
                    v___x_6999_ = l_Lean_MessageData_ofName(v_mod_6993_);
                    v___x_7000_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_7000_, 0, v___x_6998_);
                    crate::leanh::lean_ctor_set(v___x_7000_, 1, v___x_6999_);
                    v___x_7001_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__15), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__15_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__15);
                    v___x_7002_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_7002_, 0, v___x_7000_);
                    crate::leanh::lean_ctor_set(v___x_7002_, 1, v___x_7001_);
                    v___x_7003_ = l_Lean_MessageData_note(v___x_7002_);
                    v___x_7004_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_7004_, 0, v_msg_6960_);
                    crate::leanh::lean_ctor_set(v___x_7004_, 1, v___x_7003_);
                    if v_isShared_6989_ == 0 {
                        crate::leanh::lean_ctor_set_tag(v___x_6988_, 0);
                        crate::leanh::lean_ctor_set(v___x_6988_, 0, v___x_7004_);
                        v___x_7006_ = v___x_6988_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_7007_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_7007_, 0, v___x_7004_);
                        v___x_7006_ = v_reuseFailAlloc_7007_;
                        state = 2;
                        continue;
                    }
                } else {
                    v___x_7008_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__7), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__7_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__7);
                    v___x_7009_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_7009_, 0, v___x_7008_);
                    crate::leanh::lean_ctor_set(v___x_7009_, 1, v_c_6977_);
                    v___x_7010_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__17), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__17_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__17);
                    v___x_7011_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_7011_, 0, v___x_7009_);
                    crate::leanh::lean_ctor_set(v___x_7011_, 1, v___x_7010_);
                    v___x_7012_ = l_Lean_MessageData_ofName(v_mod_6993_);
                    v___x_7013_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_7013_, 0, v___x_7011_);
                    crate::leanh::lean_ctor_set(v___x_7013_, 1, v___x_7012_);
                    v___x_7014_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__19), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__19_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__19);
                    v___x_7015_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_7015_, 0, v___x_7013_);
                    crate::leanh::lean_ctor_set(v___x_7015_, 1, v___x_7014_);
                    v___x_7016_ = l_Lean_MessageData_note(v___x_7015_);
                    v___x_7017_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_7017_, 0, v_msg_6960_);
                    crate::leanh::lean_ctor_set(v___x_7017_, 1, v___x_7016_);
                    if v_isShared_6989_ == 0 {
                        crate::leanh::lean_ctor_set_tag(v___x_6988_, 0);
                        crate::leanh::lean_ctor_set(v___x_6988_, 0, v___x_7017_);
                        v___x_7019_ = v___x_6988_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_7020_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_7020_, 0, v___x_7017_);
                        v___x_7019_ = v_reuseFailAlloc_7020_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_7006_;
            }
            3 => {
                return v___x_7019_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___boxed(
    mut v_msg_7023_: *mut crate::leanh::LeanObject,
    mut v_declHint_7024_: *mut crate::leanh::LeanObject,
    mut v___y_7025_: *mut crate::leanh::LeanObject,
    mut v___y_7026_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_7027_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_7027_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg(v_msg_7023_, v_declHint_7024_, v___y_7025_);
    crate::leanh::lean_dec(v___y_7025_);
    return v_res_7027_;
}
pub unsafe fn l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3(
    mut v_msg_7028_: *mut crate::leanh::LeanObject,
    mut v_declHint_7029_: *mut crate::leanh::LeanObject,
    mut v___y_7030_: *mut crate::leanh::LeanObject,
    mut v___y_7031_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_7033_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_7034_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7036_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7037_: u8 = 0;
    let mut v___x_7038_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7039_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7041_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7042_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7043_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_7033_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg(v_msg_7028_, v_declHint_7029_, v___y_7031_);
                v_a_7034_ = crate::leanh::lean_ctor_get(v___x_7033_, 0);
                v_isSharedCheck_7043_ = (!crate::leanh::lean_is_exclusive(v___x_7033_)) as u8;
                if v_isSharedCheck_7043_ == 0 {
                    v___x_7036_ = v___x_7033_;
                    v_isShared_7037_ = v_isSharedCheck_7043_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_a_7034_);
                    crate::leanh::lean_dec(v___x_7033_);
                    v___x_7036_ = crate::leanh::lean_box(0);
                    v_isShared_7037_ = v_isSharedCheck_7043_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_7038_ = l_Lean_unknownIdentifierMessageTag;
                v___x_7039_ = crate::leanh::lean_alloc_ctor(8, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_7039_, 0, v___x_7038_);
                crate::leanh::lean_ctor_set(v___x_7039_, 1, v_a_7034_);
                if v_isShared_7037_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_7036_, 0, v___x_7039_);
                    v___x_7041_ = v___x_7036_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_7042_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7042_, 0, v___x_7039_);
                    v___x_7041_ = v_reuseFailAlloc_7042_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_7041_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3___boxed(
    mut v_msg_7044_: *mut crate::leanh::LeanObject,
    mut v_declHint_7045_: *mut crate::leanh::LeanObject,
    mut v___y_7046_: *mut crate::leanh::LeanObject,
    mut v___y_7047_: *mut crate::leanh::LeanObject,
    mut v___y_7048_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_7049_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_7049_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3(v_msg_7044_, v_declHint_7045_, v___y_7046_, v___y_7047_);
    crate::leanh::lean_dec(v___y_7047_);
    crate::leanh::lean_dec_ref(v___y_7046_);
    return v_res_7049_;
}
pub unsafe fn l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6_spec__7(
    mut v_msgData_7050_: *mut crate::leanh::LeanObject,
    mut v___y_7051_: *mut crate::leanh::LeanObject,
    mut v___y_7052_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_7054_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_7055_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_7056_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7057_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7058_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7059_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7060_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7061_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7062_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7063_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_7054_ = lean_st_ref_get(v___y_7052_);
    v_env_7055_ = crate::leanh::lean_ctor_get(v___x_7054_, 0);
    crate::leanh::lean_inc_ref(v_env_7055_);
    crate::leanh::lean_dec(v___x_7054_);
    v_options_7056_ = crate::leanh::lean_ctor_get(v___y_7051_, 2);
    v___x_7057_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__2), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__2_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__2);
    v___x_7058_ = crate::leanh::lean_unsigned_to_nat(32);
    v___x_7059_ = lean_mk_empty_array_with_capacity(v___x_7058_);
    crate::leanh::lean_dec_ref(v___x_7059_);
    v___x_7060_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__5), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__5_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__5);
    crate::leanh::lean_inc_ref(v_options_7056_);
    v___x_7061_ = crate::leanh::lean_alloc_ctor(0, 4, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_7061_, 0, v_env_7055_);
    crate::leanh::lean_ctor_set(v___x_7061_, 1, v___x_7057_);
    crate::leanh::lean_ctor_set(v___x_7061_, 2, v___x_7060_);
    crate::leanh::lean_ctor_set(v___x_7061_, 3, v_options_7056_);
    v___x_7062_ = crate::leanh::lean_alloc_ctor(3, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_7062_, 0, v___x_7061_);
    crate::leanh::lean_ctor_set(v___x_7062_, 1, v_msgData_7050_);
    v___x_7063_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_7063_, 0, v___x_7062_);
    return v___x_7063_;
}
pub unsafe fn l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6_spec__7___boxed(
    mut v_msgData_7064_: *mut crate::leanh::LeanObject,
    mut v___y_7065_: *mut crate::leanh::LeanObject,
    mut v___y_7066_: *mut crate::leanh::LeanObject,
    mut v___y_7067_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_7068_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_7068_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6_spec__7(v_msgData_7064_, v___y_7065_, v___y_7066_);
    crate::leanh::lean_dec(v___y_7066_);
    crate::leanh::lean_dec_ref(v___y_7065_);
    return v_res_7068_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6___redArg(
    mut v_msg_7069_: *mut crate::leanh::LeanObject,
    mut v___y_7070_: *mut crate::leanh::LeanObject,
    mut v___y_7071_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_ref_7073_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7074_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_7075_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7077_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7078_: u8 = 0;
    let mut v___x_7079_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7081_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7082_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7083_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ref_7073_ = crate::leanh::lean_ctor_get(v___y_7070_, 5);
                v___x_7074_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6_spec__7(v_msg_7069_, v___y_7070_, v___y_7071_);
                v_a_7075_ = crate::leanh::lean_ctor_get(v___x_7074_, 0);
                v_isSharedCheck_7083_ = (!crate::leanh::lean_is_exclusive(v___x_7074_)) as u8;
                if v_isSharedCheck_7083_ == 0 {
                    v___x_7077_ = v___x_7074_;
                    v_isShared_7078_ = v_isSharedCheck_7083_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_a_7075_);
                    crate::leanh::lean_dec(v___x_7074_);
                    v___x_7077_ = crate::leanh::lean_box(0);
                    v_isShared_7078_ = v_isSharedCheck_7083_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                crate::leanh::lean_inc(v_ref_7073_);
                v___x_7079_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_7079_, 0, v_ref_7073_);
                crate::leanh::lean_ctor_set(v___x_7079_, 1, v_a_7075_);
                if v_isShared_7078_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_7077_, 1);
                    crate::leanh::lean_ctor_set(v___x_7077_, 0, v___x_7079_);
                    v___x_7081_ = v___x_7077_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_7082_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7082_, 0, v___x_7079_);
                    v___x_7081_ = v_reuseFailAlloc_7082_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_7081_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6___redArg___boxed(
    mut v_msg_7084_: *mut crate::leanh::LeanObject,
    mut v___y_7085_: *mut crate::leanh::LeanObject,
    mut v___y_7086_: *mut crate::leanh::LeanObject,
    mut v___y_7087_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_7088_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_7088_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6___redArg(v_msg_7084_, v___y_7085_, v___y_7086_);
    crate::leanh::lean_dec(v___y_7086_);
    crate::leanh::lean_dec_ref(v___y_7085_);
    return v_res_7088_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__4___redArg(
    mut v_ref_7089_: *mut crate::leanh::LeanObject,
    mut v_msg_7090_: *mut crate::leanh::LeanObject,
    mut v___y_7091_: *mut crate::leanh::LeanObject,
    mut v___y_7092_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_fileName_7094_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fileMap_7095_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_7096_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_currRecDepth_7097_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_maxRecDepth_7098_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_7099_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_currNamespace_7100_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_openDecls_7101_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_initHeartbeats_7102_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_maxHeartbeats_7103_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_quotContext_7104_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_currMacroScope_7105_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_diag_7106_: u8 = 0;
    let mut v_cancelTk_x3f_7107_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_suppressElabErrors_7108_: u8 = 0;
    let mut v_inheritedTraceOptions_7109_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_7110_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7111_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7112_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_fileName_7094_ = crate::leanh::lean_ctor_get(v___y_7091_, 0);
    v_fileMap_7095_ = crate::leanh::lean_ctor_get(v___y_7091_, 1);
    v_options_7096_ = crate::leanh::lean_ctor_get(v___y_7091_, 2);
    v_currRecDepth_7097_ = crate::leanh::lean_ctor_get(v___y_7091_, 3);
    v_maxRecDepth_7098_ = crate::leanh::lean_ctor_get(v___y_7091_, 4);
    v_ref_7099_ = crate::leanh::lean_ctor_get(v___y_7091_, 5);
    v_currNamespace_7100_ = crate::leanh::lean_ctor_get(v___y_7091_, 6);
    v_openDecls_7101_ = crate::leanh::lean_ctor_get(v___y_7091_, 7);
    v_initHeartbeats_7102_ = crate::leanh::lean_ctor_get(v___y_7091_, 8);
    v_maxHeartbeats_7103_ = crate::leanh::lean_ctor_get(v___y_7091_, 9);
    v_quotContext_7104_ = crate::leanh::lean_ctor_get(v___y_7091_, 10);
    v_currMacroScope_7105_ = crate::leanh::lean_ctor_get(v___y_7091_, 11);
    v_diag_7106_ = crate::leanh::lean_ctor_get_uint8(
        v___y_7091_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 14) as u32,
    );
    v_cancelTk_x3f_7107_ = crate::leanh::lean_ctor_get(v___y_7091_, 12);
    v_suppressElabErrors_7108_ = crate::leanh::lean_ctor_get_uint8(
        v___y_7091_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 14 + 1) as u32,
    );
    v_inheritedTraceOptions_7109_ = crate::leanh::lean_ctor_get(v___y_7091_, 13);
    v_ref_7110_ = l_Lean_replaceRef(v_ref_7089_, v_ref_7099_);
    crate::leanh::lean_inc_ref(v_inheritedTraceOptions_7109_);
    crate::leanh::lean_inc(v_cancelTk_x3f_7107_);
    crate::leanh::lean_inc(v_currMacroScope_7105_);
    crate::leanh::lean_inc(v_quotContext_7104_);
    crate::leanh::lean_inc(v_maxHeartbeats_7103_);
    crate::leanh::lean_inc(v_initHeartbeats_7102_);
    crate::leanh::lean_inc(v_openDecls_7101_);
    crate::leanh::lean_inc(v_currNamespace_7100_);
    crate::leanh::lean_inc(v_maxRecDepth_7098_);
    crate::leanh::lean_inc(v_currRecDepth_7097_);
    crate::leanh::lean_inc_ref(v_options_7096_);
    crate::leanh::lean_inc_ref(v_fileMap_7095_);
    crate::leanh::lean_inc_ref(v_fileName_7094_);
    v___x_7111_ = crate::leanh::lean_alloc_ctor(0, 14, (2) as u32);
    crate::leanh::lean_ctor_set(v___x_7111_, 0, v_fileName_7094_);
    crate::leanh::lean_ctor_set(v___x_7111_, 1, v_fileMap_7095_);
    crate::leanh::lean_ctor_set(v___x_7111_, 2, v_options_7096_);
    crate::leanh::lean_ctor_set(v___x_7111_, 3, v_currRecDepth_7097_);
    crate::leanh::lean_ctor_set(v___x_7111_, 4, v_maxRecDepth_7098_);
    crate::leanh::lean_ctor_set(v___x_7111_, 5, v_ref_7110_);
    crate::leanh::lean_ctor_set(v___x_7111_, 6, v_currNamespace_7100_);
    crate::leanh::lean_ctor_set(v___x_7111_, 7, v_openDecls_7101_);
    crate::leanh::lean_ctor_set(v___x_7111_, 8, v_initHeartbeats_7102_);
    crate::leanh::lean_ctor_set(v___x_7111_, 9, v_maxHeartbeats_7103_);
    crate::leanh::lean_ctor_set(v___x_7111_, 10, v_quotContext_7104_);
    crate::leanh::lean_ctor_set(v___x_7111_, 11, v_currMacroScope_7105_);
    crate::leanh::lean_ctor_set(v___x_7111_, 12, v_cancelTk_x3f_7107_);
    crate::leanh::lean_ctor_set(v___x_7111_, 13, v_inheritedTraceOptions_7109_);
    crate::leanh::lean_ctor_set_uint8(
        v___x_7111_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 14) as u32,
        v_diag_7106_,
    );
    crate::leanh::lean_ctor_set_uint8(
        v___x_7111_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 14 + 1) as u32,
        v_suppressElabErrors_7108_,
    );
    v___x_7112_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6___redArg(v_msg_7090_, v___x_7111_, v___y_7092_);
    crate::leanh::lean_dec_ref_known(v___x_7111_, 14);
    return v___x_7112_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__4___redArg___boxed(
    mut v_ref_7113_: *mut crate::leanh::LeanObject,
    mut v_msg_7114_: *mut crate::leanh::LeanObject,
    mut v___y_7115_: *mut crate::leanh::LeanObject,
    mut v___y_7116_: *mut crate::leanh::LeanObject,
    mut v___y_7117_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_7118_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_7118_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__4___redArg(v_ref_7113_, v_msg_7114_, v___y_7115_, v___y_7116_);
    crate::leanh::lean_dec(v___y_7116_);
    crate::leanh::lean_dec_ref(v___y_7115_);
    crate::leanh::lean_dec(v_ref_7113_);
    return v_res_7118_;
}
pub unsafe fn l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2___redArg(
    mut v_ref_7119_: *mut crate::leanh::LeanObject,
    mut v_msg_7120_: *mut crate::leanh::LeanObject,
    mut v_declHint_7121_: *mut crate::leanh::LeanObject,
    mut v___y_7122_: *mut crate::leanh::LeanObject,
    mut v___y_7123_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_7125_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_7126_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7127_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_7125_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3(v_msg_7120_, v_declHint_7121_, v___y_7122_, v___y_7123_);
    v_a_7126_ = crate::leanh::lean_ctor_get(v___x_7125_, 0);
    crate::leanh::lean_inc(v_a_7126_);
    crate::leanh::lean_dec_ref(v___x_7125_);
    v___x_7127_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__4___redArg(v_ref_7119_, v_a_7126_, v___y_7122_, v___y_7123_);
    return v___x_7127_;
}
pub unsafe fn l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2___redArg___boxed(
    mut v_ref_7128_: *mut crate::leanh::LeanObject,
    mut v_msg_7129_: *mut crate::leanh::LeanObject,
    mut v_declHint_7130_: *mut crate::leanh::LeanObject,
    mut v___y_7131_: *mut crate::leanh::LeanObject,
    mut v___y_7132_: *mut crate::leanh::LeanObject,
    mut v___y_7133_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_7134_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_7134_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2___redArg(v_ref_7128_, v_msg_7129_, v_declHint_7130_, v___y_7131_, v___y_7132_);
    crate::leanh::lean_dec(v___y_7132_);
    crate::leanh::lean_dec_ref(v___y_7131_);
    crate::leanh::lean_dec(v_ref_7128_);
    return v_res_7134_;
}
pub unsafe fn _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1___redArg___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_7136_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7137_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_7136_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1___redArg___closed__0;
    v___x_7137_ = l_Lean_stringToMessageData(v___x_7136_);
    return v___x_7137_;
}
pub unsafe fn _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1___redArg___closed__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_7139_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7140_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_7139_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1___redArg___closed__2;
    v___x_7140_ = l_Lean_stringToMessageData(v___x_7139_);
    return v___x_7140_;
}
pub unsafe fn l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1___redArg(
    mut v_ref_7141_: *mut crate::leanh::LeanObject,
    mut v_constName_7142_: *mut crate::leanh::LeanObject,
    mut v___y_7143_: *mut crate::leanh::LeanObject,
    mut v___y_7144_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_7146_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7147_: u8 = 0;
    let mut v___x_7148_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7149_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7150_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7151_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7152_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_7146_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1___redArg___closed__1_once), _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1___redArg___closed__1);
    v___x_7147_ = 0;
    crate::leanh::lean_inc(v_constName_7142_);
    v___x_7148_ = l_Lean_MessageData_ofConstName(v_constName_7142_, v___x_7147_);
    v___x_7149_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_7149_, 0, v___x_7146_);
    crate::leanh::lean_ctor_set(v___x_7149_, 1, v___x_7148_);
    v___x_7150_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1___redArg___closed__3), core::ptr::addr_of_mut!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1___redArg___closed__3_once), _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1___redArg___closed__3);
    v___x_7151_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_7151_, 0, v___x_7149_);
    crate::leanh::lean_ctor_set(v___x_7151_, 1, v___x_7150_);
    v___x_7152_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2___redArg(v_ref_7141_, v___x_7151_, v_constName_7142_, v___y_7143_, v___y_7144_);
    return v___x_7152_;
}
pub unsafe fn l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1___redArg___boxed(
    mut v_ref_7153_: *mut crate::leanh::LeanObject,
    mut v_constName_7154_: *mut crate::leanh::LeanObject,
    mut v___y_7155_: *mut crate::leanh::LeanObject,
    mut v___y_7156_: *mut crate::leanh::LeanObject,
    mut v___y_7157_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_7158_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_7158_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1___redArg(v_ref_7153_, v_constName_7154_, v___y_7155_, v___y_7156_);
    crate::leanh::lean_dec(v___y_7156_);
    crate::leanh::lean_dec_ref(v___y_7155_);
    crate::leanh::lean_dec(v_ref_7153_);
    return v_res_7158_;
}
pub unsafe fn l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0___redArg(
    mut v_constName_7159_: *mut crate::leanh::LeanObject,
    mut v___y_7160_: *mut crate::leanh::LeanObject,
    mut v___y_7161_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_ref_7163_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7164_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_ref_7163_ = crate::leanh::lean_ctor_get(v___y_7160_, 5);
    v___x_7164_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1___redArg(v_ref_7163_, v_constName_7159_, v___y_7160_, v___y_7161_);
    return v___x_7164_;
}
pub unsafe fn l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0___redArg___boxed(
    mut v_constName_7165_: *mut crate::leanh::LeanObject,
    mut v___y_7166_: *mut crate::leanh::LeanObject,
    mut v___y_7167_: *mut crate::leanh::LeanObject,
    mut v___y_7168_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_7169_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_7169_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0___redArg(v_constName_7165_, v___y_7166_, v___y_7167_);
    crate::leanh::lean_dec(v___y_7167_);
    crate::leanh::lean_dec_ref(v___y_7166_);
    return v_res_7169_;
}
pub unsafe fn l_Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0(
    mut v_constName_7170_: *mut crate::leanh::LeanObject,
    mut v___y_7171_: *mut crate::leanh::LeanObject,
    mut v___y_7172_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_7174_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_7175_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7176_: u8 = 0;
    let mut v___x_7177_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7178_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_7179_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7181_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7182_: u8 = 0;
    let mut v___x_7184_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7185_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7186_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_7174_ = lean_st_ref_get(v___y_7172_);
                v_env_7175_ = crate::leanh::lean_ctor_get(v___x_7174_, 0);
                crate::leanh::lean_inc_ref(v_env_7175_);
                crate::leanh::lean_dec(v___x_7174_);
                v___x_7176_ = 0;
                crate::leanh::lean_inc(v_constName_7170_);
                v___x_7177_ =
                    l_Lean_Environment_find_x3f(v_env_7175_, v_constName_7170_, v___x_7176_);
                if crate::leanh::lean_obj_tag(v___x_7177_) == 0 {
                    v___x_7178_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0___redArg(v_constName_7170_, v___y_7171_, v___y_7172_);
                    return v___x_7178_;
                } else {
                    crate::leanh::lean_dec(v_constName_7170_);
                    v_val_7179_ = crate::leanh::lean_ctor_get(v___x_7177_, 0);
                    v_isSharedCheck_7186_ = (!crate::leanh::lean_is_exclusive(v___x_7177_)) as u8;
                    if v_isSharedCheck_7186_ == 0 {
                        v___x_7181_ = v___x_7177_;
                        v_isShared_7182_ = v_isSharedCheck_7186_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_val_7179_);
                        crate::leanh::lean_dec(v___x_7177_);
                        v___x_7181_ = crate::leanh::lean_box(0);
                        v_isShared_7182_ = v_isSharedCheck_7186_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_7182_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_7181_, 0);
                    v___x_7184_ = v___x_7181_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_7185_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7185_, 0, v_val_7179_);
                    v___x_7184_ = v_reuseFailAlloc_7185_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_7184_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0___boxed(
    mut v_constName_7187_: *mut crate::leanh::LeanObject,
    mut v___y_7188_: *mut crate::leanh::LeanObject,
    mut v___y_7189_: *mut crate::leanh::LeanObject,
    mut v___y_7190_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_7191_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_7191_ = l_Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0(v_constName_7187_, v___y_7188_, v___y_7189_);
    crate::leanh::lean_dec(v___y_7189_);
    crate::leanh::lean_dec_ref(v___y_7188_);
    return v_res_7191_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive(
    mut v_type_7192_: *mut crate::leanh::LeanObject,
    mut v_a_7193_: *mut crate::leanh::LeanObject,
    mut v_a_7194_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_7196_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_declName_7197_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7198_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_7199_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7201_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7202_: u8 = 0;
    let mut v_val_7203_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7204_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7205_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7206_: u8 = 0;
    let mut v___x_7207_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7209_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7210_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7211_: u8 = 0;
    let mut v___x_7212_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7214_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7215_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7216_: u8 = 0;
    let mut v_a_7217_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7219_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7220_: u8 = 0;
    let mut v___x_7222_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7223_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7224_: u8 = 0;
    let mut v___x_7225_: u8 = 0;
    let mut v___x_7226_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7227_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_7196_ = l_Lean_Expr_getAppFn(v_type_7192_);
                if crate::leanh::lean_obj_tag(v___x_7196_) == 4 {
                    v_declName_7197_ = crate::leanh::lean_ctor_get(v___x_7196_, 0);
                    crate::leanh::lean_inc(v_declName_7197_);
                    crate::leanh::lean_dec_ref_known(v___x_7196_, 2);
                    v___x_7198_ = l_Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0(v_declName_7197_, v_a_7193_, v_a_7194_);
                    if crate::leanh::lean_obj_tag(v___x_7198_) == 0 {
                        v_a_7199_ = crate::leanh::lean_ctor_get(v___x_7198_, 0);
                        v_isSharedCheck_7216_ =
                            (!crate::leanh::lean_is_exclusive(v___x_7198_)) as u8;
                        if v_isSharedCheck_7216_ == 0 {
                            v___x_7201_ = v___x_7198_;
                            v_isShared_7202_ = v_isSharedCheck_7216_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_7199_);
                            crate::leanh::lean_dec(v___x_7198_);
                            v___x_7201_ = crate::leanh::lean_box(0);
                            v_isShared_7202_ = v_isSharedCheck_7216_;
                            state = 1;
                            continue;
                        }
                    } else {
                        v_a_7217_ = crate::leanh::lean_ctor_get(v___x_7198_, 0);
                        v_isSharedCheck_7224_ =
                            (!crate::leanh::lean_is_exclusive(v___x_7198_)) as u8;
                        if v_isSharedCheck_7224_ == 0 {
                            v___x_7219_ = v___x_7198_;
                            v_isShared_7220_ = v_isSharedCheck_7224_;
                            state = 4;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_7217_);
                            crate::leanh::lean_dec(v___x_7198_);
                            v___x_7219_ = crate::leanh::lean_box(0);
                            v_isShared_7220_ = v_isSharedCheck_7224_;
                            state = 4;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec_ref(v___x_7196_);
                    v___x_7225_ = 0;
                    v___x_7226_ = crate::leanh::lean_box((v___x_7225_) as usize);
                    v___x_7227_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_7227_, 0, v___x_7226_);
                    return v___x_7227_;
                }
            }
            1 => {
                if crate::leanh::lean_obj_tag(v_a_7199_) == 5 {
                    v_val_7203_ = crate::leanh::lean_ctor_get(v_a_7199_, 0);
                    crate::leanh::lean_inc_ref(v_val_7203_);
                    crate::leanh::lean_dec_ref_known(v_a_7199_, 1);
                    v___x_7204_ = l_Lean_InductiveVal_numCtors(v_val_7203_);
                    crate::leanh::lean_dec_ref(v_val_7203_);
                    v___x_7205_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_7206_ = lean_nat_dec_le(v___x_7204_, v___x_7205_);
                    crate::leanh::lean_dec(v___x_7204_);
                    v___x_7207_ = crate::leanh::lean_box((v___x_7206_) as usize);
                    if v_isShared_7202_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_7201_, 0, v___x_7207_);
                        v___x_7209_ = v___x_7201_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_7210_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_7210_, 0, v___x_7207_);
                        v___x_7209_ = v_reuseFailAlloc_7210_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_a_7199_);
                    v___x_7211_ = 0;
                    v___x_7212_ = crate::leanh::lean_box((v___x_7211_) as usize);
                    if v_isShared_7202_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_7201_, 0, v___x_7212_);
                        v___x_7214_ = v___x_7201_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_7215_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_7215_, 0, v___x_7212_);
                        v___x_7214_ = v_reuseFailAlloc_7215_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_7209_;
            }
            3 => {
                return v___x_7214_;
            }
            4 => {
                if v_isShared_7220_ == 0 {
                    v___x_7222_ = v___x_7219_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_7223_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7223_, 0, v_a_7217_);
                    v___x_7222_ = v_reuseFailAlloc_7223_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_7222_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive___boxed(
    mut v_type_7228_: *mut crate::leanh::LeanObject,
    mut v_a_7229_: *mut crate::leanh::LeanObject,
    mut v_a_7230_: *mut crate::leanh::LeanObject,
    mut v_a_7231_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_7232_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_7232_ = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive(
        v_type_7228_,
        v_a_7229_,
        v_a_7230_,
    );
    crate::leanh::lean_dec(v_a_7230_);
    crate::leanh::lean_dec_ref(v_a_7229_);
    crate::leanh::lean_dec_ref(v_type_7228_);
    return v_res_7232_;
}
pub unsafe fn l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0(
    mut v_00_u03b1_7233_: *mut crate::leanh::LeanObject,
    mut v_constName_7234_: *mut crate::leanh::LeanObject,
    mut v___y_7235_: *mut crate::leanh::LeanObject,
    mut v___y_7236_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_7238_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_7238_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0___redArg(v_constName_7234_, v___y_7235_, v___y_7236_);
    return v___x_7238_;
}
pub unsafe fn l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0___boxed(
    mut v_00_u03b1_7239_: *mut crate::leanh::LeanObject,
    mut v_constName_7240_: *mut crate::leanh::LeanObject,
    mut v___y_7241_: *mut crate::leanh::LeanObject,
    mut v___y_7242_: *mut crate::leanh::LeanObject,
    mut v___y_7243_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_7244_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_7244_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0(v_00_u03b1_7239_, v_constName_7240_, v___y_7241_, v___y_7242_);
    crate::leanh::lean_dec(v___y_7242_);
    crate::leanh::lean_dec_ref(v___y_7241_);
    return v_res_7244_;
}
pub unsafe fn l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1(
    mut v_00_u03b1_7245_: *mut crate::leanh::LeanObject,
    mut v_ref_7246_: *mut crate::leanh::LeanObject,
    mut v_constName_7247_: *mut crate::leanh::LeanObject,
    mut v___y_7248_: *mut crate::leanh::LeanObject,
    mut v___y_7249_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_7251_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_7251_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1___redArg(v_ref_7246_, v_constName_7247_, v___y_7248_, v___y_7249_);
    return v___x_7251_;
}
pub unsafe fn l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1___boxed(
    mut v_00_u03b1_7252_: *mut crate::leanh::LeanObject,
    mut v_ref_7253_: *mut crate::leanh::LeanObject,
    mut v_constName_7254_: *mut crate::leanh::LeanObject,
    mut v___y_7255_: *mut crate::leanh::LeanObject,
    mut v___y_7256_: *mut crate::leanh::LeanObject,
    mut v___y_7257_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_7258_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_7258_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1(v_00_u03b1_7252_, v_ref_7253_, v_constName_7254_, v___y_7255_, v___y_7256_);
    crate::leanh::lean_dec(v___y_7256_);
    crate::leanh::lean_dec_ref(v___y_7255_);
    crate::leanh::lean_dec(v_ref_7253_);
    return v_res_7258_;
}
pub unsafe fn l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2(
    mut v_00_u03b1_7259_: *mut crate::leanh::LeanObject,
    mut v_ref_7260_: *mut crate::leanh::LeanObject,
    mut v_msg_7261_: *mut crate::leanh::LeanObject,
    mut v_declHint_7262_: *mut crate::leanh::LeanObject,
    mut v___y_7263_: *mut crate::leanh::LeanObject,
    mut v___y_7264_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_7266_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_7266_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2___redArg(v_ref_7260_, v_msg_7261_, v_declHint_7262_, v___y_7263_, v___y_7264_);
    return v___x_7266_;
}
pub unsafe fn l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2___boxed(
    mut v_00_u03b1_7267_: *mut crate::leanh::LeanObject,
    mut v_ref_7268_: *mut crate::leanh::LeanObject,
    mut v_msg_7269_: *mut crate::leanh::LeanObject,
    mut v_declHint_7270_: *mut crate::leanh::LeanObject,
    mut v___y_7271_: *mut crate::leanh::LeanObject,
    mut v___y_7272_: *mut crate::leanh::LeanObject,
    mut v___y_7273_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_7274_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_7274_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2(v_00_u03b1_7267_, v_ref_7268_, v_msg_7269_, v_declHint_7270_, v___y_7271_, v___y_7272_);
    crate::leanh::lean_dec(v___y_7272_);
    crate::leanh::lean_dec_ref(v___y_7271_);
    crate::leanh::lean_dec(v_ref_7268_);
    return v_res_7274_;
}
pub unsafe fn l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4(
    mut v_msg_7275_: *mut crate::leanh::LeanObject,
    mut v_declHint_7276_: *mut crate::leanh::LeanObject,
    mut v___y_7277_: *mut crate::leanh::LeanObject,
    mut v___y_7278_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_7280_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_7280_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg(v_msg_7275_, v_declHint_7276_, v___y_7278_);
    return v___x_7280_;
}
pub unsafe fn l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___boxed(
    mut v_msg_7281_: *mut crate::leanh::LeanObject,
    mut v_declHint_7282_: *mut crate::leanh::LeanObject,
    mut v___y_7283_: *mut crate::leanh::LeanObject,
    mut v___y_7284_: *mut crate::leanh::LeanObject,
    mut v___y_7285_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_7286_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_7286_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4(v_msg_7281_, v_declHint_7282_, v___y_7283_, v___y_7284_);
    crate::leanh::lean_dec(v___y_7284_);
    crate::leanh::lean_dec_ref(v___y_7283_);
    return v_res_7286_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__4(
    mut v_00_u03b1_7287_: *mut crate::leanh::LeanObject,
    mut v_ref_7288_: *mut crate::leanh::LeanObject,
    mut v_msg_7289_: *mut crate::leanh::LeanObject,
    mut v___y_7290_: *mut crate::leanh::LeanObject,
    mut v___y_7291_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_7293_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_7293_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__4___redArg(v_ref_7288_, v_msg_7289_, v___y_7290_, v___y_7291_);
    return v___x_7293_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__4___boxed(
    mut v_00_u03b1_7294_: *mut crate::leanh::LeanObject,
    mut v_ref_7295_: *mut crate::leanh::LeanObject,
    mut v_msg_7296_: *mut crate::leanh::LeanObject,
    mut v___y_7297_: *mut crate::leanh::LeanObject,
    mut v___y_7298_: *mut crate::leanh::LeanObject,
    mut v___y_7299_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_7300_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_7300_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__4(v_00_u03b1_7294_, v_ref_7295_, v_msg_7296_, v___y_7297_, v___y_7298_);
    crate::leanh::lean_dec(v___y_7298_);
    crate::leanh::lean_dec_ref(v___y_7297_);
    crate::leanh::lean_dec(v_ref_7295_);
    return v_res_7300_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6(
    mut v_00_u03b1_7301_: *mut crate::leanh::LeanObject,
    mut v_msg_7302_: *mut crate::leanh::LeanObject,
    mut v___y_7303_: *mut crate::leanh::LeanObject,
    mut v___y_7304_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_7306_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_7306_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6___redArg(v_msg_7302_, v___y_7303_, v___y_7304_);
    return v___x_7306_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6___boxed(
    mut v_00_u03b1_7307_: *mut crate::leanh::LeanObject,
    mut v_msg_7308_: *mut crate::leanh::LeanObject,
    mut v___y_7309_: *mut crate::leanh::LeanObject,
    mut v___y_7310_: *mut crate::leanh::LeanObject,
    mut v___y_7311_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_7312_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_7312_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6(v_00_u03b1_7307_, v_msg_7308_, v___y_7309_, v___y_7310_);
    crate::leanh::lean_dec(v___y_7310_);
    crate::leanh::lean_dec_ref(v___y_7309_);
    return v_res_7312_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_applyInjection_x3f(
    mut v_goal_7313_: *mut crate::leanh::LeanObject,
    mut v_fvarId_7314_: *mut crate::leanh::LeanObject,
    mut v_a_7315_: *mut crate::leanh::LeanObject,
    mut v_a_7316_: *mut crate::leanh::LeanObject,
    mut v_a_7317_: *mut crate::leanh::LeanObject,
    mut v_a_7318_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toGoalState_7320_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mvarId_7321_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7323_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7324_: u8 = 0;
    let mut v___x_7325_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_7326_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7328_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7329_: u8 = 0;
    let mut v_val_7330_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7332_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7333_: u8 = 0;
    let mut v___x_7335_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7337_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7339_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7340_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7341_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7342_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7343_: u8 = 0;
    let mut v___x_7344_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7346_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7347_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7348_: u8 = 0;
    let mut v_a_7349_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7351_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7352_: u8 = 0;
    let mut v___x_7354_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7355_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7356_: u8 = 0;
    let mut v_isSharedCheck_7357_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_toGoalState_7320_ = crate::leanh::lean_ctor_get(v_goal_7313_, 0);
                v_mvarId_7321_ = crate::leanh::lean_ctor_get(v_goal_7313_, 1);
                v_isSharedCheck_7357_ = (!crate::leanh::lean_is_exclusive(v_goal_7313_)) as u8;
                if v_isSharedCheck_7357_ == 0 {
                    v___x_7323_ = v_goal_7313_;
                    v_isShared_7324_ = v_isSharedCheck_7357_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_mvarId_7321_);
                    crate::leanh::lean_inc(v_toGoalState_7320_);
                    crate::leanh::lean_dec(v_goal_7313_);
                    v___x_7323_ = crate::leanh::lean_box(0);
                    v_isShared_7324_ = v_isSharedCheck_7357_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_7325_ = l_Lean_Meta_Grind_injection_x3f(
                    v_mvarId_7321_,
                    v_fvarId_7314_,
                    v_a_7315_,
                    v_a_7316_,
                    v_a_7317_,
                    v_a_7318_,
                );
                if crate::leanh::lean_obj_tag(v___x_7325_) == 0 {
                    v_a_7326_ = crate::leanh::lean_ctor_get(v___x_7325_, 0);
                    v_isSharedCheck_7348_ = (!crate::leanh::lean_is_exclusive(v___x_7325_)) as u8;
                    if v_isSharedCheck_7348_ == 0 {
                        v___x_7328_ = v___x_7325_;
                        v_isShared_7329_ = v_isSharedCheck_7348_;
                        state = 2;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_7326_);
                        crate::leanh::lean_dec(v___x_7325_);
                        v___x_7328_ = crate::leanh::lean_box(0);
                        v_isShared_7329_ = v_isSharedCheck_7348_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_7323_);
                    crate::leanh::lean_dec_ref(v_toGoalState_7320_);
                    v_a_7349_ = crate::leanh::lean_ctor_get(v___x_7325_, 0);
                    v_isSharedCheck_7356_ = (!crate::leanh::lean_is_exclusive(v___x_7325_)) as u8;
                    if v_isSharedCheck_7356_ == 0 {
                        v___x_7351_ = v___x_7325_;
                        v_isShared_7352_ = v_isSharedCheck_7356_;
                        state = 8;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_7349_);
                        crate::leanh::lean_dec(v___x_7325_);
                        v___x_7351_ = crate::leanh::lean_box(0);
                        v_isShared_7352_ = v_isSharedCheck_7356_;
                        state = 8;
                        continue;
                    }
                }
            }
            2 => {
                if crate::leanh::lean_obj_tag(v_a_7326_) == 1 {
                    v_val_7330_ = crate::leanh::lean_ctor_get(v_a_7326_, 0);
                    v_isSharedCheck_7343_ = (!crate::leanh::lean_is_exclusive(v_a_7326_)) as u8;
                    if v_isSharedCheck_7343_ == 0 {
                        v___x_7332_ = v_a_7326_;
                        v_isShared_7333_ = v_isSharedCheck_7343_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_val_7330_);
                        crate::leanh::lean_dec(v_a_7326_);
                        v___x_7332_ = crate::leanh::lean_box(0);
                        v_isShared_7333_ = v_isSharedCheck_7343_;
                        state = 3;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_a_7326_);
                    crate::leanh::lean_del_object(v___x_7323_);
                    crate::leanh::lean_dec_ref(v_toGoalState_7320_);
                    v___x_7344_ = crate::leanh::lean_box(0);
                    if v_isShared_7329_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_7328_, 0, v___x_7344_);
                        v___x_7346_ = v___x_7328_;
                        state = 7;
                        continue;
                    } else {
                        v_reuseFailAlloc_7347_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_7347_, 0, v___x_7344_);
                        v___x_7346_ = v_reuseFailAlloc_7347_;
                        state = 7;
                        continue;
                    }
                }
            }
            3 => {
                if v_isShared_7324_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_7323_, 1, v_val_7330_);
                    v___x_7335_ = v___x_7323_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_7342_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7342_, 0, v_toGoalState_7320_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7342_, 1, v_val_7330_);
                    v___x_7335_ = v_reuseFailAlloc_7342_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                if v_isShared_7333_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_7332_, 0, v___x_7335_);
                    v___x_7337_ = v___x_7332_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_7341_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7341_, 0, v___x_7335_);
                    v___x_7337_ = v_reuseFailAlloc_7341_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                if v_isShared_7329_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_7328_, 0, v___x_7337_);
                    v___x_7339_ = v___x_7328_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_7340_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7340_, 0, v___x_7337_);
                    v___x_7339_ = v_reuseFailAlloc_7340_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_7339_;
            }
            7 => {
                return v___x_7346_;
            }
            8 => {
                if v_isShared_7352_ == 0 {
                    v___x_7354_ = v___x_7351_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_7355_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7355_, 0, v_a_7349_);
                    v___x_7354_ = v_reuseFailAlloc_7355_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_7354_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_applyInjection_x3f___boxed(
    mut v_goal_7358_: *mut crate::leanh::LeanObject,
    mut v_fvarId_7359_: *mut crate::leanh::LeanObject,
    mut v_a_7360_: *mut crate::leanh::LeanObject,
    mut v_a_7361_: *mut crate::leanh::LeanObject,
    mut v_a_7362_: *mut crate::leanh::LeanObject,
    mut v_a_7363_: *mut crate::leanh::LeanObject,
    mut v_a_7364_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_7365_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_7365_ = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_applyInjection_x3f(
        v_goal_7358_,
        v_fvarId_7359_,
        v_a_7360_,
        v_a_7361_,
        v_a_7362_,
        v_a_7363_,
    );
    crate::leanh::lean_dec(v_a_7363_);
    crate::leanh::lean_dec_ref(v_a_7362_);
    crate::leanh::lean_dec(v_a_7361_);
    crate::leanh::lean_dec_ref(v_a_7360_);
    return v_res_7365_;
}
pub unsafe fn l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_exfalsoIfNotProp_spec__0___redArg(
    mut v_mvarId_7366_: *mut crate::leanh::LeanObject,
    mut v_x_7367_: *mut crate::leanh::LeanObject,
    mut v___y_7368_: *mut crate::leanh::LeanObject,
    mut v___y_7369_: *mut crate::leanh::LeanObject,
    mut v___y_7370_: *mut crate::leanh::LeanObject,
    mut v___y_7371_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_7373_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_7374_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7376_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7377_: u8 = 0;
    let mut v___x_7379_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7380_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7381_: u8 = 0;
    let mut v_a_7382_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7384_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7385_: u8 = 0;
    let mut v___x_7387_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7388_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7389_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_7373_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(
                    crate::leanh::lean_box(0),
                    v_mvarId_7366_,
                    v_x_7367_,
                    v___y_7368_,
                    v___y_7369_,
                    v___y_7370_,
                    v___y_7371_,
                );
                if crate::leanh::lean_obj_tag(v___x_7373_) == 0 {
                    v_a_7374_ = crate::leanh::lean_ctor_get(v___x_7373_, 0);
                    v_isSharedCheck_7381_ = (!crate::leanh::lean_is_exclusive(v___x_7373_)) as u8;
                    if v_isSharedCheck_7381_ == 0 {
                        v___x_7376_ = v___x_7373_;
                        v_isShared_7377_ = v_isSharedCheck_7381_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_7374_);
                        crate::leanh::lean_dec(v___x_7373_);
                        v___x_7376_ = crate::leanh::lean_box(0);
                        v_isShared_7377_ = v_isSharedCheck_7381_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_7382_ = crate::leanh::lean_ctor_get(v___x_7373_, 0);
                    v_isSharedCheck_7389_ = (!crate::leanh::lean_is_exclusive(v___x_7373_)) as u8;
                    if v_isSharedCheck_7389_ == 0 {
                        v___x_7384_ = v___x_7373_;
                        v_isShared_7385_ = v_isSharedCheck_7389_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_7382_);
                        crate::leanh::lean_dec(v___x_7373_);
                        v___x_7384_ = crate::leanh::lean_box(0);
                        v_isShared_7385_ = v_isSharedCheck_7389_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_7377_ == 0 {
                    v___x_7379_ = v___x_7376_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_7380_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7380_, 0, v_a_7374_);
                    v___x_7379_ = v_reuseFailAlloc_7380_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_7379_;
            }
            3 => {
                if v_isShared_7385_ == 0 {
                    v___x_7387_ = v___x_7384_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_7388_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7388_, 0, v_a_7382_);
                    v___x_7387_ = v_reuseFailAlloc_7388_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_7387_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_exfalsoIfNotProp_spec__0___redArg___boxed(
    mut v_mvarId_7390_: *mut crate::leanh::LeanObject,
    mut v_x_7391_: *mut crate::leanh::LeanObject,
    mut v___y_7392_: *mut crate::leanh::LeanObject,
    mut v___y_7393_: *mut crate::leanh::LeanObject,
    mut v___y_7394_: *mut crate::leanh::LeanObject,
    mut v___y_7395_: *mut crate::leanh::LeanObject,
    mut v___y_7396_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_7397_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_7397_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_exfalsoIfNotProp_spec__0___redArg(v_mvarId_7390_, v_x_7391_, v___y_7392_, v___y_7393_, v___y_7394_, v___y_7395_);
    crate::leanh::lean_dec(v___y_7395_);
    crate::leanh::lean_dec_ref(v___y_7394_);
    crate::leanh::lean_dec(v___y_7393_);
    crate::leanh::lean_dec_ref(v___y_7392_);
    return v_res_7397_;
}
pub unsafe fn l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_exfalsoIfNotProp_spec__0(
    mut v_00_u03b1_7398_: *mut crate::leanh::LeanObject,
    mut v_mvarId_7399_: *mut crate::leanh::LeanObject,
    mut v_x_7400_: *mut crate::leanh::LeanObject,
    mut v___y_7401_: *mut crate::leanh::LeanObject,
    mut v___y_7402_: *mut crate::leanh::LeanObject,
    mut v___y_7403_: *mut crate::leanh::LeanObject,
    mut v___y_7404_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_7406_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_7406_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_exfalsoIfNotProp_spec__0___redArg(v_mvarId_7399_, v_x_7400_, v___y_7401_, v___y_7402_, v___y_7403_, v___y_7404_);
    return v___x_7406_;
}
pub unsafe fn l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_exfalsoIfNotProp_spec__0___boxed(
    mut v_00_u03b1_7407_: *mut crate::leanh::LeanObject,
    mut v_mvarId_7408_: *mut crate::leanh::LeanObject,
    mut v_x_7409_: *mut crate::leanh::LeanObject,
    mut v___y_7410_: *mut crate::leanh::LeanObject,
    mut v___y_7411_: *mut crate::leanh::LeanObject,
    mut v___y_7412_: *mut crate::leanh::LeanObject,
    mut v___y_7413_: *mut crate::leanh::LeanObject,
    mut v___y_7414_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_7415_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_7415_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_exfalsoIfNotProp_spec__0(v_00_u03b1_7407_, v_mvarId_7408_, v_x_7409_, v___y_7410_, v___y_7411_, v___y_7412_, v___y_7413_);
    crate::leanh::lean_dec(v___y_7413_);
    crate::leanh::lean_dec_ref(v___y_7412_);
    crate::leanh::lean_dec(v___y_7411_);
    crate::leanh::lean_dec_ref(v___y_7410_);
    return v_res_7415_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_exfalsoIfNotProp___lam__0(
    mut v_mvarId_7416_: *mut crate::leanh::LeanObject,
    mut v_toGoalState_7417_: *mut crate::leanh::LeanObject,
    mut v_goal_7418_: *mut crate::leanh::LeanObject,
    mut v___y_7419_: *mut crate::leanh::LeanObject,
    mut v___y_7420_: *mut crate::leanh::LeanObject,
    mut v___y_7421_: *mut crate::leanh::LeanObject,
    mut v___y_7422_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_7424_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_7425_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7426_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_7427_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7429_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7430_: u8 = 0;
    let mut v___x_7431_: u8 = 0;
    let mut v___x_7432_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_7433_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7435_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7436_: u8 = 0;
    let mut v___x_7437_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7439_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7440_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7441_: u8 = 0;
    let mut v_a_7442_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7444_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7445_: u8 = 0;
    let mut v___x_7447_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7448_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7449_: u8 = 0;
    let mut v___x_7451_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7452_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7453_: u8 = 0;
    let mut v_a_7454_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7456_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7457_: u8 = 0;
    let mut v___x_7459_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7460_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7461_: u8 = 0;
    let mut v_a_7462_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7464_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7465_: u8 = 0;
    let mut v___x_7467_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7468_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7469_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                crate::leanh::lean_inc(v_mvarId_7416_);
                v___x_7424_ = l_Lean_MVarId_getType(
                    v_mvarId_7416_,
                    v___y_7419_,
                    v___y_7420_,
                    v___y_7421_,
                    v___y_7422_,
                );
                if crate::leanh::lean_obj_tag(v___x_7424_) == 0 {
                    v_a_7425_ = crate::leanh::lean_ctor_get(v___x_7424_, 0);
                    crate::leanh::lean_inc(v_a_7425_);
                    crate::leanh::lean_dec_ref_known(v___x_7424_, 1);
                    v___x_7426_ = l_Lean_Meta_isProp(
                        v_a_7425_,
                        v___y_7419_,
                        v___y_7420_,
                        v___y_7421_,
                        v___y_7422_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_7426_) == 0 {
                        v_a_7427_ = crate::leanh::lean_ctor_get(v___x_7426_, 0);
                        v_isSharedCheck_7453_ =
                            (!crate::leanh::lean_is_exclusive(v___x_7426_)) as u8;
                        if v_isSharedCheck_7453_ == 0 {
                            v___x_7429_ = v___x_7426_;
                            v_isShared_7430_ = v_isSharedCheck_7453_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_7427_);
                            crate::leanh::lean_dec(v___x_7426_);
                            v___x_7429_ = crate::leanh::lean_box(0);
                            v_isShared_7430_ = v_isSharedCheck_7453_;
                            state = 1;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec_ref(v_goal_7418_);
                        crate::leanh::lean_dec_ref(v_toGoalState_7417_);
                        crate::leanh::lean_dec(v_mvarId_7416_);
                        v_a_7454_ = crate::leanh::lean_ctor_get(v___x_7426_, 0);
                        v_isSharedCheck_7461_ =
                            (!crate::leanh::lean_is_exclusive(v___x_7426_)) as u8;
                        if v_isSharedCheck_7461_ == 0 {
                            v___x_7456_ = v___x_7426_;
                            v_isShared_7457_ = v_isSharedCheck_7461_;
                            state = 7;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_7454_);
                            crate::leanh::lean_dec(v___x_7426_);
                            v___x_7456_ = crate::leanh::lean_box(0);
                            v_isShared_7457_ = v_isSharedCheck_7461_;
                            state = 7;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_goal_7418_);
                    crate::leanh::lean_dec_ref(v_toGoalState_7417_);
                    crate::leanh::lean_dec(v_mvarId_7416_);
                    v_a_7462_ = crate::leanh::lean_ctor_get(v___x_7424_, 0);
                    v_isSharedCheck_7469_ = (!crate::leanh::lean_is_exclusive(v___x_7424_)) as u8;
                    if v_isSharedCheck_7469_ == 0 {
                        v___x_7464_ = v___x_7424_;
                        v_isShared_7465_ = v_isSharedCheck_7469_;
                        state = 9;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_7462_);
                        crate::leanh::lean_dec(v___x_7424_);
                        v___x_7464_ = crate::leanh::lean_box(0);
                        v_isShared_7465_ = v_isSharedCheck_7469_;
                        state = 9;
                        continue;
                    }
                }
            }
            1 => {
                v___x_7431_ = (crate::leanh::lean_unbox(v_a_7427_) as u8);
                crate::leanh::lean_dec(v_a_7427_);
                if v___x_7431_ == 0 {
                    crate::leanh::lean_del_object(v___x_7429_);
                    crate::leanh::lean_dec_ref(v_goal_7418_);
                    v___x_7432_ = l_Lean_MVarId_exfalso(
                        v_mvarId_7416_,
                        v___y_7419_,
                        v___y_7420_,
                        v___y_7421_,
                        v___y_7422_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_7432_) == 0 {
                        v_a_7433_ = crate::leanh::lean_ctor_get(v___x_7432_, 0);
                        v_isSharedCheck_7441_ =
                            (!crate::leanh::lean_is_exclusive(v___x_7432_)) as u8;
                        if v_isSharedCheck_7441_ == 0 {
                            v___x_7435_ = v___x_7432_;
                            v_isShared_7436_ = v_isSharedCheck_7441_;
                            state = 2;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_7433_);
                            crate::leanh::lean_dec(v___x_7432_);
                            v___x_7435_ = crate::leanh::lean_box(0);
                            v_isShared_7436_ = v_isSharedCheck_7441_;
                            state = 2;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec_ref(v_toGoalState_7417_);
                        v_a_7442_ = crate::leanh::lean_ctor_get(v___x_7432_, 0);
                        v_isSharedCheck_7449_ =
                            (!crate::leanh::lean_is_exclusive(v___x_7432_)) as u8;
                        if v_isSharedCheck_7449_ == 0 {
                            v___x_7444_ = v___x_7432_;
                            v_isShared_7445_ = v_isSharedCheck_7449_;
                            state = 4;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_7442_);
                            crate::leanh::lean_dec(v___x_7432_);
                            v___x_7444_ = crate::leanh::lean_box(0);
                            v_isShared_7445_ = v_isSharedCheck_7449_;
                            state = 4;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_toGoalState_7417_);
                    crate::leanh::lean_dec(v_mvarId_7416_);
                    if v_isShared_7430_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_7429_, 0, v_goal_7418_);
                        v___x_7451_ = v___x_7429_;
                        state = 6;
                        continue;
                    } else {
                        v_reuseFailAlloc_7452_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_7452_, 0, v_goal_7418_);
                        v___x_7451_ = v_reuseFailAlloc_7452_;
                        state = 6;
                        continue;
                    }
                }
            }
            2 => {
                v___x_7437_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_7437_, 0, v_toGoalState_7417_);
                crate::leanh::lean_ctor_set(v___x_7437_, 1, v_a_7433_);
                if v_isShared_7436_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_7435_, 0, v___x_7437_);
                    v___x_7439_ = v___x_7435_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_7440_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7440_, 0, v___x_7437_);
                    v___x_7439_ = v_reuseFailAlloc_7440_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_7439_;
            }
            4 => {
                if v_isShared_7445_ == 0 {
                    v___x_7447_ = v___x_7444_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_7448_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7448_, 0, v_a_7442_);
                    v___x_7447_ = v_reuseFailAlloc_7448_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_7447_;
            }
            6 => {
                return v___x_7451_;
            }
            7 => {
                if v_isShared_7457_ == 0 {
                    v___x_7459_ = v___x_7456_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_7460_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7460_, 0, v_a_7454_);
                    v___x_7459_ = v_reuseFailAlloc_7460_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_7459_;
            }
            9 => {
                if v_isShared_7465_ == 0 {
                    v___x_7467_ = v___x_7464_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_7468_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7468_, 0, v_a_7462_);
                    v___x_7467_ = v_reuseFailAlloc_7468_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_7467_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_exfalsoIfNotProp___lam__0___boxed(
    mut v_mvarId_7470_: *mut crate::leanh::LeanObject,
    mut v_toGoalState_7471_: *mut crate::leanh::LeanObject,
    mut v_goal_7472_: *mut crate::leanh::LeanObject,
    mut v___y_7473_: *mut crate::leanh::LeanObject,
    mut v___y_7474_: *mut crate::leanh::LeanObject,
    mut v___y_7475_: *mut crate::leanh::LeanObject,
    mut v___y_7476_: *mut crate::leanh::LeanObject,
    mut v___y_7477_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_7478_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_7478_ =
        l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_exfalsoIfNotProp___lam__0(
            v_mvarId_7470_,
            v_toGoalState_7471_,
            v_goal_7472_,
            v___y_7473_,
            v___y_7474_,
            v___y_7475_,
            v___y_7476_,
        );
    crate::leanh::lean_dec(v___y_7476_);
    crate::leanh::lean_dec_ref(v___y_7475_);
    crate::leanh::lean_dec(v___y_7474_);
    crate::leanh::lean_dec_ref(v___y_7473_);
    return v_res_7478_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_exfalsoIfNotProp(
    mut v_goal_7479_: *mut crate::leanh::LeanObject,
    mut v_a_7480_: *mut crate::leanh::LeanObject,
    mut v_a_7481_: *mut crate::leanh::LeanObject,
    mut v_a_7482_: *mut crate::leanh::LeanObject,
    mut v_a_7483_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toGoalState_7485_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mvarId_7486_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_7487_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7488_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_toGoalState_7485_ = crate::leanh::lean_ctor_get(v_goal_7479_, 0);
    crate::leanh::lean_inc_ref(v_toGoalState_7485_);
    v_mvarId_7486_ = crate::leanh::lean_ctor_get(v_goal_7479_, 1);
    crate::leanh::lean_inc_n(v_mvarId_7486_, 2);
    v___f_7487_ = crate::leanh::lean_alloc_closure(l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_exfalsoIfNotProp___lam__0___boxed as *mut core::ffi::c_void, 8, 3);
    crate::leanh::lean_closure_set(v___f_7487_, 0, v_mvarId_7486_);
    crate::leanh::lean_closure_set(v___f_7487_, 1, v_toGoalState_7485_);
    crate::leanh::lean_closure_set(v___f_7487_, 2, v_goal_7479_);
    v___x_7488_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_exfalsoIfNotProp_spec__0___redArg(v_mvarId_7486_, v___f_7487_, v_a_7480_, v_a_7481_, v_a_7482_, v_a_7483_);
    return v___x_7488_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_exfalsoIfNotProp___boxed(
    mut v_goal_7489_: *mut crate::leanh::LeanObject,
    mut v_a_7490_: *mut crate::leanh::LeanObject,
    mut v_a_7491_: *mut crate::leanh::LeanObject,
    mut v_a_7492_: *mut crate::leanh::LeanObject,
    mut v_a_7493_: *mut crate::leanh::LeanObject,
    mut v_a_7494_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_7495_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_7495_ = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_exfalsoIfNotProp(
        v_goal_7489_,
        v_a_7490_,
        v_a_7491_,
        v_a_7492_,
        v_a_7493_,
    );
    crate::leanh::lean_dec(v_a_7493_);
    crate::leanh::lean_dec_ref(v_a_7492_);
    crate::leanh::lean_dec(v_a_7491_);
    crate::leanh::lean_dec_ref(v_a_7490_);
    return v_res_7495_;
}
pub unsafe fn l_Lean_Meta_Grind_Goal_lastDecl_x3f(
    mut v_goal_7496_: *mut crate::leanh::LeanObject,
    mut v_a_7497_: *mut crate::leanh::LeanObject,
    mut v_a_7498_: *mut crate::leanh::LeanObject,
    mut v_a_7499_: *mut crate::leanh::LeanObject,
    mut v_a_7500_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_mvarId_7502_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7503_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_7504_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7506_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7507_: u8 = 0;
    let mut v_lctx_7508_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7509_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7511_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7512_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7513_: u8 = 0;
    let mut v_a_7514_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7516_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7517_: u8 = 0;
    let mut v___x_7519_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7520_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7521_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_mvarId_7502_ = crate::leanh::lean_ctor_get(v_goal_7496_, 1);
                crate::leanh::lean_inc(v_mvarId_7502_);
                crate::leanh::lean_dec_ref(v_goal_7496_);
                v___x_7503_ = l_Lean_MVarId_getDecl(
                    v_mvarId_7502_,
                    v_a_7497_,
                    v_a_7498_,
                    v_a_7499_,
                    v_a_7500_,
                );
                if crate::leanh::lean_obj_tag(v___x_7503_) == 0 {
                    v_a_7504_ = crate::leanh::lean_ctor_get(v___x_7503_, 0);
                    v_isSharedCheck_7513_ = (!crate::leanh::lean_is_exclusive(v___x_7503_)) as u8;
                    if v_isSharedCheck_7513_ == 0 {
                        v___x_7506_ = v___x_7503_;
                        v_isShared_7507_ = v_isSharedCheck_7513_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_7504_);
                        crate::leanh::lean_dec(v___x_7503_);
                        v___x_7506_ = crate::leanh::lean_box(0);
                        v_isShared_7507_ = v_isSharedCheck_7513_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_7514_ = crate::leanh::lean_ctor_get(v___x_7503_, 0);
                    v_isSharedCheck_7521_ = (!crate::leanh::lean_is_exclusive(v___x_7503_)) as u8;
                    if v_isSharedCheck_7521_ == 0 {
                        v___x_7516_ = v___x_7503_;
                        v_isShared_7517_ = v_isSharedCheck_7521_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_7514_);
                        crate::leanh::lean_dec(v___x_7503_);
                        v___x_7516_ = crate::leanh::lean_box(0);
                        v_isShared_7517_ = v_isSharedCheck_7521_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v_lctx_7508_ = crate::leanh::lean_ctor_get(v_a_7504_, 1);
                crate::leanh::lean_inc_ref(v_lctx_7508_);
                crate::leanh::lean_dec(v_a_7504_);
                v___x_7509_ = l_Lean_LocalContext_lastDecl(v_lctx_7508_);
                crate::leanh::lean_dec_ref(v_lctx_7508_);
                if v_isShared_7507_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_7506_, 0, v___x_7509_);
                    v___x_7511_ = v___x_7506_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_7512_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7512_, 0, v___x_7509_);
                    v___x_7511_ = v_reuseFailAlloc_7512_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_7511_;
            }
            3 => {
                if v_isShared_7517_ == 0 {
                    v___x_7519_ = v___x_7516_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_7520_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7520_, 0, v_a_7514_);
                    v___x_7519_ = v_reuseFailAlloc_7520_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_7519_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Grind_Goal_lastDecl_x3f___boxed(
    mut v_goal_7522_: *mut crate::leanh::LeanObject,
    mut v_a_7523_: *mut crate::leanh::LeanObject,
    mut v_a_7524_: *mut crate::leanh::LeanObject,
    mut v_a_7525_: *mut crate::leanh::LeanObject,
    mut v_a_7526_: *mut crate::leanh::LeanObject,
    mut v_a_7527_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_7528_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_7528_ = l_Lean_Meta_Grind_Goal_lastDecl_x3f(
        v_goal_7522_,
        v_a_7523_,
        v_a_7524_,
        v_a_7525_,
        v_a_7526_,
    );
    crate::leanh::lean_dec(v_a_7526_);
    crate::leanh::lean_dec_ref(v_a_7525_);
    crate::leanh::lean_dec(v_a_7524_);
    crate::leanh::lean_dec_ref(v_a_7523_);
    return v_res_7528_;
}
pub unsafe fn l_List_mapTR_loop___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_Action_applyCases_x3f_spec__0(
    mut v_goal_7529_: *mut crate::leanh::LeanObject,
    mut v_a_7530_: *mut crate::leanh::LeanObject,
    mut v_a_7531_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_7532_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_7533_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_7534_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7536_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7537_: u8 = 0;
    let mut v_toGoalState_7538_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7539_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7541_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7543_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7544_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_a_7530_) == 0 {
                    v___x_7532_ = l_List_reverse___redArg(v_a_7531_);
                    return v___x_7532_;
                } else {
                    v_head_7533_ = crate::leanh::lean_ctor_get(v_a_7530_, 0);
                    v_tail_7534_ = crate::leanh::lean_ctor_get(v_a_7530_, 1);
                    v_isSharedCheck_7544_ = (!crate::leanh::lean_is_exclusive(v_a_7530_)) as u8;
                    if v_isSharedCheck_7544_ == 0 {
                        v___x_7536_ = v_a_7530_;
                        v_isShared_7537_ = v_isSharedCheck_7544_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_tail_7534_);
                        crate::leanh::lean_inc(v_head_7533_);
                        crate::leanh::lean_dec(v_a_7530_);
                        v___x_7536_ = crate::leanh::lean_box(0);
                        v_isShared_7537_ = v_isSharedCheck_7544_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_toGoalState_7538_ = crate::leanh::lean_ctor_get(v_goal_7529_, 0);
                crate::leanh::lean_inc_ref(v_toGoalState_7538_);
                v___x_7539_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_7539_, 0, v_toGoalState_7538_);
                crate::leanh::lean_ctor_set(v___x_7539_, 1, v_head_7533_);
                if v_isShared_7537_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_7536_, 1, v_a_7531_);
                    crate::leanh::lean_ctor_set(v___x_7536_, 0, v___x_7539_);
                    v___x_7541_ = v___x_7536_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_7543_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7543_, 0, v___x_7539_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7543_, 1, v_a_7531_);
                    v___x_7541_ = v_reuseFailAlloc_7543_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_a_7530_ = v_tail_7534_;
                v_a_7531_ = v___x_7541_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_mapTR_loop___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_Action_applyCases_x3f_spec__0___boxed(
    mut v_goal_7545_: *mut crate::leanh::LeanObject,
    mut v_a_7546_: *mut crate::leanh::LeanObject,
    mut v_a_7547_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_7548_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_7548_ = l_List_mapTR_loop___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_Action_applyCases_x3f_spec__0(v_goal_7545_, v_a_7546_, v_a_7547_);
    crate::leanh::lean_dec_ref(v_goal_7545_);
    return v_res_7548_;
}
pub unsafe fn l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_Action_applyCases_x3f_spec__1___redArg(
    mut v_kp_7549_: *mut crate::leanh::LeanObject,
    mut v_as_x27_7550_: *mut crate::leanh::LeanObject,
    mut v_b_7551_: *mut crate::leanh::LeanObject,
    mut v___y_7552_: *mut crate::leanh::LeanObject,
    mut v___y_7553_: *mut crate::leanh::LeanObject,
    mut v___y_7554_: *mut crate::leanh::LeanObject,
    mut v___y_7555_: *mut crate::leanh::LeanObject,
    mut v___y_7556_: *mut crate::leanh::LeanObject,
    mut v___y_7557_: *mut crate::leanh::LeanObject,
    mut v___y_7558_: *mut crate::leanh::LeanObject,
    mut v___y_7559_: *mut crate::leanh::LeanObject,
    mut v___y_7560_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_7562_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_7563_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_7564_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7565_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_7566_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_7567_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_7568_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7570_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7571_: u8 = 0;
    let mut v_seq_7572_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7573_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7575_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7577_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7578_: u8 = 0;
    let mut v_fst_7579_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_7580_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7582_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7583_: u8 = 0;
    let mut v_gs_7584_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7585_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7587_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7589_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7590_: u8 = 0;
    let mut v_a_7591_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7593_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7594_: u8 = 0;
    let mut v___x_7596_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7597_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7598_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_as_x27_7550_) == 0 {
                    crate::leanh::lean_dec_ref(v_kp_7549_);
                    v___x_7562_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_7562_, 0, v_b_7551_);
                    return v___x_7562_;
                } else {
                    v_head_7563_ = crate::leanh::lean_ctor_get(v_as_x27_7550_, 0);
                    v_tail_7564_ = crate::leanh::lean_ctor_get(v_as_x27_7550_, 1);
                    crate::leanh::lean_inc_ref(v_kp_7549_);
                    crate::leanh::lean_inc(v___y_7560_);
                    crate::leanh::lean_inc_ref(v___y_7559_);
                    crate::leanh::lean_inc(v___y_7558_);
                    crate::leanh::lean_inc_ref(v___y_7557_);
                    crate::leanh::lean_inc(v___y_7556_);
                    crate::leanh::lean_inc_ref(v___y_7555_);
                    crate::leanh::lean_inc(v___y_7554_);
                    crate::leanh::lean_inc_ref(v___y_7553_);
                    crate::leanh::lean_inc(v___y_7552_);
                    crate::leanh::lean_inc(v_head_7563_);
                    v___x_7565_ = crate::leanh::lean_apply_11(
                        v_kp_7549_,
                        v_head_7563_,
                        v___y_7552_,
                        v___y_7553_,
                        v___y_7554_,
                        v___y_7555_,
                        v___y_7556_,
                        v___y_7557_,
                        v___y_7558_,
                        v___y_7559_,
                        v___y_7560_,
                        crate::leanh::lean_box(0),
                    );
                    if crate::leanh::lean_obj_tag(v___x_7565_) == 0 {
                        v_a_7566_ = crate::leanh::lean_ctor_get(v___x_7565_, 0);
                        crate::leanh::lean_inc(v_a_7566_);
                        crate::leanh::lean_dec_ref_known(v___x_7565_, 1);
                        if crate::leanh::lean_obj_tag(v_a_7566_) == 0 {
                            v_fst_7567_ = crate::leanh::lean_ctor_get(v_b_7551_, 0);
                            v_snd_7568_ = crate::leanh::lean_ctor_get(v_b_7551_, 1);
                            v_isSharedCheck_7578_ =
                                (!crate::leanh::lean_is_exclusive(v_b_7551_)) as u8;
                            if v_isSharedCheck_7578_ == 0 {
                                v___x_7570_ = v_b_7551_;
                                v_isShared_7571_ = v_isSharedCheck_7578_;
                                state = 1;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_snd_7568_);
                                crate::leanh::lean_inc(v_fst_7567_);
                                crate::leanh::lean_dec(v_b_7551_);
                                v___x_7570_ = crate::leanh::lean_box(0);
                                v_isShared_7571_ = v_isSharedCheck_7578_;
                                state = 1;
                                continue;
                            }
                        } else {
                            v_fst_7579_ = crate::leanh::lean_ctor_get(v_b_7551_, 0);
                            v_snd_7580_ = crate::leanh::lean_ctor_get(v_b_7551_, 1);
                            v_isSharedCheck_7590_ =
                                (!crate::leanh::lean_is_exclusive(v_b_7551_)) as u8;
                            if v_isSharedCheck_7590_ == 0 {
                                v___x_7582_ = v_b_7551_;
                                v_isShared_7583_ = v_isSharedCheck_7590_;
                                state = 3;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_snd_7580_);
                                crate::leanh::lean_inc(v_fst_7579_);
                                crate::leanh::lean_dec(v_b_7551_);
                                v___x_7582_ = crate::leanh::lean_box(0);
                                v_isShared_7583_ = v_isSharedCheck_7590_;
                                state = 3;
                                continue;
                            }
                        }
                    } else {
                        crate::leanh::lean_dec_ref(v_b_7551_);
                        crate::leanh::lean_dec_ref(v_kp_7549_);
                        v_a_7591_ = crate::leanh::lean_ctor_get(v___x_7565_, 0);
                        v_isSharedCheck_7598_ =
                            (!crate::leanh::lean_is_exclusive(v___x_7565_)) as u8;
                        if v_isSharedCheck_7598_ == 0 {
                            v___x_7593_ = v___x_7565_;
                            v_isShared_7594_ = v_isSharedCheck_7598_;
                            state = 5;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_7591_);
                            crate::leanh::lean_dec(v___x_7565_);
                            v___x_7593_ = crate::leanh::lean_box(0);
                            v_isShared_7594_ = v_isSharedCheck_7598_;
                            state = 5;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v_seq_7572_ = crate::leanh::lean_ctor_get(v_a_7566_, 0);
                crate::leanh::lean_inc(v_seq_7572_);
                crate::leanh::lean_dec_ref_known(v_a_7566_, 1);
                v___x_7573_ = l_List_foldl___at___00Array_appendList_spec__0___redArg(
                    v_fst_7567_,
                    v_seq_7572_,
                );
                if v_isShared_7571_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_7570_, 0, v___x_7573_);
                    v___x_7575_ = v___x_7570_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_7577_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7577_, 0, v___x_7573_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7577_, 1, v_snd_7568_);
                    v___x_7575_ = v_reuseFailAlloc_7577_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_as_x27_7550_ = v_tail_7564_;
                v_b_7551_ = v___x_7575_;
                state = 0;
                continue;
            }
            3 => {
                v_gs_7584_ = crate::leanh::lean_ctor_get(v_a_7566_, 0);
                crate::leanh::lean_inc(v_gs_7584_);
                crate::leanh::lean_dec_ref_known(v_a_7566_, 1);
                v___x_7585_ = l_List_foldl___at___00Array_appendList_spec__0___redArg(
                    v_snd_7580_,
                    v_gs_7584_,
                );
                if v_isShared_7583_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_7582_, 1, v___x_7585_);
                    v___x_7587_ = v___x_7582_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_7589_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7589_, 0, v_fst_7579_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7589_, 1, v___x_7585_);
                    v___x_7587_ = v_reuseFailAlloc_7589_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v_as_x27_7550_ = v_tail_7564_;
                v_b_7551_ = v___x_7587_;
                state = 0;
                continue;
            }
            5 => {
                if v_isShared_7594_ == 0 {
                    v___x_7596_ = v___x_7593_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_7597_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7597_, 0, v_a_7591_);
                    v___x_7596_ = v_reuseFailAlloc_7597_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_7596_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_Action_applyCases_x3f_spec__1___redArg___boxed(
    mut v_kp_7599_: *mut crate::leanh::LeanObject,
    mut v_as_x27_7600_: *mut crate::leanh::LeanObject,
    mut v_b_7601_: *mut crate::leanh::LeanObject,
    mut v___y_7602_: *mut crate::leanh::LeanObject,
    mut v___y_7603_: *mut crate::leanh::LeanObject,
    mut v___y_7604_: *mut crate::leanh::LeanObject,
    mut v___y_7605_: *mut crate::leanh::LeanObject,
    mut v___y_7606_: *mut crate::leanh::LeanObject,
    mut v___y_7607_: *mut crate::leanh::LeanObject,
    mut v___y_7608_: *mut crate::leanh::LeanObject,
    mut v___y_7609_: *mut crate::leanh::LeanObject,
    mut v___y_7610_: *mut crate::leanh::LeanObject,
    mut v___y_7611_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_7612_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_7612_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_Action_applyCases_x3f_spec__1___redArg(v_kp_7599_, v_as_x27_7600_, v_b_7601_, v___y_7602_, v___y_7603_, v___y_7604_, v___y_7605_, v___y_7606_, v___y_7607_, v___y_7608_, v___y_7609_, v___y_7610_);
    crate::leanh::lean_dec(v___y_7610_);
    crate::leanh::lean_dec_ref(v___y_7609_);
    crate::leanh::lean_dec(v___y_7608_);
    crate::leanh::lean_dec_ref(v___y_7607_);
    crate::leanh::lean_dec(v___y_7606_);
    crate::leanh::lean_dec_ref(v___y_7605_);
    crate::leanh::lean_dec(v___y_7604_);
    crate::leanh::lean_dec_ref(v___y_7603_);
    crate::leanh::lean_dec(v___y_7602_);
    crate::leanh::lean_dec(v_as_x27_7600_);
    return v_res_7612_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_Action_applyCases_x3f___lam__0(
    mut v_fvarId_7617_: *mut crate::leanh::LeanObject,
    mut v_mvarId_7618_: *mut crate::leanh::LeanObject,
    mut v_goal_7619_: *mut crate::leanh::LeanObject,
    mut v_kp_7620_: *mut crate::leanh::LeanObject,
    mut v___y_7621_: *mut crate::leanh::LeanObject,
    mut v___y_7622_: *mut crate::leanh::LeanObject,
    mut v___y_7623_: *mut crate::leanh::LeanObject,
    mut v___y_7624_: *mut crate::leanh::LeanObject,
    mut v___y_7625_: *mut crate::leanh::LeanObject,
    mut v___y_7626_: *mut crate::leanh::LeanObject,
    mut v___y_7627_: *mut crate::leanh::LeanObject,
    mut v___y_7628_: *mut crate::leanh::LeanObject,
    mut v___y_7629_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_7632_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7633_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7634_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7635_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7636_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7637_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7638_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7639_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7640_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7641_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7642_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_7643_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7644_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7645_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7646_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7647_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7648_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_7649_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7651_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7652_: u8 = 0;
    let mut v_fst_7653_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_7654_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7655_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7656_: u8 = 0;
    let mut v___x_7657_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7658_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7659_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7661_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7662_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7663_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7664_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7665_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7667_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7668_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7669_: u8 = 0;
    let mut v_a_7670_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7672_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7673_: u8 = 0;
    let mut v___x_7675_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7676_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7677_: u8 = 0;
    let mut v_a_7678_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7680_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7681_: u8 = 0;
    let mut v___x_7683_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7684_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7685_: u8 = 0;
    let mut v___x_7686_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_7687_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7688_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_7689_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7691_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7692_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7693_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7694_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7695_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7696_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7697_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7698_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7699_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7700_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_declName_7701_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7702_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_7703_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7705_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7706_: u8 = 0;
    let mut v___x_7708_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7709_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7710_: u8 = 0;
    let mut v___x_7711_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_7712_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7714_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7715_: u8 = 0;
    let mut v___x_7716_: u8 = 0;
    let mut v___x_7717_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7719_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7720_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7721_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_7722_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7723_: u8 = 0;
    let mut v___x_7724_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_7725_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7727_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7728_: u8 = 0;
    let mut v___x_7729_: u8 = 0;
    let mut v___x_7730_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7732_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7733_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7734_: u8 = 0;
    let mut v_a_7735_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7737_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7738_: u8 = 0;
    let mut v___x_7740_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7741_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7742_: u8 = 0;
    let mut v_a_7743_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7745_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7746_: u8 = 0;
    let mut v___x_7748_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7749_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7750_: u8 = 0;
    let mut v_isSharedCheck_7751_: u8 = 0;
    let mut v_a_7752_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7754_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7755_: u8 = 0;
    let mut v___x_7757_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7758_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7759_: u8 = 0;
    let mut v_a_7760_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7762_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7763_: u8 = 0;
    let mut v___x_7765_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7766_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7767_: u8 = 0;
    let mut v_a_7768_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7770_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7771_: u8 = 0;
    let mut v___x_7773_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7774_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7775_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                crate::leanh::lean_inc(v_fvarId_7617_);
                v___x_7686_ = l_Lean_FVarId_getType___redArg(
                    v_fvarId_7617_,
                    v___y_7626_,
                    v___y_7628_,
                    v___y_7629_,
                );
                if crate::leanh::lean_obj_tag(v___x_7686_) == 0 {
                    v_a_7687_ = crate::leanh::lean_ctor_get(v___x_7686_, 0);
                    crate::leanh::lean_inc(v_a_7687_);
                    crate::leanh::lean_dec_ref_known(v___x_7686_, 1);
                    crate::leanh::lean_inc(v___y_7629_);
                    crate::leanh::lean_inc_ref(v___y_7628_);
                    crate::leanh::lean_inc(v___y_7627_);
                    crate::leanh::lean_inc_ref(v___y_7626_);
                    v___x_7688_ = lean_whnf(
                        v_a_7687_,
                        v___y_7626_,
                        v___y_7627_,
                        v___y_7628_,
                        v___y_7629_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_7688_) == 0 {
                        v_a_7689_ = crate::leanh::lean_ctor_get(v___x_7688_, 0);
                        crate::leanh::lean_inc(v_a_7689_);
                        crate::leanh::lean_dec_ref_known(v___x_7688_, 1);
                        v___x_7711_ = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isEagerCasesCandidate___redArg(v_a_7689_, v___y_7622_);
                        if crate::leanh::lean_obj_tag(v___x_7711_) == 0 {
                            v_a_7712_ = crate::leanh::lean_ctor_get(v___x_7711_, 0);
                            v_isSharedCheck_7751_ =
                                (!crate::leanh::lean_is_exclusive(v___x_7711_)) as u8;
                            if v_isSharedCheck_7751_ == 0 {
                                v___x_7714_ = v___x_7711_;
                                v_isShared_7715_ = v_isSharedCheck_7751_;
                                state = 12;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_7712_);
                                crate::leanh::lean_dec(v___x_7711_);
                                v___x_7714_ = crate::leanh::lean_box(0);
                                v_isShared_7715_ = v_isSharedCheck_7751_;
                                state = 12;
                                continue;
                            }
                        } else {
                            crate::leanh::lean_dec(v_a_7689_);
                            crate::leanh::lean_dec_ref(v_kp_7620_);
                            crate::leanh::lean_dec(v_mvarId_7618_);
                            crate::leanh::lean_dec(v_fvarId_7617_);
                            v_a_7752_ = crate::leanh::lean_ctor_get(v___x_7711_, 0);
                            v_isSharedCheck_7759_ =
                                (!crate::leanh::lean_is_exclusive(v___x_7711_)) as u8;
                            if v_isSharedCheck_7759_ == 0 {
                                v___x_7754_ = v___x_7711_;
                                v_isShared_7755_ = v_isSharedCheck_7759_;
                                state = 20;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_7752_);
                                crate::leanh::lean_dec(v___x_7711_);
                                v___x_7754_ = crate::leanh::lean_box(0);
                                v_isShared_7755_ = v_isSharedCheck_7759_;
                                state = 20;
                                continue;
                            }
                        }
                    } else {
                        crate::leanh::lean_dec_ref(v_kp_7620_);
                        crate::leanh::lean_dec(v_mvarId_7618_);
                        crate::leanh::lean_dec(v_fvarId_7617_);
                        v_a_7760_ = crate::leanh::lean_ctor_get(v___x_7688_, 0);
                        v_isSharedCheck_7767_ =
                            (!crate::leanh::lean_is_exclusive(v___x_7688_)) as u8;
                        if v_isSharedCheck_7767_ == 0 {
                            v___x_7762_ = v___x_7688_;
                            v_isShared_7763_ = v_isSharedCheck_7767_;
                            state = 22;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_7760_);
                            crate::leanh::lean_dec(v___x_7688_);
                            v___x_7762_ = crate::leanh::lean_box(0);
                            v_isShared_7763_ = v_isSharedCheck_7767_;
                            state = 22;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_kp_7620_);
                    crate::leanh::lean_dec(v_mvarId_7618_);
                    crate::leanh::lean_dec(v_fvarId_7617_);
                    v_a_7768_ = crate::leanh::lean_ctor_get(v___x_7686_, 0);
                    v_isSharedCheck_7775_ = (!crate::leanh::lean_is_exclusive(v___x_7686_)) as u8;
                    if v_isSharedCheck_7775_ == 0 {
                        v___x_7770_ = v___x_7686_;
                        v_isShared_7771_ = v_isSharedCheck_7775_;
                        state = 24;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_7768_);
                        crate::leanh::lean_dec(v___x_7686_);
                        v___x_7770_ = crate::leanh::lean_box(0);
                        v_isShared_7771_ = v_isSharedCheck_7775_;
                        state = 24;
                        continue;
                    }
                }
            }
            1 => {
                v___x_7641_ = l_Lean_mkFVar(v_fvarId_7617_);
                v___x_7642_ = l_Lean_Meta_Grind_cases(
                    v_mvarId_7618_,
                    v___x_7641_,
                    v___y_7637_,
                    v___y_7638_,
                    v___y_7639_,
                    v___y_7640_,
                );
                if crate::leanh::lean_obj_tag(v___x_7642_) == 0 {
                    v_a_7643_ = crate::leanh::lean_ctor_get(v___x_7642_, 0);
                    crate::leanh::lean_inc(v_a_7643_);
                    crate::leanh::lean_dec_ref_known(v___x_7642_, 1);
                    v___x_7644_ = crate::leanh::lean_box(0);
                    v___x_7645_ = l_List_mapTR_loop___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_Action_applyCases_x3f_spec__0(v_goal_7619_, v_a_7643_, v___x_7644_);
                    v___x_7646_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___x_7647_ = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_Action_applyCases_x3f___lam__0___closed__1;
                    v___x_7648_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_Action_applyCases_x3f_spec__1___redArg(v_kp_7620_, v___x_7645_, v___x_7647_, v___y_7632_, v___y_7633_, v___y_7634_, v___y_7635_, v___y_7636_, v___y_7637_, v___y_7638_, v___y_7639_, v___y_7640_);
                    crate::leanh::lean_dec(v___x_7645_);
                    if crate::leanh::lean_obj_tag(v___x_7648_) == 0 {
                        v_a_7649_ = crate::leanh::lean_ctor_get(v___x_7648_, 0);
                        v_isSharedCheck_7669_ =
                            (!crate::leanh::lean_is_exclusive(v___x_7648_)) as u8;
                        if v_isSharedCheck_7669_ == 0 {
                            v___x_7651_ = v___x_7648_;
                            v_isShared_7652_ = v_isSharedCheck_7669_;
                            state = 2;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_7649_);
                            crate::leanh::lean_dec(v___x_7648_);
                            v___x_7651_ = crate::leanh::lean_box(0);
                            v_isShared_7652_ = v_isSharedCheck_7669_;
                            state = 2;
                            continue;
                        }
                    } else {
                        v_a_7670_ = crate::leanh::lean_ctor_get(v___x_7648_, 0);
                        v_isSharedCheck_7677_ =
                            (!crate::leanh::lean_is_exclusive(v___x_7648_)) as u8;
                        if v_isSharedCheck_7677_ == 0 {
                            v___x_7672_ = v___x_7648_;
                            v_isShared_7673_ = v_isSharedCheck_7677_;
                            state = 5;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_7670_);
                            crate::leanh::lean_dec(v___x_7648_);
                            v___x_7672_ = crate::leanh::lean_box(0);
                            v_isShared_7673_ = v_isSharedCheck_7677_;
                            state = 5;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_kp_7620_);
                    v_a_7678_ = crate::leanh::lean_ctor_get(v___x_7642_, 0);
                    v_isSharedCheck_7685_ = (!crate::leanh::lean_is_exclusive(v___x_7642_)) as u8;
                    if v_isSharedCheck_7685_ == 0 {
                        v___x_7680_ = v___x_7642_;
                        v_isShared_7681_ = v_isSharedCheck_7685_;
                        state = 7;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_7678_);
                        crate::leanh::lean_dec(v___x_7642_);
                        v___x_7680_ = crate::leanh::lean_box(0);
                        v_isShared_7681_ = v_isSharedCheck_7685_;
                        state = 7;
                        continue;
                    }
                }
            }
            2 => {
                v_fst_7653_ = crate::leanh::lean_ctor_get(v_a_7649_, 0);
                crate::leanh::lean_inc(v_fst_7653_);
                v_snd_7654_ = crate::leanh::lean_ctor_get(v_a_7649_, 1);
                crate::leanh::lean_inc(v_snd_7654_);
                crate::leanh::lean_dec(v_a_7649_);
                v___x_7655_ = lean_array_get_size(v_snd_7654_);
                v___x_7656_ = lean_nat_dec_eq(v___x_7655_, v___x_7646_);
                if v___x_7656_ == 0 {
                    crate::leanh::lean_dec(v_fst_7653_);
                    v___x_7657_ = lean_array_to_list(v_snd_7654_);
                    v___x_7658_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_7658_, 0, v___x_7657_);
                    v___x_7659_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_7659_, 0, v___x_7658_);
                    if v_isShared_7652_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_7651_, 0, v___x_7659_);
                        v___x_7661_ = v___x_7651_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_7662_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_7662_, 0, v___x_7659_);
                        v___x_7661_ = v_reuseFailAlloc_7662_;
                        state = 3;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_snd_7654_);
                    v___x_7663_ = lean_array_to_list(v_fst_7653_);
                    v___x_7664_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_7664_, 0, v___x_7663_);
                    v___x_7665_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_7665_, 0, v___x_7664_);
                    if v_isShared_7652_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_7651_, 0, v___x_7665_);
                        v___x_7667_ = v___x_7651_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_7668_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_7668_, 0, v___x_7665_);
                        v___x_7667_ = v_reuseFailAlloc_7668_;
                        state = 4;
                        continue;
                    }
                }
            }
            3 => {
                return v___x_7661_;
            }
            4 => {
                return v___x_7667_;
            }
            5 => {
                if v_isShared_7673_ == 0 {
                    v___x_7675_ = v___x_7672_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_7676_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7676_, 0, v_a_7670_);
                    v___x_7675_ = v_reuseFailAlloc_7676_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_7675_;
            }
            7 => {
                if v_isShared_7681_ == 0 {
                    v___x_7683_ = v___x_7680_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_7684_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7684_, 0, v_a_7678_);
                    v___x_7683_ = v_reuseFailAlloc_7684_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_7683_;
            }
            9 => {
                v___x_7700_ = l_Lean_Expr_getAppFn(v_a_7689_);
                crate::leanh::lean_dec(v_a_7689_);
                if crate::leanh::lean_obj_tag(v___x_7700_) == 4 {
                    v_declName_7701_ = crate::leanh::lean_ctor_get(v___x_7700_, 0);
                    crate::leanh::lean_inc(v_declName_7701_);
                    crate::leanh::lean_dec_ref_known(v___x_7700_, 2);
                    v___x_7702_ =
                        l_Lean_Meta_Grind_saveCases___redArg(v_declName_7701_, v___y_7693_);
                    if crate::leanh::lean_obj_tag(v___x_7702_) == 0 {
                        crate::leanh::lean_dec_ref_known(v___x_7702_, 1);
                        v___y_7632_ = v___y_7691_;
                        v___y_7633_ = v___y_7692_;
                        v___y_7634_ = v___y_7693_;
                        v___y_7635_ = v___y_7694_;
                        v___y_7636_ = v___y_7695_;
                        v___y_7637_ = v___y_7696_;
                        v___y_7638_ = v___y_7697_;
                        v___y_7639_ = v___y_7698_;
                        v___y_7640_ = v___y_7699_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_dec_ref(v_kp_7620_);
                        crate::leanh::lean_dec(v_mvarId_7618_);
                        crate::leanh::lean_dec(v_fvarId_7617_);
                        v_a_7703_ = crate::leanh::lean_ctor_get(v___x_7702_, 0);
                        v_isSharedCheck_7710_ =
                            (!crate::leanh::lean_is_exclusive(v___x_7702_)) as u8;
                        if v_isSharedCheck_7710_ == 0 {
                            v___x_7705_ = v___x_7702_;
                            v_isShared_7706_ = v_isSharedCheck_7710_;
                            state = 10;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_7703_);
                            crate::leanh::lean_dec(v___x_7702_);
                            v___x_7705_ = crate::leanh::lean_box(0);
                            v_isShared_7706_ = v_isSharedCheck_7710_;
                            state = 10;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec_ref(v___x_7700_);
                    v___y_7632_ = v___y_7691_;
                    v___y_7633_ = v___y_7692_;
                    v___y_7634_ = v___y_7693_;
                    v___y_7635_ = v___y_7694_;
                    v___y_7636_ = v___y_7695_;
                    v___y_7637_ = v___y_7696_;
                    v___y_7638_ = v___y_7697_;
                    v___y_7639_ = v___y_7698_;
                    v___y_7640_ = v___y_7699_;
                    state = 1;
                    continue;
                }
            }
            10 => {
                if v_isShared_7706_ == 0 {
                    v___x_7708_ = v___x_7705_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_7709_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7709_, 0, v_a_7703_);
                    v___x_7708_ = v_reuseFailAlloc_7709_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                return v___x_7708_;
            }
            12 => {
                v___x_7716_ = (crate::leanh::lean_unbox(v_a_7712_) as u8);
                crate::leanh::lean_dec(v_a_7712_);
                if v___x_7716_ == 0 {
                    crate::leanh::lean_dec(v_a_7689_);
                    crate::leanh::lean_dec_ref(v_kp_7620_);
                    crate::leanh::lean_dec(v_mvarId_7618_);
                    crate::leanh::lean_dec(v_fvarId_7617_);
                    v___x_7717_ = crate::leanh::lean_box(0);
                    if v_isShared_7715_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_7714_, 0, v___x_7717_);
                        v___x_7719_ = v___x_7714_;
                        state = 13;
                        continue;
                    } else {
                        v_reuseFailAlloc_7720_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_7720_, 0, v___x_7717_);
                        v___x_7719_ = v_reuseFailAlloc_7720_;
                        state = 13;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_7714_);
                    v___x_7721_ = l_Lean_Meta_Grind_cheapCasesOnly___redArg(v___y_7622_);
                    if crate::leanh::lean_obj_tag(v___x_7721_) == 0 {
                        v_a_7722_ = crate::leanh::lean_ctor_get(v___x_7721_, 0);
                        crate::leanh::lean_inc(v_a_7722_);
                        crate::leanh::lean_dec_ref_known(v___x_7721_, 1);
                        v___x_7723_ = (crate::leanh::lean_unbox(v_a_7722_) as u8);
                        crate::leanh::lean_dec(v_a_7722_);
                        if v___x_7723_ == 0 {
                            v___y_7691_ = v___y_7621_;
                            v___y_7692_ = v___y_7622_;
                            v___y_7693_ = v___y_7623_;
                            v___y_7694_ = v___y_7624_;
                            v___y_7695_ = v___y_7625_;
                            v___y_7696_ = v___y_7626_;
                            v___y_7697_ = v___y_7627_;
                            v___y_7698_ = v___y_7628_;
                            v___y_7699_ = v___y_7629_;
                            state = 9;
                            continue;
                        } else {
                            v___x_7724_ = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive(v_a_7689_, v___y_7628_, v___y_7629_);
                            if crate::leanh::lean_obj_tag(v___x_7724_) == 0 {
                                v_a_7725_ = crate::leanh::lean_ctor_get(v___x_7724_, 0);
                                v_isSharedCheck_7734_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_7724_)) as u8;
                                if v_isSharedCheck_7734_ == 0 {
                                    v___x_7727_ = v___x_7724_;
                                    v_isShared_7728_ = v_isSharedCheck_7734_;
                                    state = 14;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_a_7725_);
                                    crate::leanh::lean_dec(v___x_7724_);
                                    v___x_7727_ = crate::leanh::lean_box(0);
                                    v_isShared_7728_ = v_isSharedCheck_7734_;
                                    state = 14;
                                    continue;
                                }
                            } else {
                                crate::leanh::lean_dec(v_a_7689_);
                                crate::leanh::lean_dec_ref(v_kp_7620_);
                                crate::leanh::lean_dec(v_mvarId_7618_);
                                crate::leanh::lean_dec(v_fvarId_7617_);
                                v_a_7735_ = crate::leanh::lean_ctor_get(v___x_7724_, 0);
                                v_isSharedCheck_7742_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_7724_)) as u8;
                                if v_isSharedCheck_7742_ == 0 {
                                    v___x_7737_ = v___x_7724_;
                                    v_isShared_7738_ = v_isSharedCheck_7742_;
                                    state = 16;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_a_7735_);
                                    crate::leanh::lean_dec(v___x_7724_);
                                    v___x_7737_ = crate::leanh::lean_box(0);
                                    v_isShared_7738_ = v_isSharedCheck_7742_;
                                    state = 16;
                                    continue;
                                }
                            }
                        }
                    } else {
                        crate::leanh::lean_dec(v_a_7689_);
                        crate::leanh::lean_dec_ref(v_kp_7620_);
                        crate::leanh::lean_dec(v_mvarId_7618_);
                        crate::leanh::lean_dec(v_fvarId_7617_);
                        v_a_7743_ = crate::leanh::lean_ctor_get(v___x_7721_, 0);
                        v_isSharedCheck_7750_ =
                            (!crate::leanh::lean_is_exclusive(v___x_7721_)) as u8;
                        if v_isSharedCheck_7750_ == 0 {
                            v___x_7745_ = v___x_7721_;
                            v_isShared_7746_ = v_isSharedCheck_7750_;
                            state = 18;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_7743_);
                            crate::leanh::lean_dec(v___x_7721_);
                            v___x_7745_ = crate::leanh::lean_box(0);
                            v_isShared_7746_ = v_isSharedCheck_7750_;
                            state = 18;
                            continue;
                        }
                    }
                }
            }
            13 => {
                return v___x_7719_;
            }
            14 => {
                v___x_7729_ = (crate::leanh::lean_unbox(v_a_7725_) as u8);
                crate::leanh::lean_dec(v_a_7725_);
                if v___x_7729_ == 0 {
                    crate::leanh::lean_dec(v_a_7689_);
                    crate::leanh::lean_dec_ref(v_kp_7620_);
                    crate::leanh::lean_dec(v_mvarId_7618_);
                    crate::leanh::lean_dec(v_fvarId_7617_);
                    v___x_7730_ = crate::leanh::lean_box(0);
                    if v_isShared_7728_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_7727_, 0, v___x_7730_);
                        v___x_7732_ = v___x_7727_;
                        state = 15;
                        continue;
                    } else {
                        v_reuseFailAlloc_7733_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_7733_, 0, v___x_7730_);
                        v___x_7732_ = v_reuseFailAlloc_7733_;
                        state = 15;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_7727_);
                    v___y_7691_ = v___y_7621_;
                    v___y_7692_ = v___y_7622_;
                    v___y_7693_ = v___y_7623_;
                    v___y_7694_ = v___y_7624_;
                    v___y_7695_ = v___y_7625_;
                    v___y_7696_ = v___y_7626_;
                    v___y_7697_ = v___y_7627_;
                    v___y_7698_ = v___y_7628_;
                    v___y_7699_ = v___y_7629_;
                    state = 9;
                    continue;
                }
            }
            15 => {
                return v___x_7732_;
            }
            16 => {
                if v_isShared_7738_ == 0 {
                    v___x_7740_ = v___x_7737_;
                    state = 17;
                    continue;
                } else {
                    v_reuseFailAlloc_7741_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7741_, 0, v_a_7735_);
                    v___x_7740_ = v_reuseFailAlloc_7741_;
                    state = 17;
                    continue;
                }
            }
            17 => {
                return v___x_7740_;
            }
            18 => {
                if v_isShared_7746_ == 0 {
                    v___x_7748_ = v___x_7745_;
                    state = 19;
                    continue;
                } else {
                    v_reuseFailAlloc_7749_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7749_, 0, v_a_7743_);
                    v___x_7748_ = v_reuseFailAlloc_7749_;
                    state = 19;
                    continue;
                }
            }
            19 => {
                return v___x_7748_;
            }
            20 => {
                if v_isShared_7755_ == 0 {
                    v___x_7757_ = v___x_7754_;
                    state = 21;
                    continue;
                } else {
                    v_reuseFailAlloc_7758_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7758_, 0, v_a_7752_);
                    v___x_7757_ = v_reuseFailAlloc_7758_;
                    state = 21;
                    continue;
                }
            }
            21 => {
                return v___x_7757_;
            }
            22 => {
                if v_isShared_7763_ == 0 {
                    v___x_7765_ = v___x_7762_;
                    state = 23;
                    continue;
                } else {
                    v_reuseFailAlloc_7766_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7766_, 0, v_a_7760_);
                    v___x_7765_ = v_reuseFailAlloc_7766_;
                    state = 23;
                    continue;
                }
            }
            23 => {
                return v___x_7765_;
            }
            24 => {
                if v_isShared_7771_ == 0 {
                    v___x_7773_ = v___x_7770_;
                    state = 25;
                    continue;
                } else {
                    v_reuseFailAlloc_7774_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7774_, 0, v_a_7768_);
                    v___x_7773_ = v_reuseFailAlloc_7774_;
                    state = 25;
                    continue;
                }
            }
            25 => {
                return v___x_7773_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_Action_applyCases_x3f___lam__0___boxed(
    mut v_fvarId_7776_: *mut crate::leanh::LeanObject,
    mut v_mvarId_7777_: *mut crate::leanh::LeanObject,
    mut v_goal_7778_: *mut crate::leanh::LeanObject,
    mut v_kp_7779_: *mut crate::leanh::LeanObject,
    mut v___y_7780_: *mut crate::leanh::LeanObject,
    mut v___y_7781_: *mut crate::leanh::LeanObject,
    mut v___y_7782_: *mut crate::leanh::LeanObject,
    mut v___y_7783_: *mut crate::leanh::LeanObject,
    mut v___y_7784_: *mut crate::leanh::LeanObject,
    mut v___y_7785_: *mut crate::leanh::LeanObject,
    mut v___y_7786_: *mut crate::leanh::LeanObject,
    mut v___y_7787_: *mut crate::leanh::LeanObject,
    mut v___y_7788_: *mut crate::leanh::LeanObject,
    mut v___y_7789_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_7790_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_7790_ =
        l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_Action_applyCases_x3f___lam__0(
            v_fvarId_7776_,
            v_mvarId_7777_,
            v_goal_7778_,
            v_kp_7779_,
            v___y_7780_,
            v___y_7781_,
            v___y_7782_,
            v___y_7783_,
            v___y_7784_,
            v___y_7785_,
            v___y_7786_,
            v___y_7787_,
            v___y_7788_,
        );
    crate::leanh::lean_dec(v___y_7788_);
    crate::leanh::lean_dec_ref(v___y_7787_);
    crate::leanh::lean_dec(v___y_7786_);
    crate::leanh::lean_dec_ref(v___y_7785_);
    crate::leanh::lean_dec(v___y_7784_);
    crate::leanh::lean_dec_ref(v___y_7783_);
    crate::leanh::lean_dec(v___y_7782_);
    crate::leanh::lean_dec_ref(v___y_7781_);
    crate::leanh::lean_dec(v___y_7780_);
    crate::leanh::lean_dec_ref(v_goal_7778_);
    return v_res_7790_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_Action_applyCases_x3f(
    mut v_goal_7791_: *mut crate::leanh::LeanObject,
    mut v_fvarId_7792_: *mut crate::leanh::LeanObject,
    mut v_kp_7793_: *mut crate::leanh::LeanObject,
    mut v_a_7794_: *mut crate::leanh::LeanObject,
    mut v_a_7795_: *mut crate::leanh::LeanObject,
    mut v_a_7796_: *mut crate::leanh::LeanObject,
    mut v_a_7797_: *mut crate::leanh::LeanObject,
    mut v_a_7798_: *mut crate::leanh::LeanObject,
    mut v_a_7799_: *mut crate::leanh::LeanObject,
    mut v_a_7800_: *mut crate::leanh::LeanObject,
    mut v_a_7801_: *mut crate::leanh::LeanObject,
    mut v_a_7802_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_mvarId_7804_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_7805_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7806_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_mvarId_7804_ = crate::leanh::lean_ctor_get(v_goal_7791_, 1);
    crate::leanh::lean_inc_n(v_mvarId_7804_, 2);
    v___f_7805_ = crate::leanh::lean_alloc_closure(l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_Action_applyCases_x3f___lam__0___boxed as *mut core::ffi::c_void, 14, 4);
    crate::leanh::lean_closure_set(v___f_7805_, 0, v_fvarId_7792_);
    crate::leanh::lean_closure_set(v___f_7805_, 1, v_mvarId_7804_);
    crate::leanh::lean_closure_set(v___f_7805_, 2, v_goal_7791_);
    crate::leanh::lean_closure_set(v___f_7805_, 3, v_kp_7793_);
    v___x_7806_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__3___redArg(v_mvarId_7804_, v___f_7805_, v_a_7794_, v_a_7795_, v_a_7796_, v_a_7797_, v_a_7798_, v_a_7799_, v_a_7800_, v_a_7801_, v_a_7802_);
    return v___x_7806_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_Action_applyCases_x3f___boxed(
    mut v_goal_7807_: *mut crate::leanh::LeanObject,
    mut v_fvarId_7808_: *mut crate::leanh::LeanObject,
    mut v_kp_7809_: *mut crate::leanh::LeanObject,
    mut v_a_7810_: *mut crate::leanh::LeanObject,
    mut v_a_7811_: *mut crate::leanh::LeanObject,
    mut v_a_7812_: *mut crate::leanh::LeanObject,
    mut v_a_7813_: *mut crate::leanh::LeanObject,
    mut v_a_7814_: *mut crate::leanh::LeanObject,
    mut v_a_7815_: *mut crate::leanh::LeanObject,
    mut v_a_7816_: *mut crate::leanh::LeanObject,
    mut v_a_7817_: *mut crate::leanh::LeanObject,
    mut v_a_7818_: *mut crate::leanh::LeanObject,
    mut v_a_7819_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_7820_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_7820_ = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_Action_applyCases_x3f(
        v_goal_7807_,
        v_fvarId_7808_,
        v_kp_7809_,
        v_a_7810_,
        v_a_7811_,
        v_a_7812_,
        v_a_7813_,
        v_a_7814_,
        v_a_7815_,
        v_a_7816_,
        v_a_7817_,
        v_a_7818_,
    );
    crate::leanh::lean_dec(v_a_7818_);
    crate::leanh::lean_dec_ref(v_a_7817_);
    crate::leanh::lean_dec(v_a_7816_);
    crate::leanh::lean_dec_ref(v_a_7815_);
    crate::leanh::lean_dec(v_a_7814_);
    crate::leanh::lean_dec_ref(v_a_7813_);
    crate::leanh::lean_dec(v_a_7812_);
    crate::leanh::lean_dec_ref(v_a_7811_);
    crate::leanh::lean_dec(v_a_7810_);
    return v_res_7820_;
}
pub unsafe fn l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_Action_applyCases_x3f_spec__1(
    mut v_kp_7821_: *mut crate::leanh::LeanObject,
    mut v_as_7822_: *mut crate::leanh::LeanObject,
    mut v_as_x27_7823_: *mut crate::leanh::LeanObject,
    mut v_b_7824_: *mut crate::leanh::LeanObject,
    mut v_a_7825_: *mut crate::leanh::LeanObject,
    mut v___y_7826_: *mut crate::leanh::LeanObject,
    mut v___y_7827_: *mut crate::leanh::LeanObject,
    mut v___y_7828_: *mut crate::leanh::LeanObject,
    mut v___y_7829_: *mut crate::leanh::LeanObject,
    mut v___y_7830_: *mut crate::leanh::LeanObject,
    mut v___y_7831_: *mut crate::leanh::LeanObject,
    mut v___y_7832_: *mut crate::leanh::LeanObject,
    mut v___y_7833_: *mut crate::leanh::LeanObject,
    mut v___y_7834_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_7836_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_7836_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_Action_applyCases_x3f_spec__1___redArg(v_kp_7821_, v_as_x27_7823_, v_b_7824_, v___y_7826_, v___y_7827_, v___y_7828_, v___y_7829_, v___y_7830_, v___y_7831_, v___y_7832_, v___y_7833_, v___y_7834_);
    return v___x_7836_;
}
pub unsafe fn l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_Action_applyCases_x3f_spec__1___boxed(
    mut v_kp_7837_: *mut crate::leanh::LeanObject,
    mut v_as_7838_: *mut crate::leanh::LeanObject,
    mut v_as_x27_7839_: *mut crate::leanh::LeanObject,
    mut v_b_7840_: *mut crate::leanh::LeanObject,
    mut v_a_7841_: *mut crate::leanh::LeanObject,
    mut v___y_7842_: *mut crate::leanh::LeanObject,
    mut v___y_7843_: *mut crate::leanh::LeanObject,
    mut v___y_7844_: *mut crate::leanh::LeanObject,
    mut v___y_7845_: *mut crate::leanh::LeanObject,
    mut v___y_7846_: *mut crate::leanh::LeanObject,
    mut v___y_7847_: *mut crate::leanh::LeanObject,
    mut v___y_7848_: *mut crate::leanh::LeanObject,
    mut v___y_7849_: *mut crate::leanh::LeanObject,
    mut v___y_7850_: *mut crate::leanh::LeanObject,
    mut v___y_7851_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_7852_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_7852_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_Action_applyCases_x3f_spec__1(v_kp_7837_, v_as_7838_, v_as_x27_7839_, v_b_7840_, v_a_7841_, v___y_7842_, v___y_7843_, v___y_7844_, v___y_7845_, v___y_7846_, v___y_7847_, v___y_7848_, v___y_7849_, v___y_7850_);
    crate::leanh::lean_dec(v___y_7850_);
    crate::leanh::lean_dec_ref(v___y_7849_);
    crate::leanh::lean_dec(v___y_7848_);
    crate::leanh::lean_dec_ref(v___y_7847_);
    crate::leanh::lean_dec(v___y_7846_);
    crate::leanh::lean_dec_ref(v___y_7845_);
    crate::leanh::lean_dec(v___y_7844_);
    crate::leanh::lean_dec_ref(v___y_7843_);
    crate::leanh::lean_dec(v___y_7842_);
    crate::leanh::lean_dec(v_as_x27_7839_);
    crate::leanh::lean_dec(v_as_7838_);
    return v_res_7852_;
}
pub unsafe fn l_Lean_Meta_Grind_Action_intro___lam__0(
    mut v_goal_7853_: *mut crate::leanh::LeanObject,
    mut v_fvarId_7854_: *mut crate::leanh::LeanObject,
    mut v_generation_7855_: *mut crate::leanh::LeanObject,
    mut v___y_7856_: *mut crate::leanh::LeanObject,
    mut v___y_7857_: *mut crate::leanh::LeanObject,
    mut v___y_7858_: *mut crate::leanh::LeanObject,
    mut v___y_7859_: *mut crate::leanh::LeanObject,
    mut v___y_7860_: *mut crate::leanh::LeanObject,
    mut v___y_7861_: *mut crate::leanh::LeanObject,
    mut v___y_7862_: *mut crate::leanh::LeanObject,
    mut v___y_7863_: *mut crate::leanh::LeanObject,
    mut v___y_7864_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_7866_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7867_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7869_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7870_: u8 = 0;
    let mut v___x_7871_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7872_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7874_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7875_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7876_: u8 = 0;
    let mut v_unused_7877_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_7878_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7880_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7881_: u8 = 0;
    let mut v___x_7883_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7884_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7885_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_7866_ = lean_st_mk_ref(v_goal_7853_);
                v___x_7867_ = l_Lean_Meta_Grind_addHypothesis(
                    v_fvarId_7854_,
                    v_generation_7855_,
                    v___x_7866_,
                    v___y_7856_,
                    v___y_7857_,
                    v___y_7858_,
                    v___y_7859_,
                    v___y_7860_,
                    v___y_7861_,
                    v___y_7862_,
                    v___y_7863_,
                    v___y_7864_,
                );
                if crate::leanh::lean_obj_tag(v___x_7867_) == 0 {
                    v_isSharedCheck_7876_ = (!crate::leanh::lean_is_exclusive(v___x_7867_)) as u8;
                    if v_isSharedCheck_7876_ == 0 {
                        v_unused_7877_ = crate::leanh::lean_ctor_get(v___x_7867_, 0);
                        crate::leanh::lean_dec(v_unused_7877_);
                        v___x_7869_ = v___x_7867_;
                        v_isShared_7870_ = v_isSharedCheck_7876_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v___x_7867_);
                        v___x_7869_ = crate::leanh::lean_box(0);
                        v_isShared_7870_ = v_isSharedCheck_7876_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v___x_7866_);
                    v_a_7878_ = crate::leanh::lean_ctor_get(v___x_7867_, 0);
                    v_isSharedCheck_7885_ = (!crate::leanh::lean_is_exclusive(v___x_7867_)) as u8;
                    if v_isSharedCheck_7885_ == 0 {
                        v___x_7880_ = v___x_7867_;
                        v_isShared_7881_ = v_isSharedCheck_7885_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_7878_);
                        crate::leanh::lean_dec(v___x_7867_);
                        v___x_7880_ = crate::leanh::lean_box(0);
                        v_isShared_7881_ = v_isSharedCheck_7885_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v___x_7871_ = lean_st_ref_get(v___x_7866_);
                v___x_7872_ = lean_st_ref_get(v___x_7866_);
                crate::leanh::lean_dec(v___x_7866_);
                crate::leanh::lean_dec(v___x_7872_);
                if v_isShared_7870_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_7869_, 0, v___x_7871_);
                    v___x_7874_ = v___x_7869_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_7875_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7875_, 0, v___x_7871_);
                    v___x_7874_ = v_reuseFailAlloc_7875_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_7874_;
            }
            3 => {
                if v_isShared_7881_ == 0 {
                    v___x_7883_ = v___x_7880_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_7884_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7884_, 0, v_a_7878_);
                    v___x_7883_ = v_reuseFailAlloc_7884_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_7883_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Grind_Action_intro___lam__0___boxed(
    mut v_goal_7886_: *mut crate::leanh::LeanObject,
    mut v_fvarId_7887_: *mut crate::leanh::LeanObject,
    mut v_generation_7888_: *mut crate::leanh::LeanObject,
    mut v___y_7889_: *mut crate::leanh::LeanObject,
    mut v___y_7890_: *mut crate::leanh::LeanObject,
    mut v___y_7891_: *mut crate::leanh::LeanObject,
    mut v___y_7892_: *mut crate::leanh::LeanObject,
    mut v___y_7893_: *mut crate::leanh::LeanObject,
    mut v___y_7894_: *mut crate::leanh::LeanObject,
    mut v___y_7895_: *mut crate::leanh::LeanObject,
    mut v___y_7896_: *mut crate::leanh::LeanObject,
    mut v___y_7897_: *mut crate::leanh::LeanObject,
    mut v___y_7898_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_7899_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_7899_ = l_Lean_Meta_Grind_Action_intro___lam__0(
        v_goal_7886_,
        v_fvarId_7887_,
        v_generation_7888_,
        v___y_7889_,
        v___y_7890_,
        v___y_7891_,
        v___y_7892_,
        v___y_7893_,
        v___y_7894_,
        v___y_7895_,
        v___y_7896_,
        v___y_7897_,
    );
    crate::leanh::lean_dec(v___y_7897_);
    crate::leanh::lean_dec_ref(v___y_7896_);
    crate::leanh::lean_dec(v___y_7895_);
    crate::leanh::lean_dec_ref(v___y_7894_);
    crate::leanh::lean_dec(v___y_7893_);
    crate::leanh::lean_dec_ref(v___y_7892_);
    crate::leanh::lean_dec(v___y_7891_);
    crate::leanh::lean_dec_ref(v___y_7890_);
    crate::leanh::lean_dec(v___y_7889_);
    return v_res_7899_;
}
pub unsafe fn l_Lean_Meta_Grind_Action_intro(
    mut v_generation_7902_: *mut crate::leanh::LeanObject,
    mut v_goal_7903_: *mut crate::leanh::LeanObject,
    mut v_kna_7904_: *mut crate::leanh::LeanObject,
    mut v_kp_7905_: *mut crate::leanh::LeanObject,
    mut v_a_7906_: *mut crate::leanh::LeanObject,
    mut v_a_7907_: *mut crate::leanh::LeanObject,
    mut v_a_7908_: *mut crate::leanh::LeanObject,
    mut v_a_7909_: *mut crate::leanh::LeanObject,
    mut v_a_7910_: *mut crate::leanh::LeanObject,
    mut v_a_7911_: *mut crate::leanh::LeanObject,
    mut v_a_7912_: *mut crate::leanh::LeanObject,
    mut v_a_7913_: *mut crate::leanh::LeanObject,
    mut v_a_7914_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toGoalState_7916_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_inconsistent_7917_: u8 = 0;
    let mut v_mvarId_7918_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7919_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_7920_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7921_: u8 = 0;
    let mut v___x_7922_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_7923_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_goal_7924_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7925_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_7926_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toGoalState_7927_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mvarId_7928_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7929_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_7930_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7932_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7933_: u8 = 0;
    let mut v_val_7934_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7936_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7937_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7938_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7939_: u8 = 0;
    let mut v_unused_7940_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_7941_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7942_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_7943_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7945_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7946_: u8 = 0;
    let mut v___x_7948_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7949_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7950_: u8 = 0;
    let mut v_a_7951_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7953_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7954_: u8 = 0;
    let mut v___x_7956_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7957_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7958_: u8 = 0;
    let mut v_fvarId_7959_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_goal_7960_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7961_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_7962_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_7963_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7964_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7965_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_7966_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7968_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7969_: u8 = 0;
    let mut v_val_7970_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7972_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7973_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mvarId_7974_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_7975_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7976_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_7977_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7978_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_7979_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7981_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7982_: u8 = 0;
    let mut v___x_7984_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7985_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7986_: u8 = 0;
    let mut v_isSharedCheck_7987_: u8 = 0;
    let mut v_a_7988_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7990_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7991_: u8 = 0;
    let mut v___x_7993_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7994_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7995_: u8 = 0;
    let mut v_a_7996_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7998_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7999_: u8 = 0;
    let mut v___x_8001_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8002_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_8003_: u8 = 0;
    let mut v_goal_8004_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8005_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fvarId_8006_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_goal_8007_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8008_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_8009_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8011_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_8012_: u8 = 0;
    let mut v_val_8013_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8015_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8016_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8017_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_8018_: u8 = 0;
    let mut v_a_8019_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8021_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_8022_: u8 = 0;
    let mut v___x_8024_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8025_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_8026_: u8 = 0;
    let mut v_a_8027_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8029_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_8030_: u8 = 0;
    let mut v___x_8032_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8033_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_8034_: u8 = 0;
    let mut v___x_8035_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_8036_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8038_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_8039_: u8 = 0;
    let mut v___x_8041_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8042_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_8043_: u8 = 0;
    let mut v___x_8044_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8045_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_toGoalState_7916_ = crate::leanh::lean_ctor_get(v_goal_7903_, 0);
                v_inconsistent_7917_ = crate::leanh::lean_ctor_get_uint8(
                    v_toGoalState_7916_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 17) as u32,
                );
                if v_inconsistent_7917_ == 0 {
                    v_mvarId_7918_ = crate::leanh::lean_ctor_get(v_goal_7903_, 1);
                    crate::leanh::lean_inc(v_mvarId_7918_);
                    v___x_7919_ = l_Lean_MVarId_getType(
                        v_mvarId_7918_,
                        v_a_7911_,
                        v_a_7912_,
                        v_a_7913_,
                        v_a_7914_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_7919_) == 0 {
                        v_a_7920_ = crate::leanh::lean_ctor_get(v___x_7919_, 0);
                        crate::leanh::lean_inc(v_a_7920_);
                        crate::leanh::lean_dec_ref_known(v___x_7919_, 1);
                        v___x_7921_ = l_Lean_Expr_isFalse(v_a_7920_);
                        if v___x_7921_ == 0 {
                            crate::leanh::lean_dec_ref(v_kna_7904_);
                            crate::leanh::lean_inc(v_generation_7902_);
                            v___x_7922_ = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext(v_goal_7903_, v_generation_7902_, v_a_7906_, v_a_7907_, v_a_7908_, v_a_7909_, v_a_7910_, v_a_7911_, v_a_7912_, v_a_7913_, v_a_7914_);
                            if crate::leanh::lean_obj_tag(v___x_7922_) == 0 {
                                v_a_7923_ = crate::leanh::lean_ctor_get(v___x_7922_, 0);
                                crate::leanh::lean_inc(v_a_7923_);
                                crate::leanh::lean_dec_ref_known(v___x_7922_, 1);
                                match crate::leanh::lean_obj_tag(v_a_7923_) {
                                    0 => {
                                        crate::leanh::lean_dec(v_generation_7902_);
                                        v_goal_7924_ = crate::leanh::lean_ctor_get(v_a_7923_, 0);
                                        crate::leanh::lean_inc_ref(v_goal_7924_);
                                        crate::leanh::lean_dec_ref_known(v_a_7923_, 1);
                                        v___x_7925_ = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_exfalsoIfNotProp(v_goal_7924_, v_a_7911_, v_a_7912_, v_a_7913_, v_a_7914_);
                                        if crate::leanh::lean_obj_tag(v___x_7925_) == 0 {
                                            v_a_7926_ = crate::leanh::lean_ctor_get(v___x_7925_, 0);
                                            crate::leanh::lean_inc(v_a_7926_);
                                            crate::leanh::lean_dec_ref_known(v___x_7925_, 1);
                                            v_toGoalState_7927_ =
                                                crate::leanh::lean_ctor_get(v_a_7926_, 0);
                                            v_mvarId_7928_ =
                                                crate::leanh::lean_ctor_get(v_a_7926_, 1);
                                            crate::leanh::lean_inc(v_mvarId_7928_);
                                            v___x_7929_ = l_Lean_MVarId_byContra_x3f(
                                                v_mvarId_7928_,
                                                v_a_7911_,
                                                v_a_7912_,
                                                v_a_7913_,
                                                v_a_7914_,
                                            );
                                            if crate::leanh::lean_obj_tag(v___x_7929_) == 0 {
                                                v_a_7930_ =
                                                    crate::leanh::lean_ctor_get(v___x_7929_, 0);
                                                crate::leanh::lean_inc(v_a_7930_);
                                                crate::leanh::lean_dec_ref_known(v___x_7929_, 1);
                                                if crate::leanh::lean_obj_tag(v_a_7930_) == 1 {
                                                    crate::leanh::lean_inc_ref(v_toGoalState_7927_);
                                                    v_isSharedCheck_7939_ =
                                                        (!crate::leanh::lean_is_exclusive(
                                                            v_a_7926_,
                                                        ))
                                                            as u8;
                                                    if v_isSharedCheck_7939_ == 0 {
                                                        v_unused_7940_ =
                                                            crate::leanh::lean_ctor_get(
                                                                v_a_7926_, 1,
                                                            );
                                                        crate::leanh::lean_dec(v_unused_7940_);
                                                        v_unused_7941_ =
                                                            crate::leanh::lean_ctor_get(
                                                                v_a_7926_, 0,
                                                            );
                                                        crate::leanh::lean_dec(v_unused_7941_);
                                                        v___x_7932_ = v_a_7926_;
                                                        v_isShared_7933_ = v_isSharedCheck_7939_;
                                                        state = 1;
                                                        continue;
                                                    } else {
                                                        crate::leanh::lean_dec(v_a_7926_);
                                                        v___x_7932_ = crate::leanh::lean_box(0);
                                                        v_isShared_7933_ = v_isSharedCheck_7939_;
                                                        state = 1;
                                                        continue;
                                                    }
                                                } else {
                                                    crate::leanh::lean_dec(v_a_7930_);
                                                    crate::leanh::lean_inc(v_a_7914_);
                                                    crate::leanh::lean_inc_ref(v_a_7913_);
                                                    crate::leanh::lean_inc(v_a_7912_);
                                                    crate::leanh::lean_inc_ref(v_a_7911_);
                                                    crate::leanh::lean_inc(v_a_7910_);
                                                    crate::leanh::lean_inc_ref(v_a_7909_);
                                                    crate::leanh::lean_inc(v_a_7908_);
                                                    crate::leanh::lean_inc_ref(v_a_7907_);
                                                    crate::leanh::lean_inc(v_a_7906_);
                                                    v___x_7942_ = crate::leanh::lean_apply_11(
                                                        v_kp_7905_,
                                                        v_a_7926_,
                                                        v_a_7906_,
                                                        v_a_7907_,
                                                        v_a_7908_,
                                                        v_a_7909_,
                                                        v_a_7910_,
                                                        v_a_7911_,
                                                        v_a_7912_,
                                                        v_a_7913_,
                                                        v_a_7914_,
                                                        crate::leanh::lean_box(0),
                                                    );
                                                    return v___x_7942_;
                                                }
                                            } else {
                                                crate::leanh::lean_dec(v_a_7926_);
                                                crate::leanh::lean_dec_ref(v_kp_7905_);
                                                v_a_7943_ =
                                                    crate::leanh::lean_ctor_get(v___x_7929_, 0);
                                                v_isSharedCheck_7950_ =
                                                    (!crate::leanh::lean_is_exclusive(v___x_7929_))
                                                        as u8;
                                                if v_isSharedCheck_7950_ == 0 {
                                                    v___x_7945_ = v___x_7929_;
                                                    v_isShared_7946_ = v_isSharedCheck_7950_;
                                                    state = 3;
                                                    continue;
                                                } else {
                                                    crate::leanh::lean_inc(v_a_7943_);
                                                    crate::leanh::lean_dec(v___x_7929_);
                                                    v___x_7945_ = crate::leanh::lean_box(0);
                                                    v_isShared_7946_ = v_isSharedCheck_7950_;
                                                    state = 3;
                                                    continue;
                                                }
                                            }
                                        } else {
                                            crate::leanh::lean_dec_ref(v_kp_7905_);
                                            v_a_7951_ = crate::leanh::lean_ctor_get(v___x_7925_, 0);
                                            v_isSharedCheck_7958_ =
                                                (!crate::leanh::lean_is_exclusive(v___x_7925_))
                                                    as u8;
                                            if v_isSharedCheck_7958_ == 0 {
                                                v___x_7953_ = v___x_7925_;
                                                v_isShared_7954_ = v_isSharedCheck_7958_;
                                                state = 5;
                                                continue;
                                            } else {
                                                crate::leanh::lean_inc(v_a_7951_);
                                                crate::leanh::lean_dec(v___x_7925_);
                                                v___x_7953_ = crate::leanh::lean_box(0);
                                                v_isShared_7954_ = v_isSharedCheck_7958_;
                                                state = 5;
                                                continue;
                                            }
                                        }
                                    }
                                    1 => {
                                        v_fvarId_7959_ = crate::leanh::lean_ctor_get(v_a_7923_, 0);
                                        crate::leanh::lean_inc_n(v_fvarId_7959_, 2);
                                        v_goal_7960_ = crate::leanh::lean_ctor_get(v_a_7923_, 1);
                                        crate::leanh::lean_inc_ref_n(v_goal_7960_, 2);
                                        crate::leanh::lean_dec_ref_known(v_a_7923_, 2);
                                        v___x_7961_ = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_applyInjection_x3f(v_goal_7960_, v_fvarId_7959_, v_a_7911_, v_a_7912_, v_a_7913_, v_a_7914_);
                                        if crate::leanh::lean_obj_tag(v___x_7961_) == 0 {
                                            v_a_7962_ = crate::leanh::lean_ctor_get(v___x_7961_, 0);
                                            crate::leanh::lean_inc(v_a_7962_);
                                            crate::leanh::lean_dec_ref_known(v___x_7961_, 1);
                                            if crate::leanh::lean_obj_tag(v_a_7962_) == 1 {
                                                crate::leanh::lean_dec_ref(v_goal_7960_);
                                                crate::leanh::lean_dec(v_fvarId_7959_);
                                                crate::leanh::lean_dec(v_generation_7902_);
                                                v_val_7963_ =
                                                    crate::leanh::lean_ctor_get(v_a_7962_, 0);
                                                crate::leanh::lean_inc(v_val_7963_);
                                                crate::leanh::lean_dec_ref_known(v_a_7962_, 1);
                                                crate::leanh::lean_inc(v_a_7914_);
                                                crate::leanh::lean_inc_ref(v_a_7913_);
                                                crate::leanh::lean_inc(v_a_7912_);
                                                crate::leanh::lean_inc_ref(v_a_7911_);
                                                crate::leanh::lean_inc(v_a_7910_);
                                                crate::leanh::lean_inc_ref(v_a_7909_);
                                                crate::leanh::lean_inc(v_a_7908_);
                                                crate::leanh::lean_inc_ref(v_a_7907_);
                                                crate::leanh::lean_inc(v_a_7906_);
                                                v___x_7964_ = crate::leanh::lean_apply_11(
                                                    v_kp_7905_,
                                                    v_val_7963_,
                                                    v_a_7906_,
                                                    v_a_7907_,
                                                    v_a_7908_,
                                                    v_a_7909_,
                                                    v_a_7910_,
                                                    v_a_7911_,
                                                    v_a_7912_,
                                                    v_a_7913_,
                                                    v_a_7914_,
                                                    crate::leanh::lean_box(0),
                                                );
                                                return v___x_7964_;
                                            } else {
                                                crate::leanh::lean_dec(v_a_7962_);
                                                crate::leanh::lean_inc_ref(v_kp_7905_);
                                                crate::leanh::lean_inc(v_fvarId_7959_);
                                                crate::leanh::lean_inc_ref(v_goal_7960_);
                                                v___x_7965_ = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_Action_applyCases_x3f(v_goal_7960_, v_fvarId_7959_, v_kp_7905_, v_a_7906_, v_a_7907_, v_a_7908_, v_a_7909_, v_a_7910_, v_a_7911_, v_a_7912_, v_a_7913_, v_a_7914_);
                                                if crate::leanh::lean_obj_tag(v___x_7965_) == 0 {
                                                    v_a_7966_ =
                                                        crate::leanh::lean_ctor_get(v___x_7965_, 0);
                                                    v_isSharedCheck_7987_ =
                                                        (!crate::leanh::lean_is_exclusive(
                                                            v___x_7965_,
                                                        ))
                                                            as u8;
                                                    if v_isSharedCheck_7987_ == 0 {
                                                        v___x_7968_ = v___x_7965_;
                                                        v_isShared_7969_ = v_isSharedCheck_7987_;
                                                        state = 7;
                                                        continue;
                                                    } else {
                                                        crate::leanh::lean_inc(v_a_7966_);
                                                        crate::leanh::lean_dec(v___x_7965_);
                                                        v___x_7968_ = crate::leanh::lean_box(0);
                                                        v_isShared_7969_ = v_isSharedCheck_7987_;
                                                        state = 7;
                                                        continue;
                                                    }
                                                } else {
                                                    crate::leanh::lean_dec_ref(v_goal_7960_);
                                                    crate::leanh::lean_dec(v_fvarId_7959_);
                                                    crate::leanh::lean_dec_ref(v_kp_7905_);
                                                    crate::leanh::lean_dec(v_generation_7902_);
                                                    v_a_7988_ =
                                                        crate::leanh::lean_ctor_get(v___x_7965_, 0);
                                                    v_isSharedCheck_7995_ =
                                                        (!crate::leanh::lean_is_exclusive(
                                                            v___x_7965_,
                                                        ))
                                                            as u8;
                                                    if v_isSharedCheck_7995_ == 0 {
                                                        v___x_7990_ = v___x_7965_;
                                                        v_isShared_7991_ = v_isSharedCheck_7995_;
                                                        state = 11;
                                                        continue;
                                                    } else {
                                                        crate::leanh::lean_inc(v_a_7988_);
                                                        crate::leanh::lean_dec(v___x_7965_);
                                                        v___x_7990_ = crate::leanh::lean_box(0);
                                                        v_isShared_7991_ = v_isSharedCheck_7995_;
                                                        state = 11;
                                                        continue;
                                                    }
                                                }
                                            }
                                        } else {
                                            crate::leanh::lean_dec_ref(v_goal_7960_);
                                            crate::leanh::lean_dec(v_fvarId_7959_);
                                            crate::leanh::lean_dec_ref(v_kp_7905_);
                                            crate::leanh::lean_dec(v_generation_7902_);
                                            v_a_7996_ = crate::leanh::lean_ctor_get(v___x_7961_, 0);
                                            v_isSharedCheck_8003_ =
                                                (!crate::leanh::lean_is_exclusive(v___x_7961_))
                                                    as u8;
                                            if v_isSharedCheck_8003_ == 0 {
                                                v___x_7998_ = v___x_7961_;
                                                v_isShared_7999_ = v_isSharedCheck_8003_;
                                                state = 13;
                                                continue;
                                            } else {
                                                crate::leanh::lean_inc(v_a_7996_);
                                                crate::leanh::lean_dec(v___x_7961_);
                                                v___x_7998_ = crate::leanh::lean_box(0);
                                                v_isShared_7999_ = v_isSharedCheck_8003_;
                                                state = 13;
                                                continue;
                                            }
                                        }
                                    }
                                    2 => {
                                        crate::leanh::lean_dec(v_generation_7902_);
                                        v_goal_8004_ = crate::leanh::lean_ctor_get(v_a_7923_, 0);
                                        crate::leanh::lean_inc_ref(v_goal_8004_);
                                        crate::leanh::lean_dec_ref_known(v_a_7923_, 1);
                                        crate::leanh::lean_inc(v_a_7914_);
                                        crate::leanh::lean_inc_ref(v_a_7913_);
                                        crate::leanh::lean_inc(v_a_7912_);
                                        crate::leanh::lean_inc_ref(v_a_7911_);
                                        crate::leanh::lean_inc(v_a_7910_);
                                        crate::leanh::lean_inc_ref(v_a_7909_);
                                        crate::leanh::lean_inc(v_a_7908_);
                                        crate::leanh::lean_inc_ref(v_a_7907_);
                                        crate::leanh::lean_inc(v_a_7906_);
                                        v___x_8005_ = crate::leanh::lean_apply_11(
                                            v_kp_7905_,
                                            v_goal_8004_,
                                            v_a_7906_,
                                            v_a_7907_,
                                            v_a_7908_,
                                            v_a_7909_,
                                            v_a_7910_,
                                            v_a_7911_,
                                            v_a_7912_,
                                            v_a_7913_,
                                            v_a_7914_,
                                            crate::leanh::lean_box(0),
                                        );
                                        return v___x_8005_;
                                    }
                                    _ => {
                                        crate::leanh::lean_dec(v_generation_7902_);
                                        v_fvarId_8006_ = crate::leanh::lean_ctor_get(v_a_7923_, 0);
                                        crate::leanh::lean_inc(v_fvarId_8006_);
                                        v_goal_8007_ = crate::leanh::lean_ctor_get(v_a_7923_, 1);
                                        crate::leanh::lean_inc_ref_n(v_goal_8007_, 2);
                                        crate::leanh::lean_dec_ref_known(v_a_7923_, 2);
                                        crate::leanh::lean_inc_ref(v_kp_7905_);
                                        v___x_8008_ = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_Action_applyCases_x3f(v_goal_8007_, v_fvarId_8006_, v_kp_7905_, v_a_7906_, v_a_7907_, v_a_7908_, v_a_7909_, v_a_7910_, v_a_7911_, v_a_7912_, v_a_7913_, v_a_7914_);
                                        if crate::leanh::lean_obj_tag(v___x_8008_) == 0 {
                                            v_a_8009_ = crate::leanh::lean_ctor_get(v___x_8008_, 0);
                                            v_isSharedCheck_8018_ =
                                                (!crate::leanh::lean_is_exclusive(v___x_8008_))
                                                    as u8;
                                            if v_isSharedCheck_8018_ == 0 {
                                                v___x_8011_ = v___x_8008_;
                                                v_isShared_8012_ = v_isSharedCheck_8018_;
                                                state = 15;
                                                continue;
                                            } else {
                                                crate::leanh::lean_inc(v_a_8009_);
                                                crate::leanh::lean_dec(v___x_8008_);
                                                v___x_8011_ = crate::leanh::lean_box(0);
                                                v_isShared_8012_ = v_isSharedCheck_8018_;
                                                state = 15;
                                                continue;
                                            }
                                        } else {
                                            crate::leanh::lean_dec_ref(v_goal_8007_);
                                            crate::leanh::lean_dec_ref(v_kp_7905_);
                                            v_a_8019_ = crate::leanh::lean_ctor_get(v___x_8008_, 0);
                                            v_isSharedCheck_8026_ =
                                                (!crate::leanh::lean_is_exclusive(v___x_8008_))
                                                    as u8;
                                            if v_isSharedCheck_8026_ == 0 {
                                                v___x_8021_ = v___x_8008_;
                                                v_isShared_8022_ = v_isSharedCheck_8026_;
                                                state = 17;
                                                continue;
                                            } else {
                                                crate::leanh::lean_inc(v_a_8019_);
                                                crate::leanh::lean_dec(v___x_8008_);
                                                v___x_8021_ = crate::leanh::lean_box(0);
                                                v_isShared_8022_ = v_isSharedCheck_8026_;
                                                state = 17;
                                                continue;
                                            }
                                        }
                                    }
                                }
                            } else {
                                crate::leanh::lean_dec_ref(v_kp_7905_);
                                crate::leanh::lean_dec(v_generation_7902_);
                                v_a_8027_ = crate::leanh::lean_ctor_get(v___x_7922_, 0);
                                v_isSharedCheck_8034_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_7922_)) as u8;
                                if v_isSharedCheck_8034_ == 0 {
                                    v___x_8029_ = v___x_7922_;
                                    v_isShared_8030_ = v_isSharedCheck_8034_;
                                    state = 19;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_a_8027_);
                                    crate::leanh::lean_dec(v___x_7922_);
                                    v___x_8029_ = crate::leanh::lean_box(0);
                                    v_isShared_8030_ = v_isSharedCheck_8034_;
                                    state = 19;
                                    continue;
                                }
                            }
                        } else {
                            crate::leanh::lean_dec_ref(v_kp_7905_);
                            crate::leanh::lean_dec(v_generation_7902_);
                            crate::leanh::lean_inc(v_a_7914_);
                            crate::leanh::lean_inc_ref(v_a_7913_);
                            crate::leanh::lean_inc(v_a_7912_);
                            crate::leanh::lean_inc_ref(v_a_7911_);
                            crate::leanh::lean_inc(v_a_7910_);
                            crate::leanh::lean_inc_ref(v_a_7909_);
                            crate::leanh::lean_inc(v_a_7908_);
                            crate::leanh::lean_inc_ref(v_a_7907_);
                            crate::leanh::lean_inc(v_a_7906_);
                            v___x_8035_ = crate::leanh::lean_apply_11(
                                v_kna_7904_,
                                v_goal_7903_,
                                v_a_7906_,
                                v_a_7907_,
                                v_a_7908_,
                                v_a_7909_,
                                v_a_7910_,
                                v_a_7911_,
                                v_a_7912_,
                                v_a_7913_,
                                v_a_7914_,
                                crate::leanh::lean_box(0),
                            );
                            return v___x_8035_;
                        }
                    } else {
                        crate::leanh::lean_dec_ref(v_kp_7905_);
                        crate::leanh::lean_dec_ref(v_kna_7904_);
                        crate::leanh::lean_dec_ref(v_goal_7903_);
                        crate::leanh::lean_dec(v_generation_7902_);
                        v_a_8036_ = crate::leanh::lean_ctor_get(v___x_7919_, 0);
                        v_isSharedCheck_8043_ =
                            (!crate::leanh::lean_is_exclusive(v___x_7919_)) as u8;
                        if v_isSharedCheck_8043_ == 0 {
                            v___x_8038_ = v___x_7919_;
                            v_isShared_8039_ = v_isSharedCheck_8043_;
                            state = 21;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_8036_);
                            crate::leanh::lean_dec(v___x_7919_);
                            v___x_8038_ = crate::leanh::lean_box(0);
                            v_isShared_8039_ = v_isSharedCheck_8043_;
                            state = 21;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_kp_7905_);
                    crate::leanh::lean_dec_ref(v_kna_7904_);
                    crate::leanh::lean_dec_ref(v_goal_7903_);
                    crate::leanh::lean_dec(v_generation_7902_);
                    v___x_8044_ = l_Lean_Meta_Grind_Action_intro___closed__0;
                    v___x_8045_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_8045_, 0, v___x_8044_);
                    return v___x_8045_;
                }
            }
            1 => {
                v_val_7934_ = crate::leanh::lean_ctor_get(v_a_7930_, 0);
                crate::leanh::lean_inc(v_val_7934_);
                crate::leanh::lean_dec_ref_known(v_a_7930_, 1);
                if v_isShared_7933_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_7932_, 1, v_val_7934_);
                    v___x_7936_ = v___x_7932_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_7938_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7938_, 0, v_toGoalState_7927_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7938_, 1, v_val_7934_);
                    v___x_7936_ = v_reuseFailAlloc_7938_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                crate::leanh::lean_inc(v_a_7914_);
                crate::leanh::lean_inc_ref(v_a_7913_);
                crate::leanh::lean_inc(v_a_7912_);
                crate::leanh::lean_inc_ref(v_a_7911_);
                crate::leanh::lean_inc(v_a_7910_);
                crate::leanh::lean_inc_ref(v_a_7909_);
                crate::leanh::lean_inc(v_a_7908_);
                crate::leanh::lean_inc_ref(v_a_7907_);
                crate::leanh::lean_inc(v_a_7906_);
                v___x_7937_ = crate::leanh::lean_apply_11(
                    v_kp_7905_,
                    v___x_7936_,
                    v_a_7906_,
                    v_a_7907_,
                    v_a_7908_,
                    v_a_7909_,
                    v_a_7910_,
                    v_a_7911_,
                    v_a_7912_,
                    v_a_7913_,
                    v_a_7914_,
                    crate::leanh::lean_box(0),
                );
                return v___x_7937_;
            }
            3 => {
                if v_isShared_7946_ == 0 {
                    v___x_7948_ = v___x_7945_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_7949_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7949_, 0, v_a_7943_);
                    v___x_7948_ = v_reuseFailAlloc_7949_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_7948_;
            }
            5 => {
                if v_isShared_7954_ == 0 {
                    v___x_7956_ = v___x_7953_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_7957_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7957_, 0, v_a_7951_);
                    v___x_7956_ = v_reuseFailAlloc_7957_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_7956_;
            }
            7 => {
                if crate::leanh::lean_obj_tag(v_a_7966_) == 1 {
                    crate::leanh::lean_dec_ref(v_goal_7960_);
                    crate::leanh::lean_dec(v_fvarId_7959_);
                    crate::leanh::lean_dec_ref(v_kp_7905_);
                    crate::leanh::lean_dec(v_generation_7902_);
                    v_val_7970_ = crate::leanh::lean_ctor_get(v_a_7966_, 0);
                    crate::leanh::lean_inc(v_val_7970_);
                    crate::leanh::lean_dec_ref_known(v_a_7966_, 1);
                    if v_isShared_7969_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_7968_, 0, v_val_7970_);
                        v___x_7972_ = v___x_7968_;
                        state = 8;
                        continue;
                    } else {
                        v_reuseFailAlloc_7973_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_7973_, 0, v_val_7970_);
                        v___x_7972_ = v_reuseFailAlloc_7973_;
                        state = 8;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_7968_);
                    crate::leanh::lean_dec(v_a_7966_);
                    v_mvarId_7974_ = crate::leanh::lean_ctor_get(v_goal_7960_, 1);
                    crate::leanh::lean_inc(v_mvarId_7974_);
                    v___f_7975_ = crate::leanh::lean_alloc_closure(
                        l_Lean_Meta_Grind_Action_intro___lam__0___boxed as *mut core::ffi::c_void,
                        13,
                        3,
                    );
                    crate::leanh::lean_closure_set(v___f_7975_, 0, v_goal_7960_);
                    crate::leanh::lean_closure_set(v___f_7975_, 1, v_fvarId_7959_);
                    crate::leanh::lean_closure_set(v___f_7975_, 2, v_generation_7902_);
                    v___x_7976_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__3___redArg(v_mvarId_7974_, v___f_7975_, v_a_7906_, v_a_7907_, v_a_7908_, v_a_7909_, v_a_7910_, v_a_7911_, v_a_7912_, v_a_7913_, v_a_7914_);
                    if crate::leanh::lean_obj_tag(v___x_7976_) == 0 {
                        v_a_7977_ = crate::leanh::lean_ctor_get(v___x_7976_, 0);
                        crate::leanh::lean_inc(v_a_7977_);
                        crate::leanh::lean_dec_ref_known(v___x_7976_, 1);
                        crate::leanh::lean_inc(v_a_7914_);
                        crate::leanh::lean_inc_ref(v_a_7913_);
                        crate::leanh::lean_inc(v_a_7912_);
                        crate::leanh::lean_inc_ref(v_a_7911_);
                        crate::leanh::lean_inc(v_a_7910_);
                        crate::leanh::lean_inc_ref(v_a_7909_);
                        crate::leanh::lean_inc(v_a_7908_);
                        crate::leanh::lean_inc_ref(v_a_7907_);
                        crate::leanh::lean_inc(v_a_7906_);
                        v___x_7978_ = crate::leanh::lean_apply_11(
                            v_kp_7905_,
                            v_a_7977_,
                            v_a_7906_,
                            v_a_7907_,
                            v_a_7908_,
                            v_a_7909_,
                            v_a_7910_,
                            v_a_7911_,
                            v_a_7912_,
                            v_a_7913_,
                            v_a_7914_,
                            crate::leanh::lean_box(0),
                        );
                        return v___x_7978_;
                    } else {
                        crate::leanh::lean_dec_ref(v_kp_7905_);
                        v_a_7979_ = crate::leanh::lean_ctor_get(v___x_7976_, 0);
                        v_isSharedCheck_7986_ =
                            (!crate::leanh::lean_is_exclusive(v___x_7976_)) as u8;
                        if v_isSharedCheck_7986_ == 0 {
                            v___x_7981_ = v___x_7976_;
                            v_isShared_7982_ = v_isSharedCheck_7986_;
                            state = 9;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_7979_);
                            crate::leanh::lean_dec(v___x_7976_);
                            v___x_7981_ = crate::leanh::lean_box(0);
                            v_isShared_7982_ = v_isSharedCheck_7986_;
                            state = 9;
                            continue;
                        }
                    }
                }
            }
            8 => {
                return v___x_7972_;
            }
            9 => {
                if v_isShared_7982_ == 0 {
                    v___x_7984_ = v___x_7981_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_7985_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7985_, 0, v_a_7979_);
                    v___x_7984_ = v_reuseFailAlloc_7985_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_7984_;
            }
            11 => {
                if v_isShared_7991_ == 0 {
                    v___x_7993_ = v___x_7990_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_7994_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7994_, 0, v_a_7988_);
                    v___x_7993_ = v_reuseFailAlloc_7994_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                return v___x_7993_;
            }
            13 => {
                if v_isShared_7999_ == 0 {
                    v___x_8001_ = v___x_7998_;
                    state = 14;
                    continue;
                } else {
                    v_reuseFailAlloc_8002_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_8002_, 0, v_a_7996_);
                    v___x_8001_ = v_reuseFailAlloc_8002_;
                    state = 14;
                    continue;
                }
            }
            14 => {
                return v___x_8001_;
            }
            15 => {
                if crate::leanh::lean_obj_tag(v_a_8009_) == 1 {
                    crate::leanh::lean_dec_ref(v_goal_8007_);
                    crate::leanh::lean_dec_ref(v_kp_7905_);
                    v_val_8013_ = crate::leanh::lean_ctor_get(v_a_8009_, 0);
                    crate::leanh::lean_inc(v_val_8013_);
                    crate::leanh::lean_dec_ref_known(v_a_8009_, 1);
                    if v_isShared_8012_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_8011_, 0, v_val_8013_);
                        v___x_8015_ = v___x_8011_;
                        state = 16;
                        continue;
                    } else {
                        v_reuseFailAlloc_8016_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_8016_, 0, v_val_8013_);
                        v___x_8015_ = v_reuseFailAlloc_8016_;
                        state = 16;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_8011_);
                    crate::leanh::lean_dec(v_a_8009_);
                    crate::leanh::lean_inc(v_a_7914_);
                    crate::leanh::lean_inc_ref(v_a_7913_);
                    crate::leanh::lean_inc(v_a_7912_);
                    crate::leanh::lean_inc_ref(v_a_7911_);
                    crate::leanh::lean_inc(v_a_7910_);
                    crate::leanh::lean_inc_ref(v_a_7909_);
                    crate::leanh::lean_inc(v_a_7908_);
                    crate::leanh::lean_inc_ref(v_a_7907_);
                    crate::leanh::lean_inc(v_a_7906_);
                    v___x_8017_ = crate::leanh::lean_apply_11(
                        v_kp_7905_,
                        v_goal_8007_,
                        v_a_7906_,
                        v_a_7907_,
                        v_a_7908_,
                        v_a_7909_,
                        v_a_7910_,
                        v_a_7911_,
                        v_a_7912_,
                        v_a_7913_,
                        v_a_7914_,
                        crate::leanh::lean_box(0),
                    );
                    return v___x_8017_;
                }
            }
            16 => {
                return v___x_8015_;
            }
            17 => {
                if v_isShared_8022_ == 0 {
                    v___x_8024_ = v___x_8021_;
                    state = 18;
                    continue;
                } else {
                    v_reuseFailAlloc_8025_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_8025_, 0, v_a_8019_);
                    v___x_8024_ = v_reuseFailAlloc_8025_;
                    state = 18;
                    continue;
                }
            }
            18 => {
                return v___x_8024_;
            }
            19 => {
                if v_isShared_8030_ == 0 {
                    v___x_8032_ = v___x_8029_;
                    state = 20;
                    continue;
                } else {
                    v_reuseFailAlloc_8033_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_8033_, 0, v_a_8027_);
                    v___x_8032_ = v_reuseFailAlloc_8033_;
                    state = 20;
                    continue;
                }
            }
            20 => {
                return v___x_8032_;
            }
            21 => {
                if v_isShared_8039_ == 0 {
                    v___x_8041_ = v___x_8038_;
                    state = 22;
                    continue;
                } else {
                    v_reuseFailAlloc_8042_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_8042_, 0, v_a_8036_);
                    v___x_8041_ = v_reuseFailAlloc_8042_;
                    state = 22;
                    continue;
                }
            }
            22 => {
                return v___x_8041_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Grind_Action_intro___boxed(
    mut v_generation_8046_: *mut crate::leanh::LeanObject,
    mut v_goal_8047_: *mut crate::leanh::LeanObject,
    mut v_kna_8048_: *mut crate::leanh::LeanObject,
    mut v_kp_8049_: *mut crate::leanh::LeanObject,
    mut v_a_8050_: *mut crate::leanh::LeanObject,
    mut v_a_8051_: *mut crate::leanh::LeanObject,
    mut v_a_8052_: *mut crate::leanh::LeanObject,
    mut v_a_8053_: *mut crate::leanh::LeanObject,
    mut v_a_8054_: *mut crate::leanh::LeanObject,
    mut v_a_8055_: *mut crate::leanh::LeanObject,
    mut v_a_8056_: *mut crate::leanh::LeanObject,
    mut v_a_8057_: *mut crate::leanh::LeanObject,
    mut v_a_8058_: *mut crate::leanh::LeanObject,
    mut v_a_8059_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_8060_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_8060_ = l_Lean_Meta_Grind_Action_intro(
        v_generation_8046_,
        v_goal_8047_,
        v_kna_8048_,
        v_kp_8049_,
        v_a_8050_,
        v_a_8051_,
        v_a_8052_,
        v_a_8053_,
        v_a_8054_,
        v_a_8055_,
        v_a_8056_,
        v_a_8057_,
        v_a_8058_,
    );
    crate::leanh::lean_dec(v_a_8058_);
    crate::leanh::lean_dec_ref(v_a_8057_);
    crate::leanh::lean_dec(v_a_8056_);
    crate::leanh::lean_dec_ref(v_a_8055_);
    crate::leanh::lean_dec(v_a_8054_);
    crate::leanh::lean_dec_ref(v_a_8053_);
    crate::leanh::lean_dec(v_a_8052_);
    crate::leanh::lean_dec_ref(v_a_8051_);
    crate::leanh::lean_dec(v_a_8050_);
    return v_res_8060_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_Action_hugeNumber()
-> *mut crate::leanh::LeanObject {
    let mut v___x_8061_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_8061_ = crate::leanh::lean_unsigned_to_nat(1000000);
    return v___x_8061_;
}
pub unsafe fn l_Lean_Meta_Grind_Action_intros___lam__0(
    mut v___y_8062_: *mut crate::leanh::LeanObject,
    mut v___y_8063_: *mut crate::leanh::LeanObject,
    mut v___y_8064_: *mut crate::leanh::LeanObject,
    mut v___y_8065_: *mut crate::leanh::LeanObject,
    mut v___y_8066_: *mut crate::leanh::LeanObject,
    mut v___y_8067_: *mut crate::leanh::LeanObject,
    mut v___y_8068_: *mut crate::leanh::LeanObject,
    mut v___y_8069_: *mut crate::leanh::LeanObject,
    mut v___y_8070_: *mut crate::leanh::LeanObject,
    mut v___y_8071_: *mut crate::leanh::LeanObject,
    mut v___y_8072_: *mut crate::leanh::LeanObject,
    mut v___y_8073_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_8075_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_8075_ = l_Lean_Meta_Grind_Action_group___redArg(
        v___y_8062_,
        v___y_8064_,
        v___y_8065_,
        v___y_8066_,
        v___y_8067_,
        v___y_8068_,
        v___y_8069_,
        v___y_8070_,
        v___y_8071_,
        v___y_8072_,
        v___y_8073_,
    );
    return v___x_8075_;
}
pub unsafe fn l_Lean_Meta_Grind_Action_intros___lam__0___boxed(
    mut v___y_8076_: *mut crate::leanh::LeanObject,
    mut v___y_8077_: *mut crate::leanh::LeanObject,
    mut v___y_8078_: *mut crate::leanh::LeanObject,
    mut v___y_8079_: *mut crate::leanh::LeanObject,
    mut v___y_8080_: *mut crate::leanh::LeanObject,
    mut v___y_8081_: *mut crate::leanh::LeanObject,
    mut v___y_8082_: *mut crate::leanh::LeanObject,
    mut v___y_8083_: *mut crate::leanh::LeanObject,
    mut v___y_8084_: *mut crate::leanh::LeanObject,
    mut v___y_8085_: *mut crate::leanh::LeanObject,
    mut v___y_8086_: *mut crate::leanh::LeanObject,
    mut v___y_8087_: *mut crate::leanh::LeanObject,
    mut v___y_8088_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_8089_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_8089_ = l_Lean_Meta_Grind_Action_intros___lam__0(
        v___y_8076_,
        v___y_8077_,
        v___y_8078_,
        v___y_8079_,
        v___y_8080_,
        v___y_8081_,
        v___y_8082_,
        v___y_8083_,
        v___y_8084_,
        v___y_8085_,
        v___y_8086_,
        v___y_8087_,
    );
    crate::leanh::lean_dec(v___y_8087_);
    crate::leanh::lean_dec_ref(v___y_8086_);
    crate::leanh::lean_dec(v___y_8085_);
    crate::leanh::lean_dec_ref(v___y_8084_);
    crate::leanh::lean_dec(v___y_8083_);
    crate::leanh::lean_dec_ref(v___y_8082_);
    crate::leanh::lean_dec(v___y_8081_);
    crate::leanh::lean_dec_ref(v___y_8080_);
    crate::leanh::lean_dec(v___y_8079_);
    crate::leanh::lean_dec_ref(v___y_8077_);
    return v_res_8089_;
}
pub unsafe fn l_Lean_Meta_Grind_Action_intros___lam__1(
    mut v_generation_8090_: *mut crate::leanh::LeanObject,
    mut v___f_8091_: *mut crate::leanh::LeanObject,
    mut v___y_8092_: *mut crate::leanh::LeanObject,
    mut v___y_8093_: *mut crate::leanh::LeanObject,
    mut v___y_8094_: *mut crate::leanh::LeanObject,
    mut v___y_8095_: *mut crate::leanh::LeanObject,
    mut v___y_8096_: *mut crate::leanh::LeanObject,
    mut v___y_8097_: *mut crate::leanh::LeanObject,
    mut v___y_8098_: *mut crate::leanh::LeanObject,
    mut v___y_8099_: *mut crate::leanh::LeanObject,
    mut v___y_8100_: *mut crate::leanh::LeanObject,
    mut v___y_8101_: *mut crate::leanh::LeanObject,
    mut v___y_8102_: *mut crate::leanh::LeanObject,
    mut v___y_8103_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_8105_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8106_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8107_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8108_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_8105_ = crate::leanh::lean_unsigned_to_nat(1000000);
    v___x_8106_ = crate::leanh::lean_alloc_closure(
        l_Lean_Meta_Grind_Action_intro___boxed as *mut core::ffi::c_void,
        14,
        1,
    );
    crate::leanh::lean_closure_set(v___x_8106_, 0, v_generation_8090_);
    v___x_8107_ = crate::leanh::lean_alloc_closure(
        l_Lean_Meta_Grind_Action_loop___boxed as *mut core::ffi::c_void,
        15,
        2,
    );
    crate::leanh::lean_closure_set(v___x_8107_, 0, v___x_8105_);
    crate::leanh::lean_closure_set(v___x_8107_, 1, v___x_8106_);
    v___x_8108_ = l_Lean_Meta_Grind_Action_andThen(
        v___x_8107_,
        v___f_8091_,
        v___y_8092_,
        v___y_8093_,
        v___y_8094_,
        v___y_8095_,
        v___y_8096_,
        v___y_8097_,
        v___y_8098_,
        v___y_8099_,
        v___y_8100_,
        v___y_8101_,
        v___y_8102_,
        v___y_8103_,
    );
    return v___x_8108_;
}
pub unsafe fn l_Lean_Meta_Grind_Action_intros___lam__1___boxed(
    mut v_generation_8109_: *mut crate::leanh::LeanObject,
    mut v___f_8110_: *mut crate::leanh::LeanObject,
    mut v___y_8111_: *mut crate::leanh::LeanObject,
    mut v___y_8112_: *mut crate::leanh::LeanObject,
    mut v___y_8113_: *mut crate::leanh::LeanObject,
    mut v___y_8114_: *mut crate::leanh::LeanObject,
    mut v___y_8115_: *mut crate::leanh::LeanObject,
    mut v___y_8116_: *mut crate::leanh::LeanObject,
    mut v___y_8117_: *mut crate::leanh::LeanObject,
    mut v___y_8118_: *mut crate::leanh::LeanObject,
    mut v___y_8119_: *mut crate::leanh::LeanObject,
    mut v___y_8120_: *mut crate::leanh::LeanObject,
    mut v___y_8121_: *mut crate::leanh::LeanObject,
    mut v___y_8122_: *mut crate::leanh::LeanObject,
    mut v___y_8123_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_8124_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_8124_ = l_Lean_Meta_Grind_Action_intros___lam__1(
        v_generation_8109_,
        v___f_8110_,
        v___y_8111_,
        v___y_8112_,
        v___y_8113_,
        v___y_8114_,
        v___y_8115_,
        v___y_8116_,
        v___y_8117_,
        v___y_8118_,
        v___y_8119_,
        v___y_8120_,
        v___y_8121_,
        v___y_8122_,
    );
    crate::leanh::lean_dec(v___y_8122_);
    crate::leanh::lean_dec_ref(v___y_8121_);
    crate::leanh::lean_dec(v___y_8120_);
    crate::leanh::lean_dec_ref(v___y_8119_);
    crate::leanh::lean_dec(v___y_8118_);
    crate::leanh::lean_dec_ref(v___y_8117_);
    crate::leanh::lean_dec(v___y_8116_);
    crate::leanh::lean_dec_ref(v___y_8115_);
    crate::leanh::lean_dec(v___y_8114_);
    return v_res_8124_;
}
pub unsafe fn l_Lean_Meta_Grind_Action_intros(
    mut v_generation_8127_: *mut crate::leanh::LeanObject,
    mut v_a_8128_: *mut crate::leanh::LeanObject,
    mut v_kna_8129_: *mut crate::leanh::LeanObject,
    mut v_kp_8130_: *mut crate::leanh::LeanObject,
    mut v_a_8131_: *mut crate::leanh::LeanObject,
    mut v_a_8132_: *mut crate::leanh::LeanObject,
    mut v_a_8133_: *mut crate::leanh::LeanObject,
    mut v_a_8134_: *mut crate::leanh::LeanObject,
    mut v_a_8135_: *mut crate::leanh::LeanObject,
    mut v_a_8136_: *mut crate::leanh::LeanObject,
    mut v_a_8137_: *mut crate::leanh::LeanObject,
    mut v_a_8138_: *mut crate::leanh::LeanObject,
    mut v_a_8139_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_8141_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_8142_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8143_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8144_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_8141_ = l_Lean_Meta_Grind_Action_intros___closed__0;
    v___f_8142_ = crate::leanh::lean_alloc_closure(
        l_Lean_Meta_Grind_Action_intros___lam__1___boxed as *mut core::ffi::c_void,
        15,
        2,
    );
    crate::leanh::lean_closure_set(v___f_8142_, 0, v_generation_8127_);
    crate::leanh::lean_closure_set(v___f_8142_, 1, v___f_8141_);
    v___x_8143_ = l_Lean_Meta_Grind_Action_intros___closed__1;
    v___x_8144_ = l_Lean_Meta_Grind_Action_andThen(
        v___x_8143_,
        v___f_8142_,
        v_a_8128_,
        v_kna_8129_,
        v_kp_8130_,
        v_a_8131_,
        v_a_8132_,
        v_a_8133_,
        v_a_8134_,
        v_a_8135_,
        v_a_8136_,
        v_a_8137_,
        v_a_8138_,
        v_a_8139_,
    );
    return v___x_8144_;
}
pub unsafe fn l_Lean_Meta_Grind_Action_intros___boxed(
    mut v_generation_8145_: *mut crate::leanh::LeanObject,
    mut v_a_8146_: *mut crate::leanh::LeanObject,
    mut v_kna_8147_: *mut crate::leanh::LeanObject,
    mut v_kp_8148_: *mut crate::leanh::LeanObject,
    mut v_a_8149_: *mut crate::leanh::LeanObject,
    mut v_a_8150_: *mut crate::leanh::LeanObject,
    mut v_a_8151_: *mut crate::leanh::LeanObject,
    mut v_a_8152_: *mut crate::leanh::LeanObject,
    mut v_a_8153_: *mut crate::leanh::LeanObject,
    mut v_a_8154_: *mut crate::leanh::LeanObject,
    mut v_a_8155_: *mut crate::leanh::LeanObject,
    mut v_a_8156_: *mut crate::leanh::LeanObject,
    mut v_a_8157_: *mut crate::leanh::LeanObject,
    mut v_a_8158_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_8159_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_8159_ = l_Lean_Meta_Grind_Action_intros(
        v_generation_8145_,
        v_a_8146_,
        v_kna_8147_,
        v_kp_8148_,
        v_a_8149_,
        v_a_8150_,
        v_a_8151_,
        v_a_8152_,
        v_a_8153_,
        v_a_8154_,
        v_a_8155_,
        v_a_8156_,
        v_a_8157_,
    );
    crate::leanh::lean_dec(v_a_8157_);
    crate::leanh::lean_dec_ref(v_a_8156_);
    crate::leanh::lean_dec(v_a_8155_);
    crate::leanh::lean_dec_ref(v_a_8154_);
    crate::leanh::lean_dec(v_a_8153_);
    crate::leanh::lean_dec_ref(v_a_8152_);
    crate::leanh::lean_dec(v_a_8151_);
    crate::leanh::lean_dec_ref(v_a_8150_);
    crate::leanh::lean_dec(v_a_8149_);
    return v_res_8159_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_Action_assertAt___lam__0___closed__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_8167_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8168_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8169_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_8167_ = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_Action_assertAt___lam__0___closed__2;
    v___x_8168_ = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_Action_assertAt___lam__0___closed__1;
    v___x_8169_ = l_Lean_mkConst(v___x_8168_, v___x_8167_);
    return v___x_8169_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_Action_assertAt___lam__0(
    mut v_goal_8170_: *mut crate::leanh::LeanObject,
    mut v_prop_8171_: *mut crate::leanh::LeanObject,
    mut v_proof_8172_: *mut crate::leanh::LeanObject,
    mut v_generation_8173_: *mut crate::leanh::LeanObject,
    mut v___y_8174_: *mut crate::leanh::LeanObject,
    mut v___y_8175_: *mut crate::leanh::LeanObject,
    mut v___y_8176_: *mut crate::leanh::LeanObject,
    mut v___y_8177_: *mut crate::leanh::LeanObject,
    mut v___y_8178_: *mut crate::leanh::LeanObject,
    mut v___y_8179_: *mut crate::leanh::LeanObject,
    mut v___y_8180_: *mut crate::leanh::LeanObject,
    mut v___y_8181_: *mut crate::leanh::LeanObject,
    mut v___y_8182_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_8184_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8185_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_8186_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_expr_8187_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8188_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_8189_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8190_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8191_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8192_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8194_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_8195_: u8 = 0;
    let mut v___x_8196_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8197_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8199_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8200_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_8201_: u8 = 0;
    let mut v_unused_8202_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_8203_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8205_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_8206_: u8 = 0;
    let mut v___x_8208_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8209_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_8210_: u8 = 0;
    let mut v_a_8211_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8213_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_8214_: u8 = 0;
    let mut v___x_8216_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8217_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_8218_: u8 = 0;
    let mut v_a_8219_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8221_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_8222_: u8 = 0;
    let mut v___x_8224_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8225_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_8226_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_8184_ = lean_st_mk_ref(v_goal_8170_);
                crate::leanh::lean_inc(v___y_8182_);
                crate::leanh::lean_inc_ref(v___y_8181_);
                crate::leanh::lean_inc(v___y_8180_);
                crate::leanh::lean_inc_ref(v___y_8179_);
                crate::leanh::lean_inc(v___y_8178_);
                crate::leanh::lean_inc_ref(v___y_8177_);
                crate::leanh::lean_inc(v___y_8176_);
                crate::leanh::lean_inc_ref(v___y_8175_);
                crate::leanh::lean_inc(v___y_8174_);
                crate::leanh::lean_inc(v___x_8184_);
                crate::leanh::lean_inc_ref(v_prop_8171_);
                v___x_8185_ = lean_grind_preprocess(
                    v_prop_8171_,
                    v___x_8184_,
                    v___y_8174_,
                    v___y_8175_,
                    v___y_8176_,
                    v___y_8177_,
                    v___y_8178_,
                    v___y_8179_,
                    v___y_8180_,
                    v___y_8181_,
                    v___y_8182_,
                );
                if crate::leanh::lean_obj_tag(v___x_8185_) == 0 {
                    v_a_8186_ = crate::leanh::lean_ctor_get(v___x_8185_, 0);
                    crate::leanh::lean_inc(v_a_8186_);
                    crate::leanh::lean_dec_ref_known(v___x_8185_, 1);
                    v_expr_8187_ = crate::leanh::lean_ctor_get(v_a_8186_, 0);
                    crate::leanh::lean_inc_ref(v_expr_8187_);
                    v___x_8188_ = l_Lean_Meta_Simp_Result_getProof(
                        v_a_8186_,
                        v___y_8179_,
                        v___y_8180_,
                        v___y_8181_,
                        v___y_8182_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_8188_) == 0 {
                        v_a_8189_ = crate::leanh::lean_ctor_get(v___x_8188_, 0);
                        crate::leanh::lean_inc(v_a_8189_);
                        crate::leanh::lean_dec_ref_known(v___x_8188_, 1);
                        v___x_8190_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_Action_assertAt___lam__0___closed__3), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_Action_assertAt___lam__0___closed__3_once), _init_l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_Action_assertAt___lam__0___closed__3);
                        crate::leanh::lean_inc_ref(v_expr_8187_);
                        v___x_8191_ = l_Lean_mkApp4(
                            v___x_8190_,
                            v_prop_8171_,
                            v_expr_8187_,
                            v_a_8189_,
                            v_proof_8172_,
                        );
                        v___x_8192_ = l_Lean_Meta_Grind_add(
                            v_expr_8187_,
                            v___x_8191_,
                            v_generation_8173_,
                            v___x_8184_,
                            v___y_8174_,
                            v___y_8175_,
                            v___y_8176_,
                            v___y_8177_,
                            v___y_8178_,
                            v___y_8179_,
                            v___y_8180_,
                            v___y_8181_,
                            v___y_8182_,
                        );
                        if crate::leanh::lean_obj_tag(v___x_8192_) == 0 {
                            v_isSharedCheck_8201_ =
                                (!crate::leanh::lean_is_exclusive(v___x_8192_)) as u8;
                            if v_isSharedCheck_8201_ == 0 {
                                v_unused_8202_ = crate::leanh::lean_ctor_get(v___x_8192_, 0);
                                crate::leanh::lean_dec(v_unused_8202_);
                                v___x_8194_ = v___x_8192_;
                                v_isShared_8195_ = v_isSharedCheck_8201_;
                                state = 1;
                                continue;
                            } else {
                                crate::leanh::lean_dec(v___x_8192_);
                                v___x_8194_ = crate::leanh::lean_box(0);
                                v_isShared_8195_ = v_isSharedCheck_8201_;
                                state = 1;
                                continue;
                            }
                        } else {
                            crate::leanh::lean_dec(v___x_8184_);
                            v_a_8203_ = crate::leanh::lean_ctor_get(v___x_8192_, 0);
                            v_isSharedCheck_8210_ =
                                (!crate::leanh::lean_is_exclusive(v___x_8192_)) as u8;
                            if v_isSharedCheck_8210_ == 0 {
                                v___x_8205_ = v___x_8192_;
                                v_isShared_8206_ = v_isSharedCheck_8210_;
                                state = 3;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_8203_);
                                crate::leanh::lean_dec(v___x_8192_);
                                v___x_8205_ = crate::leanh::lean_box(0);
                                v_isShared_8206_ = v_isSharedCheck_8210_;
                                state = 3;
                                continue;
                            }
                        }
                    } else {
                        crate::leanh::lean_dec_ref(v_expr_8187_);
                        crate::leanh::lean_dec(v___x_8184_);
                        crate::leanh::lean_dec(v_generation_8173_);
                        crate::leanh::lean_dec_ref(v_proof_8172_);
                        crate::leanh::lean_dec_ref(v_prop_8171_);
                        v_a_8211_ = crate::leanh::lean_ctor_get(v___x_8188_, 0);
                        v_isSharedCheck_8218_ =
                            (!crate::leanh::lean_is_exclusive(v___x_8188_)) as u8;
                        if v_isSharedCheck_8218_ == 0 {
                            v___x_8213_ = v___x_8188_;
                            v_isShared_8214_ = v_isSharedCheck_8218_;
                            state = 5;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_8211_);
                            crate::leanh::lean_dec(v___x_8188_);
                            v___x_8213_ = crate::leanh::lean_box(0);
                            v_isShared_8214_ = v_isSharedCheck_8218_;
                            state = 5;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec(v___x_8184_);
                    crate::leanh::lean_dec(v_generation_8173_);
                    crate::leanh::lean_dec_ref(v_proof_8172_);
                    crate::leanh::lean_dec_ref(v_prop_8171_);
                    v_a_8219_ = crate::leanh::lean_ctor_get(v___x_8185_, 0);
                    v_isSharedCheck_8226_ = (!crate::leanh::lean_is_exclusive(v___x_8185_)) as u8;
                    if v_isSharedCheck_8226_ == 0 {
                        v___x_8221_ = v___x_8185_;
                        v_isShared_8222_ = v_isSharedCheck_8226_;
                        state = 7;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_8219_);
                        crate::leanh::lean_dec(v___x_8185_);
                        v___x_8221_ = crate::leanh::lean_box(0);
                        v_isShared_8222_ = v_isSharedCheck_8226_;
                        state = 7;
                        continue;
                    }
                }
            }
            1 => {
                v___x_8196_ = lean_st_ref_get(v___x_8184_);
                v___x_8197_ = lean_st_ref_get(v___x_8184_);
                crate::leanh::lean_dec(v___x_8184_);
                crate::leanh::lean_dec(v___x_8197_);
                if v_isShared_8195_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_8194_, 0, v___x_8196_);
                    v___x_8199_ = v___x_8194_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_8200_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_8200_, 0, v___x_8196_);
                    v___x_8199_ = v_reuseFailAlloc_8200_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_8199_;
            }
            3 => {
                if v_isShared_8206_ == 0 {
                    v___x_8208_ = v___x_8205_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_8209_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_8209_, 0, v_a_8203_);
                    v___x_8208_ = v_reuseFailAlloc_8209_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_8208_;
            }
            5 => {
                if v_isShared_8214_ == 0 {
                    v___x_8216_ = v___x_8213_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_8217_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_8217_, 0, v_a_8211_);
                    v___x_8216_ = v_reuseFailAlloc_8217_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_8216_;
            }
            7 => {
                if v_isShared_8222_ == 0 {
                    v___x_8224_ = v___x_8221_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_8225_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_8225_, 0, v_a_8219_);
                    v___x_8224_ = v_reuseFailAlloc_8225_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_8224_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_Action_assertAt___lam__0___boxed(
    mut v_goal_8227_: *mut crate::leanh::LeanObject,
    mut v_prop_8228_: *mut crate::leanh::LeanObject,
    mut v_proof_8229_: *mut crate::leanh::LeanObject,
    mut v_generation_8230_: *mut crate::leanh::LeanObject,
    mut v___y_8231_: *mut crate::leanh::LeanObject,
    mut v___y_8232_: *mut crate::leanh::LeanObject,
    mut v___y_8233_: *mut crate::leanh::LeanObject,
    mut v___y_8234_: *mut crate::leanh::LeanObject,
    mut v___y_8235_: *mut crate::leanh::LeanObject,
    mut v___y_8236_: *mut crate::leanh::LeanObject,
    mut v___y_8237_: *mut crate::leanh::LeanObject,
    mut v___y_8238_: *mut crate::leanh::LeanObject,
    mut v___y_8239_: *mut crate::leanh::LeanObject,
    mut v___y_8240_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_8241_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_8241_ =
        l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_Action_assertAt___lam__0(
            v_goal_8227_,
            v_prop_8228_,
            v_proof_8229_,
            v_generation_8230_,
            v___y_8231_,
            v___y_8232_,
            v___y_8233_,
            v___y_8234_,
            v___y_8235_,
            v___y_8236_,
            v___y_8237_,
            v___y_8238_,
            v___y_8239_,
        );
    crate::leanh::lean_dec(v___y_8239_);
    crate::leanh::lean_dec_ref(v___y_8238_);
    crate::leanh::lean_dec(v___y_8237_);
    crate::leanh::lean_dec_ref(v___y_8236_);
    crate::leanh::lean_dec(v___y_8235_);
    crate::leanh::lean_dec_ref(v___y_8234_);
    crate::leanh::lean_dec(v___y_8233_);
    crate::leanh::lean_dec_ref(v___y_8232_);
    crate::leanh::lean_dec(v___y_8231_);
    return v_res_8241_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_Action_assertAt___lam__1(
    mut v_mvarId_8242_: *mut crate::leanh::LeanObject,
    mut v___f_8243_: *mut crate::leanh::LeanObject,
    mut v_kp_8244_: *mut crate::leanh::LeanObject,
    mut v___y_8245_: *mut crate::leanh::LeanObject,
    mut v___y_8246_: *mut crate::leanh::LeanObject,
    mut v___y_8247_: *mut crate::leanh::LeanObject,
    mut v___y_8248_: *mut crate::leanh::LeanObject,
    mut v___y_8249_: *mut crate::leanh::LeanObject,
    mut v___y_8250_: *mut crate::leanh::LeanObject,
    mut v___y_8251_: *mut crate::leanh::LeanObject,
    mut v___y_8252_: *mut crate::leanh::LeanObject,
    mut v___y_8253_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_8255_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_8256_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8257_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_8258_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8260_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_8261_: u8 = 0;
    let mut v___x_8263_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8264_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_8265_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_8255_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__3___redArg(v_mvarId_8242_, v___f_8243_, v___y_8245_, v___y_8246_, v___y_8247_, v___y_8248_, v___y_8249_, v___y_8250_, v___y_8251_, v___y_8252_, v___y_8253_);
                if crate::leanh::lean_obj_tag(v___x_8255_) == 0 {
                    v_a_8256_ = crate::leanh::lean_ctor_get(v___x_8255_, 0);
                    crate::leanh::lean_inc(v_a_8256_);
                    crate::leanh::lean_dec_ref_known(v___x_8255_, 1);
                    crate::leanh::lean_inc(v___y_8253_);
                    crate::leanh::lean_inc_ref(v___y_8252_);
                    crate::leanh::lean_inc(v___y_8251_);
                    crate::leanh::lean_inc_ref(v___y_8250_);
                    crate::leanh::lean_inc(v___y_8249_);
                    crate::leanh::lean_inc_ref(v___y_8248_);
                    crate::leanh::lean_inc(v___y_8247_);
                    crate::leanh::lean_inc_ref(v___y_8246_);
                    crate::leanh::lean_inc(v___y_8245_);
                    v___x_8257_ = crate::leanh::lean_apply_11(
                        v_kp_8244_,
                        v_a_8256_,
                        v___y_8245_,
                        v___y_8246_,
                        v___y_8247_,
                        v___y_8248_,
                        v___y_8249_,
                        v___y_8250_,
                        v___y_8251_,
                        v___y_8252_,
                        v___y_8253_,
                        crate::leanh::lean_box(0),
                    );
                    return v___x_8257_;
                } else {
                    crate::leanh::lean_dec_ref(v_kp_8244_);
                    v_a_8258_ = crate::leanh::lean_ctor_get(v___x_8255_, 0);
                    v_isSharedCheck_8265_ = (!crate::leanh::lean_is_exclusive(v___x_8255_)) as u8;
                    if v_isSharedCheck_8265_ == 0 {
                        v___x_8260_ = v___x_8255_;
                        v_isShared_8261_ = v_isSharedCheck_8265_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_8258_);
                        crate::leanh::lean_dec(v___x_8255_);
                        v___x_8260_ = crate::leanh::lean_box(0);
                        v_isShared_8261_ = v_isSharedCheck_8265_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_8261_ == 0 {
                    v___x_8263_ = v___x_8260_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_8264_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_8264_, 0, v_a_8258_);
                    v___x_8263_ = v_reuseFailAlloc_8264_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_8263_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_Action_assertAt___lam__1___boxed(
    mut v_mvarId_8266_: *mut crate::leanh::LeanObject,
    mut v___f_8267_: *mut crate::leanh::LeanObject,
    mut v_kp_8268_: *mut crate::leanh::LeanObject,
    mut v___y_8269_: *mut crate::leanh::LeanObject,
    mut v___y_8270_: *mut crate::leanh::LeanObject,
    mut v___y_8271_: *mut crate::leanh::LeanObject,
    mut v___y_8272_: *mut crate::leanh::LeanObject,
    mut v___y_8273_: *mut crate::leanh::LeanObject,
    mut v___y_8274_: *mut crate::leanh::LeanObject,
    mut v___y_8275_: *mut crate::leanh::LeanObject,
    mut v___y_8276_: *mut crate::leanh::LeanObject,
    mut v___y_8277_: *mut crate::leanh::LeanObject,
    mut v___y_8278_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_8279_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_8279_ =
        l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_Action_assertAt___lam__1(
            v_mvarId_8266_,
            v___f_8267_,
            v_kp_8268_,
            v___y_8269_,
            v___y_8270_,
            v___y_8271_,
            v___y_8272_,
            v___y_8273_,
            v___y_8274_,
            v___y_8275_,
            v___y_8276_,
            v___y_8277_,
        );
    crate::leanh::lean_dec(v___y_8277_);
    crate::leanh::lean_dec_ref(v___y_8276_);
    crate::leanh::lean_dec(v___y_8275_);
    crate::leanh::lean_dec_ref(v___y_8274_);
    crate::leanh::lean_dec(v___y_8273_);
    crate::leanh::lean_dec_ref(v___y_8272_);
    crate::leanh::lean_dec(v___y_8271_);
    crate::leanh::lean_dec_ref(v___y_8270_);
    crate::leanh::lean_dec(v___y_8269_);
    return v_res_8279_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_Action_assertAt(
    mut v_proof_8280_: *mut crate::leanh::LeanObject,
    mut v_prop_8281_: *mut crate::leanh::LeanObject,
    mut v_generation_8282_: *mut crate::leanh::LeanObject,
    mut v_goal_8283_: *mut crate::leanh::LeanObject,
    mut v_kna_8284_: *mut crate::leanh::LeanObject,
    mut v_kp_8285_: *mut crate::leanh::LeanObject,
    mut v_a_8286_: *mut crate::leanh::LeanObject,
    mut v_a_8287_: *mut crate::leanh::LeanObject,
    mut v_a_8288_: *mut crate::leanh::LeanObject,
    mut v_a_8289_: *mut crate::leanh::LeanObject,
    mut v_a_8290_: *mut crate::leanh::LeanObject,
    mut v_a_8291_: *mut crate::leanh::LeanObject,
    mut v_a_8292_: *mut crate::leanh::LeanObject,
    mut v_a_8293_: *mut crate::leanh::LeanObject,
    mut v_a_8294_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_8296_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_8297_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8298_: u8 = 0;
    let mut v_mvarId_8299_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_8300_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_8301_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8302_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8303_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8304_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_8305_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toGoalState_8306_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mvarId_8307_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8309_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_8310_: u8 = 0;
    let mut v___x_8311_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_8312_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8314_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8315_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8316_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_8317_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8319_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_8320_: u8 = 0;
    let mut v___x_8322_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8323_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_8324_: u8 = 0;
    let mut v_isSharedCheck_8325_: u8 = 0;
    let mut v_a_8326_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8328_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_8329_: u8 = 0;
    let mut v___x_8331_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8332_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_8333_: u8 = 0;
    let mut v_a_8334_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8336_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_8337_: u8 = 0;
    let mut v___x_8339_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8340_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_8341_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_8296_ = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isEagerCasesCandidate___redArg(v_prop_8281_, v_a_8287_);
                if crate::leanh::lean_obj_tag(v___x_8296_) == 0 {
                    v_a_8297_ = crate::leanh::lean_ctor_get(v___x_8296_, 0);
                    crate::leanh::lean_inc(v_a_8297_);
                    crate::leanh::lean_dec_ref_known(v___x_8296_, 1);
                    v___x_8298_ = (crate::leanh::lean_unbox(v_a_8297_) as u8);
                    crate::leanh::lean_dec(v_a_8297_);
                    if v___x_8298_ == 0 {
                        crate::leanh::lean_dec_ref(v_kna_8284_);
                        v_mvarId_8299_ = crate::leanh::lean_ctor_get(v_goal_8283_, 1);
                        crate::leanh::lean_inc_n(v_mvarId_8299_, 2);
                        v___f_8300_ = crate::leanh::lean_alloc_closure(l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_Action_assertAt___lam__0___boxed as *mut core::ffi::c_void, 14, 4);
                        crate::leanh::lean_closure_set(v___f_8300_, 0, v_goal_8283_);
                        crate::leanh::lean_closure_set(v___f_8300_, 1, v_prop_8281_);
                        crate::leanh::lean_closure_set(v___f_8300_, 2, v_proof_8280_);
                        crate::leanh::lean_closure_set(v___f_8300_, 3, v_generation_8282_);
                        v___f_8301_ = crate::leanh::lean_alloc_closure(l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_Action_assertAt___lam__1___boxed as *mut core::ffi::c_void, 13, 3);
                        crate::leanh::lean_closure_set(v___f_8301_, 0, v_mvarId_8299_);
                        crate::leanh::lean_closure_set(v___f_8301_, 1, v___f_8300_);
                        crate::leanh::lean_closure_set(v___f_8301_, 2, v_kp_8285_);
                        v___x_8302_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__3___redArg(v_mvarId_8299_, v___f_8301_, v_a_8286_, v_a_8287_, v_a_8288_, v_a_8289_, v_a_8290_, v_a_8291_, v_a_8292_, v_a_8293_, v_a_8294_);
                        return v___x_8302_;
                    } else {
                        v___x_8303_ = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkBaseName___closed__3;
                        v___x_8304_ =
                            l_Lean_Core_mkFreshUserName(v___x_8303_, v_a_8293_, v_a_8294_);
                        if crate::leanh::lean_obj_tag(v___x_8304_) == 0 {
                            v_a_8305_ = crate::leanh::lean_ctor_get(v___x_8304_, 0);
                            crate::leanh::lean_inc(v_a_8305_);
                            crate::leanh::lean_dec_ref_known(v___x_8304_, 1);
                            v_toGoalState_8306_ = crate::leanh::lean_ctor_get(v_goal_8283_, 0);
                            v_mvarId_8307_ = crate::leanh::lean_ctor_get(v_goal_8283_, 1);
                            v_isSharedCheck_8325_ =
                                (!crate::leanh::lean_is_exclusive(v_goal_8283_)) as u8;
                            if v_isSharedCheck_8325_ == 0 {
                                v___x_8309_ = v_goal_8283_;
                                v_isShared_8310_ = v_isSharedCheck_8325_;
                                state = 1;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_mvarId_8307_);
                                crate::leanh::lean_inc(v_toGoalState_8306_);
                                crate::leanh::lean_dec(v_goal_8283_);
                                v___x_8309_ = crate::leanh::lean_box(0);
                                v_isShared_8310_ = v_isSharedCheck_8325_;
                                state = 1;
                                continue;
                            }
                        } else {
                            crate::leanh::lean_dec_ref(v_kp_8285_);
                            crate::leanh::lean_dec_ref(v_kna_8284_);
                            crate::leanh::lean_dec_ref(v_goal_8283_);
                            crate::leanh::lean_dec(v_generation_8282_);
                            crate::leanh::lean_dec_ref(v_prop_8281_);
                            crate::leanh::lean_dec_ref(v_proof_8280_);
                            v_a_8326_ = crate::leanh::lean_ctor_get(v___x_8304_, 0);
                            v_isSharedCheck_8333_ =
                                (!crate::leanh::lean_is_exclusive(v___x_8304_)) as u8;
                            if v_isSharedCheck_8333_ == 0 {
                                v___x_8328_ = v___x_8304_;
                                v_isShared_8329_ = v_isSharedCheck_8333_;
                                state = 5;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_8326_);
                                crate::leanh::lean_dec(v___x_8304_);
                                v___x_8328_ = crate::leanh::lean_box(0);
                                v_isShared_8329_ = v_isSharedCheck_8333_;
                                state = 5;
                                continue;
                            }
                        }
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_kp_8285_);
                    crate::leanh::lean_dec_ref(v_kna_8284_);
                    crate::leanh::lean_dec_ref(v_goal_8283_);
                    crate::leanh::lean_dec(v_generation_8282_);
                    crate::leanh::lean_dec_ref(v_prop_8281_);
                    crate::leanh::lean_dec_ref(v_proof_8280_);
                    v_a_8334_ = crate::leanh::lean_ctor_get(v___x_8296_, 0);
                    v_isSharedCheck_8341_ = (!crate::leanh::lean_is_exclusive(v___x_8296_)) as u8;
                    if v_isSharedCheck_8341_ == 0 {
                        v___x_8336_ = v___x_8296_;
                        v_isShared_8337_ = v_isSharedCheck_8341_;
                        state = 7;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_8334_);
                        crate::leanh::lean_dec(v___x_8296_);
                        v___x_8336_ = crate::leanh::lean_box(0);
                        v_isShared_8337_ = v_isSharedCheck_8341_;
                        state = 7;
                        continue;
                    }
                }
            }
            1 => {
                v___x_8311_ = l_Lean_MVarId_assert(
                    v_mvarId_8307_,
                    v_a_8305_,
                    v_prop_8281_,
                    v_proof_8280_,
                    v_a_8291_,
                    v_a_8292_,
                    v_a_8293_,
                    v_a_8294_,
                );
                if crate::leanh::lean_obj_tag(v___x_8311_) == 0 {
                    v_a_8312_ = crate::leanh::lean_ctor_get(v___x_8311_, 0);
                    crate::leanh::lean_inc(v_a_8312_);
                    crate::leanh::lean_dec_ref_known(v___x_8311_, 1);
                    if v_isShared_8310_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_8309_, 1, v_a_8312_);
                        v___x_8314_ = v___x_8309_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_8316_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_8316_, 0, v_toGoalState_8306_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_8316_, 1, v_a_8312_);
                        v___x_8314_ = v_reuseFailAlloc_8316_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_8309_);
                    crate::leanh::lean_dec_ref(v_toGoalState_8306_);
                    crate::leanh::lean_dec_ref(v_kp_8285_);
                    crate::leanh::lean_dec_ref(v_kna_8284_);
                    crate::leanh::lean_dec(v_generation_8282_);
                    v_a_8317_ = crate::leanh::lean_ctor_get(v___x_8311_, 0);
                    v_isSharedCheck_8324_ = (!crate::leanh::lean_is_exclusive(v___x_8311_)) as u8;
                    if v_isSharedCheck_8324_ == 0 {
                        v___x_8319_ = v___x_8311_;
                        v_isShared_8320_ = v_isSharedCheck_8324_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_8317_);
                        crate::leanh::lean_dec(v___x_8311_);
                        v___x_8319_ = crate::leanh::lean_box(0);
                        v_isShared_8320_ = v_isSharedCheck_8324_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                v___x_8315_ = l_Lean_Meta_Grind_Action_intros(
                    v_generation_8282_,
                    v___x_8314_,
                    v_kna_8284_,
                    v_kp_8285_,
                    v_a_8286_,
                    v_a_8287_,
                    v_a_8288_,
                    v_a_8289_,
                    v_a_8290_,
                    v_a_8291_,
                    v_a_8292_,
                    v_a_8293_,
                    v_a_8294_,
                );
                return v___x_8315_;
            }
            3 => {
                if v_isShared_8320_ == 0 {
                    v___x_8322_ = v___x_8319_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_8323_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_8323_, 0, v_a_8317_);
                    v___x_8322_ = v_reuseFailAlloc_8323_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_8322_;
            }
            5 => {
                if v_isShared_8329_ == 0 {
                    v___x_8331_ = v___x_8328_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_8332_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_8332_, 0, v_a_8326_);
                    v___x_8331_ = v_reuseFailAlloc_8332_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_8331_;
            }
            7 => {
                if v_isShared_8337_ == 0 {
                    v___x_8339_ = v___x_8336_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_8340_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_8340_, 0, v_a_8334_);
                    v___x_8339_ = v_reuseFailAlloc_8340_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_8339_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_Action_assertAt___boxed(
    mut v_proof_8342_: *mut crate::leanh::LeanObject,
    mut v_prop_8343_: *mut crate::leanh::LeanObject,
    mut v_generation_8344_: *mut crate::leanh::LeanObject,
    mut v_goal_8345_: *mut crate::leanh::LeanObject,
    mut v_kna_8346_: *mut crate::leanh::LeanObject,
    mut v_kp_8347_: *mut crate::leanh::LeanObject,
    mut v_a_8348_: *mut crate::leanh::LeanObject,
    mut v_a_8349_: *mut crate::leanh::LeanObject,
    mut v_a_8350_: *mut crate::leanh::LeanObject,
    mut v_a_8351_: *mut crate::leanh::LeanObject,
    mut v_a_8352_: *mut crate::leanh::LeanObject,
    mut v_a_8353_: *mut crate::leanh::LeanObject,
    mut v_a_8354_: *mut crate::leanh::LeanObject,
    mut v_a_8355_: *mut crate::leanh::LeanObject,
    mut v_a_8356_: *mut crate::leanh::LeanObject,
    mut v_a_8357_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_8358_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_8358_ = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_Action_assertAt(
        v_proof_8342_,
        v_prop_8343_,
        v_generation_8344_,
        v_goal_8345_,
        v_kna_8346_,
        v_kp_8347_,
        v_a_8348_,
        v_a_8349_,
        v_a_8350_,
        v_a_8351_,
        v_a_8352_,
        v_a_8353_,
        v_a_8354_,
        v_a_8355_,
        v_a_8356_,
    );
    crate::leanh::lean_dec(v_a_8356_);
    crate::leanh::lean_dec_ref(v_a_8355_);
    crate::leanh::lean_dec(v_a_8354_);
    crate::leanh::lean_dec_ref(v_a_8353_);
    crate::leanh::lean_dec(v_a_8352_);
    crate::leanh::lean_dec_ref(v_a_8351_);
    crate::leanh::lean_dec(v_a_8350_);
    crate::leanh::lean_dec_ref(v_a_8349_);
    crate::leanh::lean_dec(v_a_8348_);
    return v_res_8358_;
}
pub unsafe fn l_Lean_Meta_Grind_Action_assertNext(
    mut v_goal_8359_: *mut crate::leanh::LeanObject,
    mut v_kna_8360_: *mut crate::leanh::LeanObject,
    mut v_kp_8361_: *mut crate::leanh::LeanObject,
    mut v_a_8362_: *mut crate::leanh::LeanObject,
    mut v_a_8363_: *mut crate::leanh::LeanObject,
    mut v_a_8364_: *mut crate::leanh::LeanObject,
    mut v_a_8365_: *mut crate::leanh::LeanObject,
    mut v_a_8366_: *mut crate::leanh::LeanObject,
    mut v_a_8367_: *mut crate::leanh::LeanObject,
    mut v_a_8368_: *mut crate::leanh::LeanObject,
    mut v_a_8369_: *mut crate::leanh::LeanObject,
    mut v_a_8370_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toGoalState_8372_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_inconsistent_8373_: u8 = 0;
    let mut v_mvarId_8374_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextDeclIdx_8375_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_enodeMap_8376_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_exprs_8377_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_parents_8378_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_congrTable_8379_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_appMap_8380_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_indicesFound_8381_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_newFacts_8382_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextIdx_8383_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_newRawFacts_8384_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_facts_8385_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_extThms_8386_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ematch_8387_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_inj_8388_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_split_8389_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_clean_8390_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sstates_8391_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8393_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_8394_: u8 = 0;
    let mut v___x_8395_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8397_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_8398_: u8 = 0;
    let mut v_val_8399_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_8400_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_8401_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_proof_8402_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_prop_8403_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_generation_8404_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_splitSource_8405_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ematchDiagSource_8406_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_simp_8407_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_simpMethods_8408_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_config_8409_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_anchorRefs_x3f_8410_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_cheapCases_8411_: u8 = 0;
    let mut v_reportMVarIssue_8412_: u8 = 0;
    let mut v_symPrios_8413_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_extensions_8414_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_debug_8415_: u8 = 0;
    let mut v_ematchDiag_8416_: u8 = 0;
    let mut v___x_8418_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_goal_8420_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8421_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8422_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8423_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8424_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_8425_: u8 = 0;
    let mut v_unused_8426_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_8427_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8428_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_8429_: u8 = 0;
    let mut v___x_8430_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8431_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_toGoalState_8372_ = crate::leanh::lean_ctor_get(v_goal_8359_, 0);
                crate::leanh::lean_inc_ref(v_toGoalState_8372_);
                v_inconsistent_8373_ = crate::leanh::lean_ctor_get_uint8(
                    v_toGoalState_8372_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 17) as u32,
                );
                if v_inconsistent_8373_ == 0 {
                    v_mvarId_8374_ = crate::leanh::lean_ctor_get(v_goal_8359_, 1);
                    v_nextDeclIdx_8375_ = crate::leanh::lean_ctor_get(v_toGoalState_8372_, 0);
                    v_enodeMap_8376_ = crate::leanh::lean_ctor_get(v_toGoalState_8372_, 1);
                    v_exprs_8377_ = crate::leanh::lean_ctor_get(v_toGoalState_8372_, 2);
                    v_parents_8378_ = crate::leanh::lean_ctor_get(v_toGoalState_8372_, 3);
                    v_congrTable_8379_ = crate::leanh::lean_ctor_get(v_toGoalState_8372_, 4);
                    v_appMap_8380_ = crate::leanh::lean_ctor_get(v_toGoalState_8372_, 5);
                    v_indicesFound_8381_ = crate::leanh::lean_ctor_get(v_toGoalState_8372_, 6);
                    v_newFacts_8382_ = crate::leanh::lean_ctor_get(v_toGoalState_8372_, 7);
                    v_nextIdx_8383_ = crate::leanh::lean_ctor_get(v_toGoalState_8372_, 8);
                    v_newRawFacts_8384_ = crate::leanh::lean_ctor_get(v_toGoalState_8372_, 9);
                    v_facts_8385_ = crate::leanh::lean_ctor_get(v_toGoalState_8372_, 10);
                    v_extThms_8386_ = crate::leanh::lean_ctor_get(v_toGoalState_8372_, 11);
                    v_ematch_8387_ = crate::leanh::lean_ctor_get(v_toGoalState_8372_, 12);
                    v_inj_8388_ = crate::leanh::lean_ctor_get(v_toGoalState_8372_, 13);
                    v_split_8389_ = crate::leanh::lean_ctor_get(v_toGoalState_8372_, 14);
                    v_clean_8390_ = crate::leanh::lean_ctor_get(v_toGoalState_8372_, 15);
                    v_sstates_8391_ = crate::leanh::lean_ctor_get(v_toGoalState_8372_, 16);
                    v_isSharedCheck_8429_ =
                        (!crate::leanh::lean_is_exclusive(v_toGoalState_8372_)) as u8;
                    if v_isSharedCheck_8429_ == 0 {
                        v___x_8393_ = v_toGoalState_8372_;
                        v_isShared_8394_ = v_isSharedCheck_8429_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_sstates_8391_);
                        crate::leanh::lean_inc(v_clean_8390_);
                        crate::leanh::lean_inc(v_split_8389_);
                        crate::leanh::lean_inc(v_inj_8388_);
                        crate::leanh::lean_inc(v_ematch_8387_);
                        crate::leanh::lean_inc(v_extThms_8386_);
                        crate::leanh::lean_inc(v_facts_8385_);
                        crate::leanh::lean_inc(v_newRawFacts_8384_);
                        crate::leanh::lean_inc(v_nextIdx_8383_);
                        crate::leanh::lean_inc(v_newFacts_8382_);
                        crate::leanh::lean_inc(v_indicesFound_8381_);
                        crate::leanh::lean_inc(v_appMap_8380_);
                        crate::leanh::lean_inc(v_congrTable_8379_);
                        crate::leanh::lean_inc(v_parents_8378_);
                        crate::leanh::lean_inc(v_exprs_8377_);
                        crate::leanh::lean_inc(v_enodeMap_8376_);
                        crate::leanh::lean_inc(v_nextDeclIdx_8375_);
                        crate::leanh::lean_dec(v_toGoalState_8372_);
                        v___x_8393_ = crate::leanh::lean_box(0);
                        v_isShared_8394_ = v_isSharedCheck_8429_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_toGoalState_8372_);
                    crate::leanh::lean_dec_ref(v_kp_8361_);
                    crate::leanh::lean_dec_ref(v_kna_8360_);
                    crate::leanh::lean_dec_ref(v_goal_8359_);
                    v___x_8430_ = l_Lean_Meta_Grind_Action_intro___closed__0;
                    v___x_8431_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_8431_, 0, v___x_8430_);
                    return v___x_8431_;
                }
            }
            1 => {
                v___x_8395_ = l_Std_Queue_dequeue_x3f___redArg(v_newRawFacts_8384_);
                if crate::leanh::lean_obj_tag(v___x_8395_) == 1 {
                    crate::leanh::lean_inc(v_mvarId_8374_);
                    v_isSharedCheck_8425_ = (!crate::leanh::lean_is_exclusive(v_goal_8359_)) as u8;
                    if v_isSharedCheck_8425_ == 0 {
                        v_unused_8426_ = crate::leanh::lean_ctor_get(v_goal_8359_, 1);
                        crate::leanh::lean_dec(v_unused_8426_);
                        v_unused_8427_ = crate::leanh::lean_ctor_get(v_goal_8359_, 0);
                        crate::leanh::lean_dec(v_unused_8427_);
                        v___x_8397_ = v_goal_8359_;
                        v_isShared_8398_ = v_isSharedCheck_8425_;
                        state = 2;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v_goal_8359_);
                        v___x_8397_ = crate::leanh::lean_box(0);
                        v_isShared_8398_ = v_isSharedCheck_8425_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v___x_8395_);
                    crate::leanh::lean_del_object(v___x_8393_);
                    crate::leanh::lean_dec_ref(v_sstates_8391_);
                    crate::leanh::lean_dec_ref(v_clean_8390_);
                    crate::leanh::lean_dec_ref(v_split_8389_);
                    crate::leanh::lean_dec_ref(v_inj_8388_);
                    crate::leanh::lean_dec_ref(v_ematch_8387_);
                    crate::leanh::lean_dec_ref(v_extThms_8386_);
                    crate::leanh::lean_dec_ref(v_facts_8385_);
                    crate::leanh::lean_dec(v_nextIdx_8383_);
                    crate::leanh::lean_dec_ref(v_newFacts_8382_);
                    crate::leanh::lean_dec_ref(v_indicesFound_8381_);
                    crate::leanh::lean_dec_ref(v_appMap_8380_);
                    crate::leanh::lean_dec_ref(v_congrTable_8379_);
                    crate::leanh::lean_dec_ref(v_parents_8378_);
                    crate::leanh::lean_dec_ref(v_exprs_8377_);
                    crate::leanh::lean_dec_ref(v_enodeMap_8376_);
                    crate::leanh::lean_dec(v_nextDeclIdx_8375_);
                    crate::leanh::lean_dec_ref(v_kp_8361_);
                    crate::leanh::lean_inc(v_a_8370_);
                    crate::leanh::lean_inc_ref(v_a_8369_);
                    crate::leanh::lean_inc(v_a_8368_);
                    crate::leanh::lean_inc_ref(v_a_8367_);
                    crate::leanh::lean_inc(v_a_8366_);
                    crate::leanh::lean_inc_ref(v_a_8365_);
                    crate::leanh::lean_inc(v_a_8364_);
                    crate::leanh::lean_inc_ref(v_a_8363_);
                    crate::leanh::lean_inc(v_a_8362_);
                    v___x_8428_ = crate::leanh::lean_apply_11(
                        v_kna_8360_,
                        v_goal_8359_,
                        v_a_8362_,
                        v_a_8363_,
                        v_a_8364_,
                        v_a_8365_,
                        v_a_8366_,
                        v_a_8367_,
                        v_a_8368_,
                        v_a_8369_,
                        v_a_8370_,
                        crate::leanh::lean_box(0),
                    );
                    return v___x_8428_;
                }
            }
            2 => {
                v_val_8399_ = crate::leanh::lean_ctor_get(v___x_8395_, 0);
                crate::leanh::lean_inc(v_val_8399_);
                crate::leanh::lean_dec_ref_known(v___x_8395_, 1);
                v_fst_8400_ = crate::leanh::lean_ctor_get(v_val_8399_, 0);
                crate::leanh::lean_inc(v_fst_8400_);
                v_snd_8401_ = crate::leanh::lean_ctor_get(v_val_8399_, 1);
                crate::leanh::lean_inc(v_snd_8401_);
                crate::leanh::lean_dec(v_val_8399_);
                v_proof_8402_ = crate::leanh::lean_ctor_get(v_fst_8400_, 0);
                crate::leanh::lean_inc_ref(v_proof_8402_);
                v_prop_8403_ = crate::leanh::lean_ctor_get(v_fst_8400_, 1);
                crate::leanh::lean_inc_ref(v_prop_8403_);
                v_generation_8404_ = crate::leanh::lean_ctor_get(v_fst_8400_, 2);
                crate::leanh::lean_inc(v_generation_8404_);
                v_splitSource_8405_ = crate::leanh::lean_ctor_get(v_fst_8400_, 3);
                crate::leanh::lean_inc(v_splitSource_8405_);
                v_ematchDiagSource_8406_ = crate::leanh::lean_ctor_get(v_fst_8400_, 4);
                crate::leanh::lean_inc(v_ematchDiagSource_8406_);
                crate::leanh::lean_dec(v_fst_8400_);
                v_simp_8407_ = crate::leanh::lean_ctor_get(v_a_8363_, 0);
                v_simpMethods_8408_ = crate::leanh::lean_ctor_get(v_a_8363_, 1);
                v_config_8409_ = crate::leanh::lean_ctor_get(v_a_8363_, 2);
                v_anchorRefs_x3f_8410_ = crate::leanh::lean_ctor_get(v_a_8363_, 3);
                v_cheapCases_8411_ = crate::leanh::lean_ctor_get_uint8(
                    v_a_8363_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 8) as u32,
                );
                v_reportMVarIssue_8412_ = crate::leanh::lean_ctor_get_uint8(
                    v_a_8363_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 8 + 1) as u32,
                );
                v_symPrios_8413_ = crate::leanh::lean_ctor_get(v_a_8363_, 6);
                v_extensions_8414_ = crate::leanh::lean_ctor_get(v_a_8363_, 7);
                v_debug_8415_ = crate::leanh::lean_ctor_get_uint8(
                    v_a_8363_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 8 + 2) as u32,
                );
                v_ematchDiag_8416_ = crate::leanh::lean_ctor_get_uint8(
                    v_a_8363_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 8 + 3) as u32,
                );
                if v_isShared_8394_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_8393_, 9, v_snd_8401_);
                    v___x_8418_ = v___x_8393_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_8424_ = crate::leanh::lean_alloc_ctor(0, 17, (1) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_8424_, 0, v_nextDeclIdx_8375_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_8424_, 1, v_enodeMap_8376_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_8424_, 2, v_exprs_8377_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_8424_, 3, v_parents_8378_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_8424_, 4, v_congrTable_8379_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_8424_, 5, v_appMap_8380_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_8424_, 6, v_indicesFound_8381_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_8424_, 7, v_newFacts_8382_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_8424_, 8, v_nextIdx_8383_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_8424_, 9, v_snd_8401_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_8424_, 10, v_facts_8385_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_8424_, 11, v_extThms_8386_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_8424_, 12, v_ematch_8387_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_8424_, 13, v_inj_8388_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_8424_, 14, v_split_8389_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_8424_, 15, v_clean_8390_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_8424_, 16, v_sstates_8391_);
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_8424_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 17) as u32,
                        v_inconsistent_8373_,
                    );
                    v___x_8418_ = v_reuseFailAlloc_8424_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_8398_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_8397_, 0, v___x_8418_);
                    v_goal_8420_ = v___x_8397_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_8423_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_8423_, 0, v___x_8418_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_8423_, 1, v_mvarId_8374_);
                    v_goal_8420_ = v_reuseFailAlloc_8423_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                crate::leanh::lean_inc_ref(v_extensions_8414_);
                crate::leanh::lean_inc_ref(v_symPrios_8413_);
                crate::leanh::lean_inc(v_anchorRefs_x3f_8410_);
                crate::leanh::lean_inc_ref(v_config_8409_);
                crate::leanh::lean_inc_ref(v_simpMethods_8408_);
                crate::leanh::lean_inc_ref(v_simp_8407_);
                v___x_8421_ = crate::leanh::lean_alloc_ctor(0, 8, (4) as u32);
                crate::leanh::lean_ctor_set(v___x_8421_, 0, v_simp_8407_);
                crate::leanh::lean_ctor_set(v___x_8421_, 1, v_simpMethods_8408_);
                crate::leanh::lean_ctor_set(v___x_8421_, 2, v_config_8409_);
                crate::leanh::lean_ctor_set(v___x_8421_, 3, v_anchorRefs_x3f_8410_);
                crate::leanh::lean_ctor_set(v___x_8421_, 4, v_splitSource_8405_);
                crate::leanh::lean_ctor_set(v___x_8421_, 5, v_ematchDiagSource_8406_);
                crate::leanh::lean_ctor_set(v___x_8421_, 6, v_symPrios_8413_);
                crate::leanh::lean_ctor_set(v___x_8421_, 7, v_extensions_8414_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_8421_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 8) as u32,
                    v_cheapCases_8411_,
                );
                crate::leanh::lean_ctor_set_uint8(
                    v___x_8421_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 8 + 1) as u32,
                    v_reportMVarIssue_8412_,
                );
                crate::leanh::lean_ctor_set_uint8(
                    v___x_8421_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 8 + 2) as u32,
                    v_debug_8415_,
                );
                crate::leanh::lean_ctor_set_uint8(
                    v___x_8421_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 8 + 3) as u32,
                    v_ematchDiag_8416_,
                );
                v___x_8422_ =
                    l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_Action_assertAt(
                        v_proof_8402_,
                        v_prop_8403_,
                        v_generation_8404_,
                        v_goal_8420_,
                        v_kna_8360_,
                        v_kp_8361_,
                        v_a_8362_,
                        v___x_8421_,
                        v_a_8364_,
                        v_a_8365_,
                        v_a_8366_,
                        v_a_8367_,
                        v_a_8368_,
                        v_a_8369_,
                        v_a_8370_,
                    );
                crate::leanh::lean_dec_ref_known(v___x_8421_, 8);
                return v___x_8422_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Grind_Action_assertNext___boxed(
    mut v_goal_8432_: *mut crate::leanh::LeanObject,
    mut v_kna_8433_: *mut crate::leanh::LeanObject,
    mut v_kp_8434_: *mut crate::leanh::LeanObject,
    mut v_a_8435_: *mut crate::leanh::LeanObject,
    mut v_a_8436_: *mut crate::leanh::LeanObject,
    mut v_a_8437_: *mut crate::leanh::LeanObject,
    mut v_a_8438_: *mut crate::leanh::LeanObject,
    mut v_a_8439_: *mut crate::leanh::LeanObject,
    mut v_a_8440_: *mut crate::leanh::LeanObject,
    mut v_a_8441_: *mut crate::leanh::LeanObject,
    mut v_a_8442_: *mut crate::leanh::LeanObject,
    mut v_a_8443_: *mut crate::leanh::LeanObject,
    mut v_a_8444_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_8445_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_8445_ = l_Lean_Meta_Grind_Action_assertNext(
        v_goal_8432_,
        v_kna_8433_,
        v_kp_8434_,
        v_a_8435_,
        v_a_8436_,
        v_a_8437_,
        v_a_8438_,
        v_a_8439_,
        v_a_8440_,
        v_a_8441_,
        v_a_8442_,
        v_a_8443_,
    );
    crate::leanh::lean_dec(v_a_8443_);
    crate::leanh::lean_dec_ref(v_a_8442_);
    crate::leanh::lean_dec(v_a_8441_);
    crate::leanh::lean_dec_ref(v_a_8440_);
    crate::leanh::lean_dec(v_a_8439_);
    crate::leanh::lean_dec_ref(v_a_8438_);
    crate::leanh::lean_dec(v_a_8437_);
    crate::leanh::lean_dec_ref(v_a_8436_);
    crate::leanh::lean_dec(v_a_8435_);
    return v_res_8445_;
}
pub unsafe fn l_Lean_Meta_Grind_Action_assertAll___redArg(
    mut v_a_8446_: *mut crate::leanh::LeanObject,
    mut v_kp_8447_: *mut crate::leanh::LeanObject,
    mut v_a_8448_: *mut crate::leanh::LeanObject,
    mut v_a_8449_: *mut crate::leanh::LeanObject,
    mut v_a_8450_: *mut crate::leanh::LeanObject,
    mut v_a_8451_: *mut crate::leanh::LeanObject,
    mut v_a_8452_: *mut crate::leanh::LeanObject,
    mut v_a_8453_: *mut crate::leanh::LeanObject,
    mut v_a_8454_: *mut crate::leanh::LeanObject,
    mut v_a_8455_: *mut crate::leanh::LeanObject,
    mut v_a_8456_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_8458_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8459_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8460_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_8458_ = crate::leanh::lean_unsigned_to_nat(1000000);
    v___x_8459_ = crate::leanh::lean_alloc_closure(
        l_Lean_Meta_Grind_Action_assertNext___boxed as *mut core::ffi::c_void,
        13,
        0,
    );
    v___x_8460_ = l_Lean_Meta_Grind_Action_loop___redArg(
        v___x_8458_,
        v___x_8459_,
        v_a_8446_,
        v_kp_8447_,
        v_a_8448_,
        v_a_8449_,
        v_a_8450_,
        v_a_8451_,
        v_a_8452_,
        v_a_8453_,
        v_a_8454_,
        v_a_8455_,
        v_a_8456_,
    );
    return v___x_8460_;
}
pub unsafe fn l_Lean_Meta_Grind_Action_assertAll___redArg___boxed(
    mut v_a_8461_: *mut crate::leanh::LeanObject,
    mut v_kp_8462_: *mut crate::leanh::LeanObject,
    mut v_a_8463_: *mut crate::leanh::LeanObject,
    mut v_a_8464_: *mut crate::leanh::LeanObject,
    mut v_a_8465_: *mut crate::leanh::LeanObject,
    mut v_a_8466_: *mut crate::leanh::LeanObject,
    mut v_a_8467_: *mut crate::leanh::LeanObject,
    mut v_a_8468_: *mut crate::leanh::LeanObject,
    mut v_a_8469_: *mut crate::leanh::LeanObject,
    mut v_a_8470_: *mut crate::leanh::LeanObject,
    mut v_a_8471_: *mut crate::leanh::LeanObject,
    mut v_a_8472_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_8473_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_8473_ = l_Lean_Meta_Grind_Action_assertAll___redArg(
        v_a_8461_, v_kp_8462_, v_a_8463_, v_a_8464_, v_a_8465_, v_a_8466_, v_a_8467_, v_a_8468_,
        v_a_8469_, v_a_8470_, v_a_8471_,
    );
    crate::leanh::lean_dec(v_a_8471_);
    crate::leanh::lean_dec_ref(v_a_8470_);
    crate::leanh::lean_dec(v_a_8469_);
    crate::leanh::lean_dec_ref(v_a_8468_);
    crate::leanh::lean_dec(v_a_8467_);
    crate::leanh::lean_dec_ref(v_a_8466_);
    crate::leanh::lean_dec(v_a_8465_);
    crate::leanh::lean_dec_ref(v_a_8464_);
    crate::leanh::lean_dec(v_a_8463_);
    return v_res_8473_;
}
pub unsafe fn l_Lean_Meta_Grind_Action_assertAll(
    mut v_a_8474_: *mut crate::leanh::LeanObject,
    mut v_kna_8475_: *mut crate::leanh::LeanObject,
    mut v_kp_8476_: *mut crate::leanh::LeanObject,
    mut v_a_8477_: *mut crate::leanh::LeanObject,
    mut v_a_8478_: *mut crate::leanh::LeanObject,
    mut v_a_8479_: *mut crate::leanh::LeanObject,
    mut v_a_8480_: *mut crate::leanh::LeanObject,
    mut v_a_8481_: *mut crate::leanh::LeanObject,
    mut v_a_8482_: *mut crate::leanh::LeanObject,
    mut v_a_8483_: *mut crate::leanh::LeanObject,
    mut v_a_8484_: *mut crate::leanh::LeanObject,
    mut v_a_8485_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_8487_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_8487_ = l_Lean_Meta_Grind_Action_assertAll___redArg(
        v_a_8474_, v_kp_8476_, v_a_8477_, v_a_8478_, v_a_8479_, v_a_8480_, v_a_8481_, v_a_8482_,
        v_a_8483_, v_a_8484_, v_a_8485_,
    );
    return v___x_8487_;
}
pub unsafe fn l_Lean_Meta_Grind_Action_assertAll___boxed(
    mut v_a_8488_: *mut crate::leanh::LeanObject,
    mut v_kna_8489_: *mut crate::leanh::LeanObject,
    mut v_kp_8490_: *mut crate::leanh::LeanObject,
    mut v_a_8491_: *mut crate::leanh::LeanObject,
    mut v_a_8492_: *mut crate::leanh::LeanObject,
    mut v_a_8493_: *mut crate::leanh::LeanObject,
    mut v_a_8494_: *mut crate::leanh::LeanObject,
    mut v_a_8495_: *mut crate::leanh::LeanObject,
    mut v_a_8496_: *mut crate::leanh::LeanObject,
    mut v_a_8497_: *mut crate::leanh::LeanObject,
    mut v_a_8498_: *mut crate::leanh::LeanObject,
    mut v_a_8499_: *mut crate::leanh::LeanObject,
    mut v_a_8500_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_8501_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_8501_ = l_Lean_Meta_Grind_Action_assertAll(
        v_a_8488_,
        v_kna_8489_,
        v_kp_8490_,
        v_a_8491_,
        v_a_8492_,
        v_a_8493_,
        v_a_8494_,
        v_a_8495_,
        v_a_8496_,
        v_a_8497_,
        v_a_8498_,
        v_a_8499_,
    );
    crate::leanh::lean_dec(v_a_8499_);
    crate::leanh::lean_dec_ref(v_a_8498_);
    crate::leanh::lean_dec(v_a_8497_);
    crate::leanh::lean_dec_ref(v_a_8496_);
    crate::leanh::lean_dec(v_a_8495_);
    crate::leanh::lean_dec_ref(v_a_8494_);
    crate::leanh::lean_dec(v_a_8493_);
    crate::leanh::lean_dec_ref(v_a_8492_);
    crate::leanh::lean_dec(v_a_8491_);
    crate::leanh::lean_dec_ref(v_kna_8489_);
    return v_res_8501_;
}
pub unsafe fn l_Lean_Meta_Grind_Solvers_mkAction___lam__0(
    mut v___y_8502_: *mut crate::leanh::LeanObject,
    mut v___y_8503_: *mut crate::leanh::LeanObject,
    mut v___y_8504_: *mut crate::leanh::LeanObject,
    mut v___y_8505_: *mut crate::leanh::LeanObject,
    mut v___y_8506_: *mut crate::leanh::LeanObject,
    mut v___y_8507_: *mut crate::leanh::LeanObject,
    mut v___y_8508_: *mut crate::leanh::LeanObject,
    mut v___y_8509_: *mut crate::leanh::LeanObject,
    mut v___y_8510_: *mut crate::leanh::LeanObject,
    mut v___y_8511_: *mut crate::leanh::LeanObject,
    mut v___y_8512_: *mut crate::leanh::LeanObject,
    mut v___y_8513_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_8515_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_8515_ = l_Lean_Meta_Grind_Action_assertAll___redArg(
        v___y_8502_,
        v___y_8504_,
        v___y_8505_,
        v___y_8506_,
        v___y_8507_,
        v___y_8508_,
        v___y_8509_,
        v___y_8510_,
        v___y_8511_,
        v___y_8512_,
        v___y_8513_,
    );
    return v___x_8515_;
}
pub unsafe fn l_Lean_Meta_Grind_Solvers_mkAction___lam__0___boxed(
    mut v___y_8516_: *mut crate::leanh::LeanObject,
    mut v___y_8517_: *mut crate::leanh::LeanObject,
    mut v___y_8518_: *mut crate::leanh::LeanObject,
    mut v___y_8519_: *mut crate::leanh::LeanObject,
    mut v___y_8520_: *mut crate::leanh::LeanObject,
    mut v___y_8521_: *mut crate::leanh::LeanObject,
    mut v___y_8522_: *mut crate::leanh::LeanObject,
    mut v___y_8523_: *mut crate::leanh::LeanObject,
    mut v___y_8524_: *mut crate::leanh::LeanObject,
    mut v___y_8525_: *mut crate::leanh::LeanObject,
    mut v___y_8526_: *mut crate::leanh::LeanObject,
    mut v___y_8527_: *mut crate::leanh::LeanObject,
    mut v___y_8528_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_8529_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_8529_ = l_Lean_Meta_Grind_Solvers_mkAction___lam__0(
        v___y_8516_,
        v___y_8517_,
        v___y_8518_,
        v___y_8519_,
        v___y_8520_,
        v___y_8521_,
        v___y_8522_,
        v___y_8523_,
        v___y_8524_,
        v___y_8525_,
        v___y_8526_,
        v___y_8527_,
    );
    crate::leanh::lean_dec(v___y_8527_);
    crate::leanh::lean_dec_ref(v___y_8526_);
    crate::leanh::lean_dec(v___y_8525_);
    crate::leanh::lean_dec_ref(v___y_8524_);
    crate::leanh::lean_dec(v___y_8523_);
    crate::leanh::lean_dec_ref(v___y_8522_);
    crate::leanh::lean_dec(v___y_8521_);
    crate::leanh::lean_dec_ref(v___y_8520_);
    crate::leanh::lean_dec(v___y_8519_);
    crate::leanh::lean_dec_ref(v___y_8517_);
    return v_res_8529_;
}
pub unsafe fn l_Lean_Meta_Grind_Solvers_mkAction___lam__1(
    mut v_a_8530_: *mut crate::leanh::LeanObject,
    mut v___f_8531_: *mut crate::leanh::LeanObject,
    mut v___y_8532_: *mut crate::leanh::LeanObject,
    mut v___y_8533_: *mut crate::leanh::LeanObject,
    mut v___y_8534_: *mut crate::leanh::LeanObject,
    mut v___y_8535_: *mut crate::leanh::LeanObject,
    mut v___y_8536_: *mut crate::leanh::LeanObject,
    mut v___y_8537_: *mut crate::leanh::LeanObject,
    mut v___y_8538_: *mut crate::leanh::LeanObject,
    mut v___y_8539_: *mut crate::leanh::LeanObject,
    mut v___y_8540_: *mut crate::leanh::LeanObject,
    mut v___y_8541_: *mut crate::leanh::LeanObject,
    mut v___y_8542_: *mut crate::leanh::LeanObject,
    mut v___y_8543_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_8545_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_8545_ = l_Lean_Meta_Grind_Action_andThen(
        v_a_8530_,
        v___f_8531_,
        v___y_8532_,
        v___y_8533_,
        v___y_8534_,
        v___y_8535_,
        v___y_8536_,
        v___y_8537_,
        v___y_8538_,
        v___y_8539_,
        v___y_8540_,
        v___y_8541_,
        v___y_8542_,
        v___y_8543_,
    );
    return v___x_8545_;
}
pub unsafe fn l_Lean_Meta_Grind_Solvers_mkAction___lam__1___boxed(
    mut v_a_8546_: *mut crate::leanh::LeanObject,
    mut v___f_8547_: *mut crate::leanh::LeanObject,
    mut v___y_8548_: *mut crate::leanh::LeanObject,
    mut v___y_8549_: *mut crate::leanh::LeanObject,
    mut v___y_8550_: *mut crate::leanh::LeanObject,
    mut v___y_8551_: *mut crate::leanh::LeanObject,
    mut v___y_8552_: *mut crate::leanh::LeanObject,
    mut v___y_8553_: *mut crate::leanh::LeanObject,
    mut v___y_8554_: *mut crate::leanh::LeanObject,
    mut v___y_8555_: *mut crate::leanh::LeanObject,
    mut v___y_8556_: *mut crate::leanh::LeanObject,
    mut v___y_8557_: *mut crate::leanh::LeanObject,
    mut v___y_8558_: *mut crate::leanh::LeanObject,
    mut v___y_8559_: *mut crate::leanh::LeanObject,
    mut v___y_8560_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_8561_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_8561_ = l_Lean_Meta_Grind_Solvers_mkAction___lam__1(
        v_a_8546_,
        v___f_8547_,
        v___y_8548_,
        v___y_8549_,
        v___y_8550_,
        v___y_8551_,
        v___y_8552_,
        v___y_8553_,
        v___y_8554_,
        v___y_8555_,
        v___y_8556_,
        v___y_8557_,
        v___y_8558_,
        v___y_8559_,
    );
    crate::leanh::lean_dec(v___y_8559_);
    crate::leanh::lean_dec_ref(v___y_8558_);
    crate::leanh::lean_dec(v___y_8557_);
    crate::leanh::lean_dec_ref(v___y_8556_);
    crate::leanh::lean_dec(v___y_8555_);
    crate::leanh::lean_dec_ref(v___y_8554_);
    crate::leanh::lean_dec(v___y_8553_);
    crate::leanh::lean_dec_ref(v___y_8552_);
    crate::leanh::lean_dec(v___y_8551_);
    return v_res_8561_;
}
pub unsafe fn l_Lean_Meta_Grind_Solvers_mkAction() -> *mut crate::leanh::LeanObject {
    let mut v___x_8564_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_8565_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8567_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_8568_: u8 = 0;
    let mut v___f_8569_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_8570_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8572_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8573_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_8574_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_8564_ = l_Lean_Meta_Grind_Solvers_mkActionCore();
                if crate::leanh::lean_obj_tag(v___x_8564_) == 0 {
                    v_a_8565_ = crate::leanh::lean_ctor_get(v___x_8564_, 0);
                    v_isSharedCheck_8574_ = (!crate::leanh::lean_is_exclusive(v___x_8564_)) as u8;
                    if v_isSharedCheck_8574_ == 0 {
                        v___x_8567_ = v___x_8564_;
                        v_isShared_8568_ = v_isSharedCheck_8574_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_8565_);
                        crate::leanh::lean_dec(v___x_8564_);
                        v___x_8567_ = crate::leanh::lean_box(0);
                        v_isShared_8568_ = v_isSharedCheck_8574_;
                        state = 1;
                        continue;
                    }
                } else {
                    return v___x_8564_;
                }
            }
            1 => {
                v___f_8569_ = l_Lean_Meta_Grind_Solvers_mkAction___closed__0;
                v___f_8570_ = crate::leanh::lean_alloc_closure(
                    l_Lean_Meta_Grind_Solvers_mkAction___lam__1___boxed as *mut core::ffi::c_void,
                    15,
                    2,
                );
                crate::leanh::lean_closure_set(v___f_8570_, 0, v_a_8565_);
                crate::leanh::lean_closure_set(v___f_8570_, 1, v___f_8569_);
                if v_isShared_8568_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_8567_, 0, v___f_8570_);
                    v___x_8572_ = v___x_8567_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_8573_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_8573_, 0, v___f_8570_);
                    v___x_8572_ = v_reuseFailAlloc_8573_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_8572_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Grind_Solvers_mkAction___boxed(
    mut v_a_8575_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_8576_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_8576_ = l_Lean_Meta_Grind_Solvers_mkAction();
    return v_res_8576_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Meta_Tactic_Grind_Intro(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Grind_Lemmas(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Grind_Action(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Apply(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Grind_Util(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Grind_CasesMatch(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Grind_Injection(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Grind_Core(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Grind_RevertAll(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Grind_Util(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    l_Lean_Meta_Grind_instInhabitedIntroResult_default =
        _init_l_Lean_Meta_Grind_instInhabitedIntroResult_default();
    crate::leanh::lean_mark_persistent(l_Lean_Meta_Grind_instInhabitedIntroResult_default);
    l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_instInhabitedIntroResult =
        _init_l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_instInhabitedIntroResult(
        );
    crate::leanh::lean_mark_persistent(
        l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_instInhabitedIntroResult,
    );
    l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_Action_hugeNumber =
        _init_l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_Action_hugeNumber();
    crate::leanh::lean_mark_persistent(
        l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_Action_hugeNumber,
    );
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Meta_Tactic_Grind_Intro(
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
pub unsafe fn initialize_Lean_Meta_Tactic_Grind_Intro(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_Grind_Lemmas(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Meta_Tactic_Grind_Action(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Meta_Tactic_Apply(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Meta_Tactic_Grind_Util(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Meta_Tactic_Grind_CasesMatch(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Meta_Tactic_Grind_Injection(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Meta_Tactic_Grind_Core(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Meta_Tactic_Grind_RevertAll(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Grind_Util(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Grind_Intro(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Meta_Tactic_Grind_Intro(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Lean_Meta_Tactic_Grind_Intro(builtin);
}
