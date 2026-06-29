// Lean compiler output
// Module: Lean.Meta.Tactic.Grind.CasesMatch
// Imports: Lean.Meta.Tactic.Util Lean.Meta.Tactic.Grind.Util Lean.Meta.Match.MatcherApp Lean.Meta.Tactic.Cases
use crate::r#gen::Init::Control::StateRef::l_StateRefT_x27_instMonad___redArg;
use crate::r#gen::Init::Data::Array::Subarray::l_Array_toSubarray___redArg;
use crate::r#gen::Init::Data::List::Basic::l_List_reverse___redArg;
use crate::r#gen::Init::Data::Slice::Array::Iterator::l_Subarray_copy___redArg;
use crate::r#gen::Init::Prelude::{
    l_Array_extract___redArg, l_Lean_Name_num___override, l_Lean_replaceRef,
    l_List_lengthTR___redArg, l_ReaderT_instApplicativeOfMonad___redArg___lam__1,
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
use crate::r#gen::Lean::Data::Name::{l_Lean_Name_getPrefix, l_Lean_Name_isAnonymous};
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
    l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux, l_Lean_Expr_app___override,
    l_Lean_Expr_appFnCleanup___redArg, l_Lean_Expr_cleanupAnnotations,
    l_Lean_Expr_forallE___override, l_Lean_Expr_getAppFn, l_Lean_Expr_getAppNumArgs,
    l_Lean_Expr_hasLooseBVars, l_Lean_Expr_isApp, l_Lean_Expr_isConstOf, l_Lean_Expr_isFalse,
    l_Lean_Expr_isForall, l_Lean_Expr_mvarId_x21, l_Lean_Expr_sort___override,
    l_Lean_instBEqBinderInfo_beq, l_Lean_instBEqMVarId_beq, l_Lean_instHashableMVarId_hash,
    l_Lean_instInhabitedExpr, l_Lean_mkAppN, l_Lean_mkConst, l_Lean_mkSort,
};
use crate::r#gen::Lean::Level::l_Lean_Level_ofNat;
use crate::r#gen::Lean::Message::{
    l_Lean_MessageData_note, l_Lean_MessageData_ofConstName, l_Lean_MessageData_ofName,
    l_Lean_indentExpr, l_Lean_stringToMessageData,
};
use crate::r#gen::Lean::Meta::Basic::{
    l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAux,
    l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp,
    l_Lean_Meta_forallMetaBoundedTelescope, l_Lean_Meta_instMonadMetaM___lam__0___boxed,
    l_Lean_Meta_instMonadMetaM___lam__1___boxed, l_Lean_Meta_mkForallFVars,
    l_Lean_Meta_mkLambdaFVars,
};
use crate::r#gen::Lean::Meta::InferType::l_Lean_Meta_getLevel;
use crate::r#gen::Lean::Meta::Match::MatcherApp::{
    initialize_Lean_Meta_Match_MatcherApp, runtime_initialize_Lean_Meta_Match_MatcherApp,
};
use crate::r#gen::Lean::Meta::Match::MatcherInfo::{
    l_Lean_Meta_Match_Extension_getMatcherInfo_x3f, l_Lean_Meta_Match_MatcherInfo_arity,
    l_Lean_Meta_Match_MatcherInfo_getMotivePos, l_Lean_Meta_Match_MatcherInfo_numAlts,
    l_Lean_Meta_Match_instInhabitedAltParamInfo_default,
};
use crate::r#gen::Lean::Meta::Tactic::Cases::{
    initialize_Lean_Meta_Tactic_Cases, l_Lean_Meta_withNewEqs___redArg,
    runtime_initialize_Lean_Meta_Tactic_Cases,
};
use crate::r#gen::Lean::Meta::Tactic::Grind::Util::{
    initialize_Lean_Meta_Tactic_Grind_Util, l_Lean_Meta_Grind_markAsPreMatchCond,
    runtime_initialize_Lean_Meta_Tactic_Grind_Util,
};
use crate::r#gen::Lean::Meta::Tactic::Util::{
    initialize_Lean_Meta_Tactic_Util, l_Lean_MVarId_getTag, l_Lean_MVarId_getType,
    l_Lean_MVarId_setTag___redArg, l_Lean_Meta_throwTacticEx___redArg,
    runtime_initialize_Lean_Meta_Tactic_Util,
};
use crate::r#gen::Lean::PrivateName::l_Lean_isPrivateName;
use crate::ffi::{
    lean_array_size, lean_array_uget_borrowed, lean_array_uset, lean_mk_array,
};
use crate::ffi::{lean_array_fset, lean_array_set};
use crate::ffi::{
    lean_uint64_to_usize, lean_usize_land, lean_usize_mul, lean_usize_shift_left,
    lean_usize_shift_right,
};
use crate::ffi::{
    lean_usize_add, lean_usize_dec_le, lean_usize_dec_lt, lean_usize_sub, lean_usize_to_nat,
};
use crate::ffi::{
    lean_array_fget, lean_array_fget_borrowed, lean_array_get, lean_array_get_borrowed,
    lean_array_get_size, lean_array_mk, lean_array_push, lean_array_to_list,
    lean_mk_empty_array_with_capacity, lean_nat_add, lean_nat_dec_eq, lean_nat_dec_le,
    lean_nat_dec_lt, lean_nat_sub, lean_panic_fn_borrowed, lean_usize_dec_eq,
};
use crate::ffi::{
    lean_st_ref_get, lean_st_ref_set, lean_st_ref_take,
};
use crate::ffi::lean_ptr_addr;
use crate::ffi::lean_expr_has_loose_bvar;
use crate::ffi::lean_infer_type;
use crate::ffi::lean_get_match_equations_for;
pub static l___private_Lean_Meta_Tactic_Grind_CasesMatch_0__Lean_Meta_Grind_isMatchCondCandidate_go___closed__0_value: crate::leanh::LeanStringObject<3> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [69, 113, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_CasesMatch_0__Lean_Meta_Grind_isMatchCondCandidate_go___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_CasesMatch_0__Lean_Meta_Grind_isMatchCondCandidate_go___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_CasesMatch_0__Lean_Meta_Grind_isMatchCondCandidate_go___closed__1_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_CasesMatch_0__Lean_Meta_Grind_isMatchCondCandidate_go___closed__0_value) as *mut crate::leanh::LeanObject,16122875713692181903 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_CasesMatch_0__Lean_Meta_Grind_isMatchCondCandidate_go___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_CasesMatch_0__Lean_Meta_Grind_isMatchCondCandidate_go___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_CasesMatch_0__Lean_Meta_Grind_isMatchCondCandidate_go___closed__2_value: crate::leanh::LeanStringObject<4> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [72, 69, 113, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_CasesMatch_0__Lean_Meta_Grind_isMatchCondCandidate_go___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_CasesMatch_0__Lean_Meta_Grind_isMatchCondCandidate_go___closed__2_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_CasesMatch_0__Lean_Meta_Grind_isMatchCondCandidate_go___closed__3_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_CasesMatch_0__Lean_Meta_Grind_isMatchCondCandidate_go___closed__2_value) as *mut crate::leanh::LeanObject,13589827700912665667 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_CasesMatch_0__Lean_Meta_Grind_isMatchCondCandidate_go___closed__3: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_CasesMatch_0__Lean_Meta_Grind_isMatchCondCandidate_go___closed__3_value) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Meta_Tactic_Grind_CasesMatch_0__Lean_Meta_Grind_casesMatch_mkMotiveAndRefls___closed__0_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_CasesMatch_0__Lean_Meta_Grind_casesMatch_mkMotiveAndRefls___closed__0: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_Tactic_Grind_CasesMatch_0__Lean_Meta_Grind_casesMatch_mkMotiveAndRefls___closed__1_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_CasesMatch_0__Lean_Meta_Grind_casesMatch_mkMotiveAndRefls___closed__1: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Meta_Grind_casesMatch_spec__0_spec__0_spec__2_spec__7_spec__10_spec__12_spec__15___redArg___closed__0_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Meta_Grind_casesMatch_spec__0_spec__0_spec__2_spec__7_spec__10_spec__12_spec__15___redArg___closed__0: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Meta_Grind_casesMatch_spec__0_spec__0_spec__2_spec__7_spec__10_spec__12_spec__15___redArg___closed__1_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Meta_Grind_casesMatch_spec__0_spec__0_spec__2_spec__7_spec__10_spec__12_spec__15___redArg___closed__1: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Meta_Grind_casesMatch_spec__0_spec__0_spec__2_spec__7_spec__10_spec__12_spec__15___redArg___closed__2_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Meta_Grind_casesMatch_spec__0_spec__0_spec__2_spec__7_spec__10_spec__12_spec__15___redArg___closed__2: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Meta_Grind_casesMatch_spec__0_spec__0_spec__2_spec__7_spec__10_spec__12_spec__15___redArg___closed__3_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Meta_Grind_casesMatch_spec__0_spec__0_spec__2_spec__7_spec__10_spec__12_spec__15___redArg___closed__3: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Meta_Grind_casesMatch_spec__0_spec__0_spec__2_spec__7_spec__10_spec__12_spec__15___redArg___closed__4_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Meta_Grind_casesMatch_spec__0_spec__0_spec__2_spec__7_spec__10_spec__12_spec__15___redArg___closed__4: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Meta_Grind_casesMatch_spec__0_spec__0_spec__2_spec__7_spec__10_spec__12_spec__15___redArg___closed__5_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Meta_Grind_casesMatch_spec__0_spec__0_spec__2_spec__7_spec__10_spec__12_spec__15___redArg___closed__5: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Meta_Grind_casesMatch_spec__0_spec__0_spec__2_spec__7_spec__10_spec__12_spec__15___redArg___closed__6_value: crate::leanh::LeanStringObject<24> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 24, m_capacity: 24, m_length: 23, m_data: [65, 32, 112, 114, 105, 118, 97, 116, 101, 32, 100, 101, 99, 108, 97, 114, 97, 116, 105, 111, 110, 32, 96, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Meta_Grind_casesMatch_spec__0_spec__0_spec__2_spec__7_spec__10_spec__12_spec__15___redArg___closed__6: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Meta_Grind_casesMatch_spec__0_spec__0_spec__2_spec__7_spec__10_spec__12_spec__15___redArg___closed__6_value) as *mut crate::leanh::LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Meta_Grind_casesMatch_spec__0_spec__0_spec__2_spec__7_spec__10_spec__12_spec__15___redArg___closed__7_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Meta_Grind_casesMatch_spec__0_spec__0_spec__2_spec__7_spec__10_spec__12_spec__15___redArg___closed__7: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Meta_Grind_casesMatch_spec__0_spec__0_spec__2_spec__7_spec__10_spec__12_spec__15___redArg___closed__8_value: crate::leanh::LeanStringObject<79> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 79, m_capacity: 79, m_length: 78, m_data: [96, 32, 40, 102, 114, 111, 109, 32, 116, 104, 101, 32, 99, 117, 114, 114, 101, 110, 116, 32, 109, 111, 100, 117, 108, 101, 41, 32, 101, 120, 105, 115, 116, 115, 32, 98, 117, 116, 32, 119, 111, 117, 108, 100, 32, 110, 101, 101, 100, 32, 116, 111, 32, 98, 101, 32, 112, 117, 98, 108, 105, 99, 32, 116, 111, 32, 97, 99, 99, 101, 115, 115, 32, 104, 101, 114, 101, 46, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Meta_Grind_casesMatch_spec__0_spec__0_spec__2_spec__7_spec__10_spec__12_spec__15___redArg___closed__8: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Meta_Grind_casesMatch_spec__0_spec__0_spec__2_spec__7_spec__10_spec__12_spec__15___redArg___closed__8_value) as *mut crate::leanh::LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Meta_Grind_casesMatch_spec__0_spec__0_spec__2_spec__7_spec__10_spec__12_spec__15___redArg___closed__9_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Meta_Grind_casesMatch_spec__0_spec__0_spec__2_spec__7_spec__10_spec__12_spec__15___redArg___closed__9: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Meta_Grind_casesMatch_spec__0_spec__0_spec__2_spec__7_spec__10_spec__12_spec__15___redArg___closed__10_value: crate::leanh::LeanStringObject<23> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 23, m_capacity: 23, m_length: 22, m_data: [65, 32, 112, 117, 98, 108, 105, 99, 32, 100, 101, 99, 108, 97, 114, 97, 116, 105, 111, 110, 32, 96, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Meta_Grind_casesMatch_spec__0_spec__0_spec__2_spec__7_spec__10_spec__12_spec__15___redArg___closed__10: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Meta_Grind_casesMatch_spec__0_spec__0_spec__2_spec__7_spec__10_spec__12_spec__15___redArg___closed__10_value) as *mut crate::leanh::LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Meta_Grind_casesMatch_spec__0_spec__0_spec__2_spec__7_spec__10_spec__12_spec__15___redArg___closed__11_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Meta_Grind_casesMatch_spec__0_spec__0_spec__2_spec__7_spec__10_spec__12_spec__15___redArg___closed__11: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Meta_Grind_casesMatch_spec__0_spec__0_spec__2_spec__7_spec__10_spec__12_spec__15___redArg___closed__12_value: crate::leanh::LeanStringObject<68> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 68, m_capacity: 68, m_length: 67, m_data: [96, 32, 101, 120, 105, 115, 116, 115, 32, 98, 117, 116, 32, 105, 115, 32, 105, 109, 112, 111, 114, 116, 101, 100, 32, 112, 114, 105, 118, 97, 116, 101, 108, 121, 59, 32, 99, 111, 110, 115, 105, 100, 101, 114, 32, 97, 100, 100, 105, 110, 103, 32, 96, 112, 117, 98, 108, 105, 99, 32, 105, 109, 112, 111, 114, 116, 32, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Meta_Grind_casesMatch_spec__0_spec__0_spec__2_spec__7_spec__10_spec__12_spec__15___redArg___closed__12: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Meta_Grind_casesMatch_spec__0_spec__0_spec__2_spec__7_spec__10_spec__12_spec__15___redArg___closed__12_value) as *mut crate::leanh::LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Meta_Grind_casesMatch_spec__0_spec__0_spec__2_spec__7_spec__10_spec__12_spec__15___redArg___closed__13_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Meta_Grind_casesMatch_spec__0_spec__0_spec__2_spec__7_spec__10_spec__12_spec__15___redArg___closed__13: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Meta_Grind_casesMatch_spec__0_spec__0_spec__2_spec__7_spec__10_spec__12_spec__15___redArg___closed__14_value: crate::leanh::LeanStringObject<3> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [96, 46, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Meta_Grind_casesMatch_spec__0_spec__0_spec__2_spec__7_spec__10_spec__12_spec__15___redArg___closed__14: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Meta_Grind_casesMatch_spec__0_spec__0_spec__2_spec__7_spec__10_spec__12_spec__15___redArg___closed__14_value) as *mut crate::leanh::LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Meta_Grind_casesMatch_spec__0_spec__0_spec__2_spec__7_spec__10_spec__12_spec__15___redArg___closed__15_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Meta_Grind_casesMatch_spec__0_spec__0_spec__2_spec__7_spec__10_spec__12_spec__15___redArg___closed__15: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Meta_Grind_casesMatch_spec__0_spec__0_spec__2_spec__7_spec__10_spec__12_spec__15___redArg___closed__16_value: crate::leanh::LeanStringObject<10> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [96, 32, 40, 102, 114, 111, 109, 32, 96, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Meta_Grind_casesMatch_spec__0_spec__0_spec__2_spec__7_spec__10_spec__12_spec__15___redArg___closed__16: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Meta_Grind_casesMatch_spec__0_spec__0_spec__2_spec__7_spec__10_spec__12_spec__15___redArg___closed__16_value) as *mut crate::leanh::LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Meta_Grind_casesMatch_spec__0_spec__0_spec__2_spec__7_spec__10_spec__12_spec__15___redArg___closed__17_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Meta_Grind_casesMatch_spec__0_spec__0_spec__2_spec__7_spec__10_spec__12_spec__15___redArg___closed__17: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Meta_Grind_casesMatch_spec__0_spec__0_spec__2_spec__7_spec__10_spec__12_spec__15___redArg___closed__18_value: crate::leanh::LeanStringObject<54> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 54, m_capacity: 54, m_length: 53, m_data: [96, 41, 32, 101, 120, 105, 115, 116, 115, 32, 98, 117, 116, 32, 119, 111, 117, 108, 100, 32, 110, 101, 101, 100, 32, 116, 111, 32, 98, 101, 32, 112, 117, 98, 108, 105, 99, 32, 116, 111, 32, 97, 99, 99, 101, 115, 115, 32, 104, 101, 114, 101, 46, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Meta_Grind_casesMatch_spec__0_spec__0_spec__2_spec__7_spec__10_spec__12_spec__15___redArg___closed__18: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Meta_Grind_casesMatch_spec__0_spec__0_spec__2_spec__7_spec__10_spec__12_spec__15___redArg___closed__18_value) as *mut crate::leanh::LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Meta_Grind_casesMatch_spec__0_spec__0_spec__2_spec__7_spec__10_spec__12_spec__15___redArg___closed__19_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Meta_Grind_casesMatch_spec__0_spec__0_spec__2_spec__7_spec__10_spec__12_spec__15___redArg___closed__19: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Meta_Grind_casesMatch_spec__0_spec__0_spec__2_spec__7___redArg___closed__0_value: crate::leanh::LeanStringObject<19> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 19, m_capacity: 19, m_length: 18, m_data: [85, 110, 107, 110, 111, 119, 110, 32, 99, 111, 110, 115, 116, 97, 110, 116, 32, 96, 0]};
static mut l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Meta_Grind_casesMatch_spec__0_spec__0_spec__2_spec__7___redArg___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Meta_Grind_casesMatch_spec__0_spec__0_spec__2_spec__7___redArg___closed__0_value) as *mut crate::leanh::LeanObject;
static mut l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Meta_Grind_casesMatch_spec__0_spec__0_spec__2_spec__7___redArg___closed__1_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Meta_Grind_casesMatch_spec__0_spec__0_spec__2_spec__7___redArg___closed__1: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Meta_Grind_casesMatch_spec__0_spec__0_spec__2_spec__7___redArg___closed__2_value: crate::leanh::LeanStringObject<2> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [96, 0]};
static mut l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Meta_Grind_casesMatch_spec__0_spec__0_spec__2_spec__7___redArg___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Meta_Grind_casesMatch_spec__0_spec__0_spec__2_spec__7___redArg___closed__2_value) as *mut crate::leanh::LeanObject;
static mut l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Meta_Grind_casesMatch_spec__0_spec__0_spec__2_spec__7___redArg___closed__3_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Meta_Grind_casesMatch_spec__0_spec__0_spec__2_spec__7___redArg___closed__3: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_panic___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Meta_Grind_casesMatch_spec__0_spec__1___closed__0_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_panic___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Meta_Grind_casesMatch_spec__0_spec__1___closed__0: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_panic___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Meta_Grind_casesMatch_spec__0_spec__1___closed__1_value: crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Core_instMonadCoreM___lam__0___boxed as *const core::ffi::c_void, m_arity: 5, m_num_fixed: 0, m_objs: [] };
static mut l_panic___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Meta_Grind_casesMatch_spec__0_spec__1___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_panic___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Meta_Grind_casesMatch_spec__0_spec__1___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l_panic___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Meta_Grind_casesMatch_spec__0_spec__1___closed__2_value: crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Core_instMonadCoreM___lam__1___boxed as *const core::ffi::c_void, m_arity: 7, m_num_fixed: 0, m_objs: [] };
static mut l_panic___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Meta_Grind_casesMatch_spec__0_spec__1___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_panic___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Meta_Grind_casesMatch_spec__0_spec__1___closed__2_value) as *mut crate::leanh::LeanObject;
pub static l_panic___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Meta_Grind_casesMatch_spec__0_spec__1___closed__3_value: crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Meta_instMonadMetaM___lam__0___boxed as *const core::ffi::c_void, m_arity: 7, m_num_fixed: 0, m_objs: [] };
static mut l_panic___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Meta_Grind_casesMatch_spec__0_spec__1___closed__3: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_panic___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Meta_Grind_casesMatch_spec__0_spec__1___closed__3_value) as *mut crate::leanh::LeanObject;
pub static l_panic___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Meta_Grind_casesMatch_spec__0_spec__1___closed__4_value: crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Meta_instMonadMetaM___lam__1___boxed as *const core::ffi::c_void, m_arity: 9, m_num_fixed: 0, m_objs: [] };
static mut l_panic___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Meta_Grind_casesMatch_spec__0_spec__1___closed__4: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_panic___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Meta_Grind_casesMatch_spec__0_spec__1___closed__4_value) as *mut crate::leanh::LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Meta_Grind_casesMatch_spec__0_spec__3___closed__0_value: crate::leanh::LeanStringObject<33> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 33, m_capacity: 33, m_length: 32, m_data: [76, 101, 97, 110, 46, 77, 101, 116, 97, 46, 77, 97, 116, 99, 104, 46, 77, 97, 116, 99, 104, 101, 114, 65, 112, 112, 46, 66, 97, 115, 105, 99, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Meta_Grind_casesMatch_spec__0_spec__3___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Meta_Grind_casesMatch_spec__0_spec__3___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Meta_Grind_casesMatch_spec__0_spec__3___closed__1_value: crate::leanh::LeanStringObject<27> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 27, m_capacity: 27, m_length: 26, m_data: [76, 101, 97, 110, 46, 77, 101, 116, 97, 46, 109, 97, 116, 99, 104, 77, 97, 116, 99, 104, 101, 114, 65, 112, 112, 63, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Meta_Grind_casesMatch_spec__0_spec__3___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Meta_Grind_casesMatch_spec__0_spec__3___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Meta_Grind_casesMatch_spec__0_spec__3___closed__2_value: crate::leanh::LeanStringObject<21> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 21, m_capacity: 21, m_length: 20, m_data: [101, 120, 112, 101, 99, 116, 101, 100, 32, 99, 111, 110, 115, 116, 114, 117, 99, 116, 111, 114, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Meta_Grind_casesMatch_spec__0_spec__3___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Meta_Grind_casesMatch_spec__0_spec__3___closed__2_value) as *mut crate::leanh::LeanObject;
static mut l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Meta_Grind_casesMatch_spec__0_spec__3___closed__3_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Meta_Grind_casesMatch_spec__0_spec__3___closed__3: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Meta_matchMatcherApp_x3f___at___00Lean_Meta_Grind_casesMatch_spec__0___closed__0_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Meta_matchMatcherApp_x3f___at___00Lean_Meta_Grind_casesMatch_spec__0___closed__0: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Meta_matchMatcherApp_x3f___at___00Lean_Meta_Grind_casesMatch_spec__0___closed__1_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Meta_matchMatcherApp_x3f___at___00Lean_Meta_Grind_casesMatch_spec__0___closed__1: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Meta_matchMatcherApp_x3f___at___00Lean_Meta_Grind_casesMatch_spec__0___closed__2_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Meta_matchMatcherApp_x3f___at___00Lean_Meta_Grind_casesMatch_spec__0___closed__2: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Meta_matchMatcherApp_x3f___at___00Lean_Meta_Grind_casesMatch_spec__0___closed__3_value: crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l_Lean_Meta_matchMatcherApp_x3f___at___00Lean_Meta_Grind_casesMatch_spec__0___closed__3: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_Meta_matchMatcherApp_x3f___at___00Lean_Meta_Grind_casesMatch_spec__0___closed__3_value) as *mut crate::leanh::LeanObject;
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_casesMatch_spec__1_spec__5_spec__8___redArg___closed__0_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_casesMatch_spec__1_spec__5_spec__8___redArg___closed__0: usize = 0;
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_casesMatch_spec__1_spec__5_spec__8___redArg___closed__1_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_casesMatch_spec__1_spec__5_spec__8___redArg___closed__1: usize = 0;
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_casesMatch_spec__1_spec__5_spec__8___redArg___closed__2_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_casesMatch_spec__1_spec__5_spec__8___redArg___closed__2: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Meta_Grind_casesMatch___lam__0___closed__0_value: crate::leanh::LeanStringObject<
    6,
> = crate::leanh::LeanStringObject {
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
static mut l_Lean_Meta_Grind_casesMatch___lam__0___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_casesMatch___lam__0___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Grind_casesMatch___lam__0___closed__1_value: crate::leanh::LeanStringObject<
    11,
> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 11,
    m_capacity: 11,
    m_length: 10,
    m_data: [99, 97, 115, 101, 115, 77, 97, 116, 99, 104, 0],
};
static mut l_Lean_Meta_Grind_casesMatch___lam__0___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_casesMatch___lam__0___closed__1_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Meta_Grind_casesMatch___lam__0___closed__2_value_aux_0: crate::leanh::LeanCtorObject<
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
        core::ptr::addr_of!(l_Lean_Meta_Grind_casesMatch___lam__0___closed__0_value)
            as *mut crate::leanh::LeanObject,
        15947788021050471391 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Lean_Meta_Grind_casesMatch___lam__0___closed__2_value: crate::leanh::LeanCtorObject<
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
        core::ptr::addr_of!(l_Lean_Meta_Grind_casesMatch___lam__0___closed__2_value_aux_0)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_Grind_casesMatch___lam__0___closed__1_value)
            as *mut crate::leanh::LeanObject,
        10880498660615990170 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_Grind_casesMatch___lam__0___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_casesMatch___lam__0___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Grind_casesMatch___lam__0___closed__3_value: crate::leanh::LeanStringObject<
    28,
> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 28,
    m_capacity: 28,
    m_length: 27,
    m_data: [
        96, 109, 97, 116, 99, 104, 96, 45, 101, 120, 112, 114, 101, 115, 115, 105, 111, 110, 32,
        101, 120, 112, 101, 99, 116, 101, 100, 0,
    ],
};
static mut l_Lean_Meta_Grind_casesMatch___lam__0___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_casesMatch___lam__0___closed__3_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Meta_Grind_casesMatch___lam__0___closed__4_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Grind_casesMatch___lam__0___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_CasesMatch_0__Lean_Meta_Grind_isMatchCondCandidate_go(
    mut v_e_1691_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v_binderType_1692_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_body_1693_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_lhs_1695_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1696_: u8 = 0;
    let mut v___x_1698_: u8 = 0;
    let mut v___x_1700_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1701_: u8 = 0;
    let mut v___x_1703_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1704_: u8 = 0;
    let mut v___x_1705_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1706_: u8 = 0;
    let mut v_arg_1707_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1708_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1709_: u8 = 0;
    let mut v_arg_1710_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1711_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1712_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1713_: u8 = 0;
    let mut v___x_1714_: u8 = 0;
    let mut v___x_1715_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1716_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1717_: u8 = 0;
    let mut v___x_1718_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_e_1691_) == 7 {
                    v_binderType_1692_ = crate::leanh::lean_ctor_get(v_e_1691_, 1);
                    crate::leanh::lean_inc_ref(v_binderType_1692_);
                    v_body_1693_ = crate::leanh::lean_ctor_get(v_e_1691_, 2);
                    crate::leanh::lean_inc_ref(v_body_1693_);
                    crate::leanh::lean_dec_ref_known(v_e_1691_, 3);
                    v___x_1703_ = l_Lean_Expr_cleanupAnnotations(v_binderType_1692_);
                    v___x_1704_ = l_Lean_Expr_isApp(v___x_1703_);
                    if v___x_1704_ == 0 {
                        crate::leanh::lean_dec_ref(v___x_1703_);
                        state = 2;
                        continue;
                    } else {
                        v___x_1705_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1703_);
                        v___x_1706_ = l_Lean_Expr_isApp(v___x_1705_);
                        if v___x_1706_ == 0 {
                            crate::leanh::lean_dec_ref(v___x_1705_);
                            state = 2;
                            continue;
                        } else {
                            v_arg_1707_ = crate::leanh::lean_ctor_get(v___x_1705_, 1);
                            crate::leanh::lean_inc_ref(v_arg_1707_);
                            v___x_1708_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1705_);
                            v___x_1709_ = l_Lean_Expr_isApp(v___x_1708_);
                            if v___x_1709_ == 0 {
                                crate::leanh::lean_dec_ref(v___x_1708_);
                                crate::leanh::lean_dec_ref(v_arg_1707_);
                                state = 2;
                                continue;
                            } else {
                                v_arg_1710_ = crate::leanh::lean_ctor_get(v___x_1708_, 1);
                                crate::leanh::lean_inc_ref(v_arg_1710_);
                                v___x_1711_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1708_);
                                v___x_1712_ = l___private_Lean_Meta_Tactic_Grind_CasesMatch_0__Lean_Meta_Grind_isMatchCondCandidate_go___closed__1;
                                v___x_1713_ = l_Lean_Expr_isConstOf(v___x_1711_, v___x_1712_);
                                if v___x_1713_ == 0 {
                                    crate::leanh::lean_dec_ref(v_arg_1707_);
                                    v___x_1714_ = l_Lean_Expr_isApp(v___x_1711_);
                                    if v___x_1714_ == 0 {
                                        crate::leanh::lean_dec_ref(v___x_1711_);
                                        crate::leanh::lean_dec_ref(v_arg_1710_);
                                        state = 2;
                                        continue;
                                    } else {
                                        v___x_1715_ =
                                            l_Lean_Expr_appFnCleanup___redArg(v___x_1711_);
                                        v___x_1716_ = l___private_Lean_Meta_Tactic_Grind_CasesMatch_0__Lean_Meta_Grind_isMatchCondCandidate_go___closed__3;
                                        v___x_1717_ =
                                            l_Lean_Expr_isConstOf(v___x_1715_, v___x_1716_);
                                        crate::leanh::lean_dec_ref(v___x_1715_);
                                        if v___x_1717_ == 0 {
                                            crate::leanh::lean_dec_ref(v_arg_1710_);
                                            state = 2;
                                            continue;
                                        } else {
                                            v_lhs_1695_ = v_arg_1710_;
                                            state = 1;
                                            continue;
                                        }
                                    }
                                } else {
                                    crate::leanh::lean_dec_ref(v___x_1711_);
                                    crate::leanh::lean_dec_ref(v_arg_1710_);
                                    v_lhs_1695_ = v_arg_1707_;
                                    state = 1;
                                    continue;
                                }
                            }
                        }
                    }
                } else {
                    v___x_1718_ = l_Lean_Expr_isFalse(v_e_1691_);
                    return v___x_1718_;
                }
            }
            1 => {
                v___x_1696_ = l_Lean_Expr_hasLooseBVars(v_lhs_1695_);
                crate::leanh::lean_dec_ref(v_lhs_1695_);
                if v___x_1696_ == 0 {
                    v_e_1691_ = v_body_1693_;
                    state = 0;
                    continue;
                } else {
                    crate::leanh::lean_dec_ref(v_body_1693_);
                    v___x_1698_ = 0;
                    return v___x_1698_;
                }
            }
            2 => {
                v___x_1700_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_1701_ = lean_expr_has_loose_bvar(v_body_1693_, v___x_1700_);
                if v___x_1701_ == 0 {
                    crate::leanh::lean_dec_ref(v_body_1693_);
                    return v___x_1701_;
                } else {
                    v_e_1691_ = v_body_1693_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_CasesMatch_0__Lean_Meta_Grind_isMatchCondCandidate_go___boxed(
    mut v_e_1719_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1720_: u8 = 0;
    let mut v_r_1721_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1720_ =
        l___private_Lean_Meta_Tactic_Grind_CasesMatch_0__Lean_Meta_Grind_isMatchCondCandidate_go(
            v_e_1719_,
        );
    v_r_1721_ = crate::leanh::lean_box((v_res_1720_) as usize);
    return v_r_1721_;
}
pub unsafe fn l_Lean_Meta_Grind_isMatchCondCandidate(
    mut v_e_1722_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_1723_: u8 = 0;
    v___x_1723_ = l_Lean_Expr_isForall(v_e_1722_);
    if v___x_1723_ == 0 {
        crate::leanh::lean_dec_ref(v_e_1722_);
        return v___x_1723_;
    } else {
        let mut v___x_1724_: u8 = 0;
        v___x_1724_ = l___private_Lean_Meta_Tactic_Grind_CasesMatch_0__Lean_Meta_Grind_isMatchCondCandidate_go(v_e_1722_);
        return v___x_1724_;
    }
}
pub unsafe fn l_Lean_Meta_Grind_isMatchCondCandidate___boxed(
    mut v_e_1725_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1726_: u8 = 0;
    let mut v_r_1727_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1726_ = l_Lean_Meta_Grind_isMatchCondCandidate(v_e_1725_);
    v_r_1727_ = crate::leanh::lean_box((v_res_1726_) as usize);
    return v_r_1727_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_CasesMatch_0__Lean_Meta_Grind_addMatchCondsToAlt(
    mut v_alt_1728_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_binderName_1729_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_binderType_1730_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_body_1731_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_binderInfo_1732_: u8 = 0;
    let mut v___y_1734_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1735_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1736_: u8 = 0;
    let mut v___x_1737_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1738_: u8 = 0;
    let mut v___x_1739_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1741_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1742_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1743_: usize = 0;
    let mut v___x_1744_: usize = 0;
    let mut v___x_1745_: u8 = 0;
    let mut v___x_1746_: usize = 0;
    let mut v___x_1747_: usize = 0;
    let mut v___x_1748_: u8 = 0;
    let mut v___x_1749_: u8 = 0;
    let mut v___x_1750_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_alt_1728_) == 7 {
                    v_binderName_1729_ = crate::leanh::lean_ctor_get(v_alt_1728_, 0);
                    v_binderType_1730_ = crate::leanh::lean_ctor_get(v_alt_1728_, 1);
                    v_body_1731_ = crate::leanh::lean_ctor_get(v_alt_1728_, 2);
                    v_binderInfo_1732_ = crate::leanh::lean_ctor_get_uint8(
                        v_alt_1728_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 8) as u32,
                    );
                    crate::leanh::lean_inc_ref(v_binderType_1730_);
                    v___x_1749_ = l_Lean_Meta_Grind_isMatchCondCandidate(v_binderType_1730_);
                    if v___x_1749_ == 0 {
                        crate::leanh::lean_inc_ref(v_binderType_1730_);
                        v___y_1741_ = v_binderType_1730_;
                        state = 2;
                        continue;
                    } else {
                        crate::leanh::lean_inc_ref(v_binderType_1730_);
                        v___x_1750_ = l_Lean_Meta_Grind_markAsPreMatchCond(v_binderType_1730_);
                        v___y_1741_ = v___x_1750_;
                        state = 2;
                        continue;
                    }
                } else {
                    return v_alt_1728_;
                }
            }
            1 => {
                if v___y_1736_ == 0 {
                    crate::leanh::lean_inc(v_binderName_1729_);
                    crate::leanh::lean_dec_ref_known(v_alt_1728_, 3);
                    v___x_1737_ = l_Lean_Expr_forallE___override(
                        v_binderName_1729_,
                        v___y_1735_,
                        v___y_1734_,
                        v_binderInfo_1732_,
                    );
                    return v___x_1737_;
                } else {
                    v___x_1738_ =
                        l_Lean_instBEqBinderInfo_beq(v_binderInfo_1732_, v_binderInfo_1732_);
                    if v___x_1738_ == 0 {
                        crate::leanh::lean_inc(v_binderName_1729_);
                        crate::leanh::lean_dec_ref_known(v_alt_1728_, 3);
                        v___x_1739_ = l_Lean_Expr_forallE___override(
                            v_binderName_1729_,
                            v___y_1735_,
                            v___y_1734_,
                            v_binderInfo_1732_,
                        );
                        return v___x_1739_;
                    } else {
                        crate::leanh::lean_dec_ref(v___y_1735_);
                        crate::leanh::lean_dec_ref(v___y_1734_);
                        return v_alt_1728_;
                    }
                }
            }
            2 => {
                crate::leanh::lean_inc_ref(v_body_1731_);
                v___x_1742_ = l___private_Lean_Meta_Tactic_Grind_CasesMatch_0__Lean_Meta_Grind_addMatchCondsToAlt(v_body_1731_);
                v___x_1743_ = lean_ptr_addr(v_binderType_1730_);
                v___x_1744_ = lean_ptr_addr(v___y_1741_);
                v___x_1745_ = lean_usize_dec_eq(v___x_1743_, v___x_1744_);
                if v___x_1745_ == 0 {
                    v___y_1734_ = v___x_1742_;
                    v___y_1735_ = v___y_1741_;
                    v___y_1736_ = v___x_1745_;
                    state = 1;
                    continue;
                } else {
                    v___x_1746_ = lean_ptr_addr(v_body_1731_);
                    v___x_1747_ = lean_ptr_addr(v___x_1742_);
                    v___x_1748_ = lean_usize_dec_eq(v___x_1746_, v___x_1747_);
                    v___y_1734_ = v___x_1742_;
                    v___y_1735_ = v___y_1741_;
                    v___y_1736_ = v___x_1748_;
                    state = 1;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_CasesMatch_0__Lean_Meta_Grind_addMatchCondsToSplitter(
    mut v_splitterType_1751_: *mut crate::leanh::LeanObject,
    mut v_numAlts_1752_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1753_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1754_: u8 = 0;
    let mut v_binderName_1755_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_binderType_1756_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_body_1757_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_binderInfo_1758_: u8 = 0;
    let mut v___x_1759_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1760_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1761_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1762_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1764_: u8 = 0;
    let mut v___x_1765_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1766_: u8 = 0;
    let mut v___x_1767_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1768_: usize = 0;
    let mut v___x_1769_: usize = 0;
    let mut v___x_1770_: u8 = 0;
    let mut v___x_1771_: usize = 0;
    let mut v___x_1772_: usize = 0;
    let mut v___x_1773_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1753_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_1754_ = lean_nat_dec_eq(v_numAlts_1752_, v___x_1753_);
                if v___x_1754_ == 0 {
                    if crate::leanh::lean_obj_tag(v_splitterType_1751_) == 7 {
                        v_binderName_1755_ = crate::leanh::lean_ctor_get(v_splitterType_1751_, 0);
                        v_binderType_1756_ = crate::leanh::lean_ctor_get(v_splitterType_1751_, 1);
                        v_body_1757_ = crate::leanh::lean_ctor_get(v_splitterType_1751_, 2);
                        v_binderInfo_1758_ = crate::leanh::lean_ctor_get_uint8(
                            v_splitterType_1751_,
                            (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 8) as u32,
                        );
                        crate::leanh::lean_inc_ref(v_binderType_1756_);
                        v___x_1759_ = l___private_Lean_Meta_Tactic_Grind_CasesMatch_0__Lean_Meta_Grind_addMatchCondsToAlt(v_binderType_1756_);
                        v___x_1760_ = crate::leanh::lean_unsigned_to_nat(1);
                        v___x_1761_ = lean_nat_sub(v_numAlts_1752_, v___x_1760_);
                        crate::leanh::lean_inc_ref(v_body_1757_);
                        v___x_1762_ = l___private_Lean_Meta_Tactic_Grind_CasesMatch_0__Lean_Meta_Grind_addMatchCondsToSplitter(v_body_1757_, v___x_1761_);
                        crate::leanh::lean_dec(v___x_1761_);
                        v___x_1768_ = lean_ptr_addr(v_binderType_1756_);
                        v___x_1769_ = lean_ptr_addr(v___x_1759_);
                        v___x_1770_ = lean_usize_dec_eq(v___x_1768_, v___x_1769_);
                        if v___x_1770_ == 0 {
                            v___y_1764_ = v___x_1770_;
                            state = 1;
                            continue;
                        } else {
                            v___x_1771_ = lean_ptr_addr(v_body_1757_);
                            v___x_1772_ = lean_ptr_addr(v___x_1762_);
                            v___x_1773_ = lean_usize_dec_eq(v___x_1771_, v___x_1772_);
                            v___y_1764_ = v___x_1773_;
                            state = 1;
                            continue;
                        }
                    } else {
                        return v_splitterType_1751_;
                    }
                } else {
                    return v_splitterType_1751_;
                }
            }
            1 => {
                if v___y_1764_ == 0 {
                    crate::leanh::lean_inc(v_binderName_1755_);
                    crate::leanh::lean_dec_ref_known(v_splitterType_1751_, 3);
                    v___x_1765_ = l_Lean_Expr_forallE___override(
                        v_binderName_1755_,
                        v___x_1759_,
                        v___x_1762_,
                        v_binderInfo_1758_,
                    );
                    return v___x_1765_;
                } else {
                    v___x_1766_ =
                        l_Lean_instBEqBinderInfo_beq(v_binderInfo_1758_, v_binderInfo_1758_);
                    if v___x_1766_ == 0 {
                        crate::leanh::lean_inc(v_binderName_1755_);
                        crate::leanh::lean_dec_ref_known(v_splitterType_1751_, 3);
                        v___x_1767_ = l_Lean_Expr_forallE___override(
                            v_binderName_1755_,
                            v___x_1759_,
                            v___x_1762_,
                            v_binderInfo_1758_,
                        );
                        return v___x_1767_;
                    } else {
                        crate::leanh::lean_dec_ref(v___x_1762_);
                        crate::leanh::lean_dec_ref(v___x_1759_);
                        return v_splitterType_1751_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_CasesMatch_0__Lean_Meta_Grind_addMatchCondsToSplitter___boxed(
    mut v_splitterType_1774_: *mut crate::leanh::LeanObject,
    mut v_numAlts_1775_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1776_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1776_ =
        l___private_Lean_Meta_Tactic_Grind_CasesMatch_0__Lean_Meta_Grind_addMatchCondsToSplitter(
            v_splitterType_1774_,
            v_numAlts_1775_,
        );
    crate::leanh::lean_dec(v_numAlts_1775_);
    return v_res_1776_;
}
pub unsafe fn l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_Tactic_Grind_CasesMatch_0__Lean_Meta_Grind_casesMatch_mkMotiveAndRefls_spec__0___redArg___lam__0(
    mut v_k_1777_: *mut crate::leanh::LeanObject,
    mut v_b_1778_: *mut crate::leanh::LeanObject,
    mut v_c_1779_: *mut crate::leanh::LeanObject,
    mut v___y_1780_: *mut crate::leanh::LeanObject,
    mut v___y_1781_: *mut crate::leanh::LeanObject,
    mut v___y_1782_: *mut crate::leanh::LeanObject,
    mut v___y_1783_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1785_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    crate::leanh::lean_inc(v___y_1783_);
    crate::leanh::lean_inc_ref(v___y_1782_);
    crate::leanh::lean_inc(v___y_1781_);
    crate::leanh::lean_inc_ref(v___y_1780_);
    v___x_1785_ = crate::leanh::lean_apply_7(
        v_k_1777_,
        v_b_1778_,
        v_c_1779_,
        v___y_1780_,
        v___y_1781_,
        v___y_1782_,
        v___y_1783_,
        crate::leanh::lean_box(0),
    );
    return v___x_1785_;
}
pub unsafe fn l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_Tactic_Grind_CasesMatch_0__Lean_Meta_Grind_casesMatch_mkMotiveAndRefls_spec__0___redArg___lam__0___boxed(
    mut v_k_1786_: *mut crate::leanh::LeanObject,
    mut v_b_1787_: *mut crate::leanh::LeanObject,
    mut v_c_1788_: *mut crate::leanh::LeanObject,
    mut v___y_1789_: *mut crate::leanh::LeanObject,
    mut v___y_1790_: *mut crate::leanh::LeanObject,
    mut v___y_1791_: *mut crate::leanh::LeanObject,
    mut v___y_1792_: *mut crate::leanh::LeanObject,
    mut v___y_1793_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1794_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1794_ = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_Tactic_Grind_CasesMatch_0__Lean_Meta_Grind_casesMatch_mkMotiveAndRefls_spec__0___redArg___lam__0(v_k_1786_, v_b_1787_, v_c_1788_, v___y_1789_, v___y_1790_, v___y_1791_, v___y_1792_);
    crate::leanh::lean_dec(v___y_1792_);
    crate::leanh::lean_dec_ref(v___y_1791_);
    crate::leanh::lean_dec(v___y_1790_);
    crate::leanh::lean_dec_ref(v___y_1789_);
    return v_res_1794_;
}
pub unsafe fn l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_Tactic_Grind_CasesMatch_0__Lean_Meta_Grind_casesMatch_mkMotiveAndRefls_spec__0___redArg(
    mut v_type_1795_: *mut crate::leanh::LeanObject,
    mut v_maxFVars_x3f_1796_: *mut crate::leanh::LeanObject,
    mut v_k_1797_: *mut crate::leanh::LeanObject,
    mut v_cleanupAnnotations_1798_: u8,
    mut v_whnfType_1799_: u8,
    mut v___y_1800_: *mut crate::leanh::LeanObject,
    mut v___y_1801_: *mut crate::leanh::LeanObject,
    mut v___y_1802_: *mut crate::leanh::LeanObject,
    mut v___y_1803_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_1805_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1806_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1807_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1809_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1810_: u8 = 0;
    let mut v___x_1812_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1813_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1814_: u8 = 0;
    let mut v_a_1815_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1817_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1818_: u8 = 0;
    let mut v___x_1820_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1821_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1822_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___f_1805_ = crate::leanh::lean_alloc_closure(l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_Tactic_Grind_CasesMatch_0__Lean_Meta_Grind_casesMatch_mkMotiveAndRefls_spec__0___redArg___lam__0___boxed as *mut core::ffi::c_void, 8, 1);
                crate::leanh::lean_closure_set(v___f_1805_, 0, v_k_1797_);
                v___x_1806_ = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAux(
                    crate::leanh::lean_box(0),
                    v_type_1795_,
                    v_maxFVars_x3f_1796_,
                    v___f_1805_,
                    v_cleanupAnnotations_1798_,
                    v_whnfType_1799_,
                    v___y_1800_,
                    v___y_1801_,
                    v___y_1802_,
                    v___y_1803_,
                );
                if crate::leanh::lean_obj_tag(v___x_1806_) == 0 {
                    v_a_1807_ = crate::leanh::lean_ctor_get(v___x_1806_, 0);
                    v_isSharedCheck_1814_ = (!crate::leanh::lean_is_exclusive(v___x_1806_)) as u8;
                    if v_isSharedCheck_1814_ == 0 {
                        v___x_1809_ = v___x_1806_;
                        v_isShared_1810_ = v_isSharedCheck_1814_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1807_);
                        crate::leanh::lean_dec(v___x_1806_);
                        v___x_1809_ = crate::leanh::lean_box(0);
                        v_isShared_1810_ = v_isSharedCheck_1814_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_1815_ = crate::leanh::lean_ctor_get(v___x_1806_, 0);
                    v_isSharedCheck_1822_ = (!crate::leanh::lean_is_exclusive(v___x_1806_)) as u8;
                    if v_isSharedCheck_1822_ == 0 {
                        v___x_1817_ = v___x_1806_;
                        v_isShared_1818_ = v_isSharedCheck_1822_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1815_);
                        crate::leanh::lean_dec(v___x_1806_);
                        v___x_1817_ = crate::leanh::lean_box(0);
                        v_isShared_1818_ = v_isSharedCheck_1822_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_1810_ == 0 {
                    v___x_1812_ = v___x_1809_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1813_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1813_, 0, v_a_1807_);
                    v___x_1812_ = v_reuseFailAlloc_1813_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1812_;
            }
            3 => {
                if v_isShared_1818_ == 0 {
                    v___x_1820_ = v___x_1817_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1821_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1821_, 0, v_a_1815_);
                    v___x_1820_ = v_reuseFailAlloc_1821_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_1820_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_Tactic_Grind_CasesMatch_0__Lean_Meta_Grind_casesMatch_mkMotiveAndRefls_spec__0___redArg___boxed(
    mut v_type_1823_: *mut crate::leanh::LeanObject,
    mut v_maxFVars_x3f_1824_: *mut crate::leanh::LeanObject,
    mut v_k_1825_: *mut crate::leanh::LeanObject,
    mut v_cleanupAnnotations_1826_: *mut crate::leanh::LeanObject,
    mut v_whnfType_1827_: *mut crate::leanh::LeanObject,
    mut v___y_1828_: *mut crate::leanh::LeanObject,
    mut v___y_1829_: *mut crate::leanh::LeanObject,
    mut v___y_1830_: *mut crate::leanh::LeanObject,
    mut v___y_1831_: *mut crate::leanh::LeanObject,
    mut v___y_1832_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_cleanupAnnotations_boxed_1833_: u8 = 0;
    let mut v_whnfType_boxed_1834_: u8 = 0;
    let mut v_res_1835_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_cleanupAnnotations_boxed_1833_ = (crate::leanh::lean_unbox(v_cleanupAnnotations_1826_) as u8);
    v_whnfType_boxed_1834_ = (crate::leanh::lean_unbox(v_whnfType_1827_) as u8);
    v_res_1835_ = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_Tactic_Grind_CasesMatch_0__Lean_Meta_Grind_casesMatch_mkMotiveAndRefls_spec__0___redArg(v_type_1823_, v_maxFVars_x3f_1824_, v_k_1825_, v_cleanupAnnotations_boxed_1833_, v_whnfType_boxed_1834_, v___y_1828_, v___y_1829_, v___y_1830_, v___y_1831_);
    crate::leanh::lean_dec(v___y_1831_);
    crate::leanh::lean_dec_ref(v___y_1830_);
    crate::leanh::lean_dec(v___y_1829_);
    crate::leanh::lean_dec_ref(v___y_1828_);
    return v_res_1835_;
}
pub unsafe fn l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_Tactic_Grind_CasesMatch_0__Lean_Meta_Grind_casesMatch_mkMotiveAndRefls_spec__0(
    mut v_00_u03b1_1836_: *mut crate::leanh::LeanObject,
    mut v_type_1837_: *mut crate::leanh::LeanObject,
    mut v_maxFVars_x3f_1838_: *mut crate::leanh::LeanObject,
    mut v_k_1839_: *mut crate::leanh::LeanObject,
    mut v_cleanupAnnotations_1840_: u8,
    mut v_whnfType_1841_: u8,
    mut v___y_1842_: *mut crate::leanh::LeanObject,
    mut v___y_1843_: *mut crate::leanh::LeanObject,
    mut v___y_1844_: *mut crate::leanh::LeanObject,
    mut v___y_1845_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1847_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1847_ = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_Tactic_Grind_CasesMatch_0__Lean_Meta_Grind_casesMatch_mkMotiveAndRefls_spec__0___redArg(v_type_1837_, v_maxFVars_x3f_1838_, v_k_1839_, v_cleanupAnnotations_1840_, v_whnfType_1841_, v___y_1842_, v___y_1843_, v___y_1844_, v___y_1845_);
    return v___x_1847_;
}
pub unsafe fn l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_Tactic_Grind_CasesMatch_0__Lean_Meta_Grind_casesMatch_mkMotiveAndRefls_spec__0___boxed(
    mut v_00_u03b1_1848_: *mut crate::leanh::LeanObject,
    mut v_type_1849_: *mut crate::leanh::LeanObject,
    mut v_maxFVars_x3f_1850_: *mut crate::leanh::LeanObject,
    mut v_k_1851_: *mut crate::leanh::LeanObject,
    mut v_cleanupAnnotations_1852_: *mut crate::leanh::LeanObject,
    mut v_whnfType_1853_: *mut crate::leanh::LeanObject,
    mut v___y_1854_: *mut crate::leanh::LeanObject,
    mut v___y_1855_: *mut crate::leanh::LeanObject,
    mut v___y_1856_: *mut crate::leanh::LeanObject,
    mut v___y_1857_: *mut crate::leanh::LeanObject,
    mut v___y_1858_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_cleanupAnnotations_boxed_1859_: u8 = 0;
    let mut v_whnfType_boxed_1860_: u8 = 0;
    let mut v_res_1861_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_cleanupAnnotations_boxed_1859_ = (crate::leanh::lean_unbox(v_cleanupAnnotations_1852_) as u8);
    v_whnfType_boxed_1860_ = (crate::leanh::lean_unbox(v_whnfType_1853_) as u8);
    v_res_1861_ = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_Tactic_Grind_CasesMatch_0__Lean_Meta_Grind_casesMatch_mkMotiveAndRefls_spec__0(v_00_u03b1_1848_, v_type_1849_, v_maxFVars_x3f_1850_, v_k_1851_, v_cleanupAnnotations_boxed_1859_, v_whnfType_boxed_1860_, v___y_1854_, v___y_1855_, v___y_1856_, v___y_1857_);
    crate::leanh::lean_dec(v___y_1857_);
    crate::leanh::lean_dec_ref(v___y_1856_);
    crate::leanh::lean_dec(v___y_1855_);
    crate::leanh::lean_dec_ref(v___y_1854_);
    return v_res_1861_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_CasesMatch_0__Lean_Meta_Grind_casesMatch_mkMotiveAndRefls___lam__0(
    mut v_mvarId_1862_: *mut crate::leanh::LeanObject,
    mut v_xs_1863_: *mut crate::leanh::LeanObject,
    mut v_eqs_1864_: *mut crate::leanh::LeanObject,
    mut v_eqRefls_1865_: *mut crate::leanh::LeanObject,
    mut v___y_1866_: *mut crate::leanh::LeanObject,
    mut v___y_1867_: *mut crate::leanh::LeanObject,
    mut v___y_1868_: *mut crate::leanh::LeanObject,
    mut v___y_1869_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1871_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1872_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1873_: u8 = 0;
    let mut v___x_1874_: u8 = 0;
    let mut v___x_1875_: u8 = 0;
    let mut v___x_1876_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1877_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1878_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1879_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1881_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1882_: u8 = 0;
    let mut v___x_1883_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1885_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1886_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1887_: u8 = 0;
    let mut v_a_1888_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1890_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1891_: u8 = 0;
    let mut v___x_1893_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1894_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1895_: u8 = 0;
    let mut v_a_1896_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1898_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1899_: u8 = 0;
    let mut v___x_1901_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1902_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1903_: u8 = 0;
    let mut v_a_1904_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1906_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1907_: u8 = 0;
    let mut v___x_1909_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1910_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1911_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1871_ = l_Lean_MVarId_getType(
                    v_mvarId_1862_,
                    v___y_1866_,
                    v___y_1867_,
                    v___y_1868_,
                    v___y_1869_,
                );
                if crate::leanh::lean_obj_tag(v___x_1871_) == 0 {
                    v_a_1872_ = crate::leanh::lean_ctor_get(v___x_1871_, 0);
                    crate::leanh::lean_inc(v_a_1872_);
                    crate::leanh::lean_dec_ref_known(v___x_1871_, 1);
                    v___x_1873_ = 0;
                    v___x_1874_ = 1;
                    v___x_1875_ = 1;
                    v___x_1876_ = l_Lean_Meta_mkForallFVars(
                        v_eqs_1864_,
                        v_a_1872_,
                        v___x_1873_,
                        v___x_1874_,
                        v___x_1874_,
                        v___x_1875_,
                        v___y_1866_,
                        v___y_1867_,
                        v___y_1868_,
                        v___y_1869_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_1876_) == 0 {
                        v_a_1877_ = crate::leanh::lean_ctor_get(v___x_1876_, 0);
                        crate::leanh::lean_inc(v_a_1877_);
                        crate::leanh::lean_dec_ref_known(v___x_1876_, 1);
                        v___x_1878_ = l_Lean_Meta_mkLambdaFVars(
                            v_xs_1863_,
                            v_a_1877_,
                            v___x_1873_,
                            v___x_1874_,
                            v___x_1873_,
                            v___x_1874_,
                            v___x_1875_,
                            v___y_1866_,
                            v___y_1867_,
                            v___y_1868_,
                            v___y_1869_,
                        );
                        if crate::leanh::lean_obj_tag(v___x_1878_) == 0 {
                            v_a_1879_ = crate::leanh::lean_ctor_get(v___x_1878_, 0);
                            v_isSharedCheck_1887_ =
                                (!crate::leanh::lean_is_exclusive(v___x_1878_)) as u8;
                            if v_isSharedCheck_1887_ == 0 {
                                v___x_1881_ = v___x_1878_;
                                v_isShared_1882_ = v_isSharedCheck_1887_;
                                state = 1;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_1879_);
                                crate::leanh::lean_dec(v___x_1878_);
                                v___x_1881_ = crate::leanh::lean_box(0);
                                v_isShared_1882_ = v_isSharedCheck_1887_;
                                state = 1;
                                continue;
                            }
                        } else {
                            crate::leanh::lean_dec_ref(v_eqRefls_1865_);
                            v_a_1888_ = crate::leanh::lean_ctor_get(v___x_1878_, 0);
                            v_isSharedCheck_1895_ =
                                (!crate::leanh::lean_is_exclusive(v___x_1878_)) as u8;
                            if v_isSharedCheck_1895_ == 0 {
                                v___x_1890_ = v___x_1878_;
                                v_isShared_1891_ = v_isSharedCheck_1895_;
                                state = 3;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_1888_);
                                crate::leanh::lean_dec(v___x_1878_);
                                v___x_1890_ = crate::leanh::lean_box(0);
                                v_isShared_1891_ = v_isSharedCheck_1895_;
                                state = 3;
                                continue;
                            }
                        }
                    } else {
                        crate::leanh::lean_dec_ref(v_eqRefls_1865_);
                        v_a_1896_ = crate::leanh::lean_ctor_get(v___x_1876_, 0);
                        v_isSharedCheck_1903_ =
                            (!crate::leanh::lean_is_exclusive(v___x_1876_)) as u8;
                        if v_isSharedCheck_1903_ == 0 {
                            v___x_1898_ = v___x_1876_;
                            v_isShared_1899_ = v_isSharedCheck_1903_;
                            state = 5;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_1896_);
                            crate::leanh::lean_dec(v___x_1876_);
                            v___x_1898_ = crate::leanh::lean_box(0);
                            v_isShared_1899_ = v_isSharedCheck_1903_;
                            state = 5;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_eqRefls_1865_);
                    v_a_1904_ = crate::leanh::lean_ctor_get(v___x_1871_, 0);
                    v_isSharedCheck_1911_ = (!crate::leanh::lean_is_exclusive(v___x_1871_)) as u8;
                    if v_isSharedCheck_1911_ == 0 {
                        v___x_1906_ = v___x_1871_;
                        v_isShared_1907_ = v_isSharedCheck_1911_;
                        state = 7;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1904_);
                        crate::leanh::lean_dec(v___x_1871_);
                        v___x_1906_ = crate::leanh::lean_box(0);
                        v_isShared_1907_ = v_isSharedCheck_1911_;
                        state = 7;
                        continue;
                    }
                }
            }
            1 => {
                v___x_1883_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1883_, 0, v_a_1879_);
                crate::leanh::lean_ctor_set(v___x_1883_, 1, v_eqRefls_1865_);
                if v_isShared_1882_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1881_, 0, v___x_1883_);
                    v___x_1885_ = v___x_1881_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1886_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1886_, 0, v___x_1883_);
                    v___x_1885_ = v_reuseFailAlloc_1886_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1885_;
            }
            3 => {
                if v_isShared_1891_ == 0 {
                    v___x_1893_ = v___x_1890_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1894_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1894_, 0, v_a_1888_);
                    v___x_1893_ = v_reuseFailAlloc_1894_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_1893_;
            }
            5 => {
                if v_isShared_1899_ == 0 {
                    v___x_1901_ = v___x_1898_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_1902_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1902_, 0, v_a_1896_);
                    v___x_1901_ = v_reuseFailAlloc_1902_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_1901_;
            }
            7 => {
                if v_isShared_1907_ == 0 {
                    v___x_1909_ = v___x_1906_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_1910_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1910_, 0, v_a_1904_);
                    v___x_1909_ = v_reuseFailAlloc_1910_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_1909_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_CasesMatch_0__Lean_Meta_Grind_casesMatch_mkMotiveAndRefls___lam__0___boxed(
    mut v_mvarId_1912_: *mut crate::leanh::LeanObject,
    mut v_xs_1913_: *mut crate::leanh::LeanObject,
    mut v_eqs_1914_: *mut crate::leanh::LeanObject,
    mut v_eqRefls_1915_: *mut crate::leanh::LeanObject,
    mut v___y_1916_: *mut crate::leanh::LeanObject,
    mut v___y_1917_: *mut crate::leanh::LeanObject,
    mut v___y_1918_: *mut crate::leanh::LeanObject,
    mut v___y_1919_: *mut crate::leanh::LeanObject,
    mut v___y_1920_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1921_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1921_ = l___private_Lean_Meta_Tactic_Grind_CasesMatch_0__Lean_Meta_Grind_casesMatch_mkMotiveAndRefls___lam__0(v_mvarId_1912_, v_xs_1913_, v_eqs_1914_, v_eqRefls_1915_, v___y_1916_, v___y_1917_, v___y_1918_, v___y_1919_);
    crate::leanh::lean_dec(v___y_1919_);
    crate::leanh::lean_dec_ref(v___y_1918_);
    crate::leanh::lean_dec(v___y_1917_);
    crate::leanh::lean_dec_ref(v___y_1916_);
    crate::leanh::lean_dec_ref(v_eqs_1914_);
    crate::leanh::lean_dec_ref(v_xs_1913_);
    return v_res_1921_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_CasesMatch_0__Lean_Meta_Grind_casesMatch_mkMotiveAndRefls___lam__1(
    mut v_mvarId_1922_: *mut crate::leanh::LeanObject,
    mut v_discrs_1923_: *mut crate::leanh::LeanObject,
    mut v_xs_1924_: *mut crate::leanh::LeanObject,
    mut v_x_1925_: *mut crate::leanh::LeanObject,
    mut v___y_1926_: *mut crate::leanh::LeanObject,
    mut v___y_1927_: *mut crate::leanh::LeanObject,
    mut v___y_1928_: *mut crate::leanh::LeanObject,
    mut v___y_1929_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_1931_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1932_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    crate::leanh::lean_inc_ref(v_xs_1924_);
    v___f_1931_ = crate::leanh::lean_alloc_closure(l___private_Lean_Meta_Tactic_Grind_CasesMatch_0__Lean_Meta_Grind_casesMatch_mkMotiveAndRefls___lam__0___boxed as *mut core::ffi::c_void, 9, 2);
    crate::leanh::lean_closure_set(v___f_1931_, 0, v_mvarId_1922_);
    crate::leanh::lean_closure_set(v___f_1931_, 1, v_xs_1924_);
    v___x_1932_ = l_Lean_Meta_withNewEqs___redArg(
        v_discrs_1923_,
        v_xs_1924_,
        v___f_1931_,
        v___y_1926_,
        v___y_1927_,
        v___y_1928_,
        v___y_1929_,
    );
    return v___x_1932_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_CasesMatch_0__Lean_Meta_Grind_casesMatch_mkMotiveAndRefls___lam__1___boxed(
    mut v_mvarId_1933_: *mut crate::leanh::LeanObject,
    mut v_discrs_1934_: *mut crate::leanh::LeanObject,
    mut v_xs_1935_: *mut crate::leanh::LeanObject,
    mut v_x_1936_: *mut crate::leanh::LeanObject,
    mut v___y_1937_: *mut crate::leanh::LeanObject,
    mut v___y_1938_: *mut crate::leanh::LeanObject,
    mut v___y_1939_: *mut crate::leanh::LeanObject,
    mut v___y_1940_: *mut crate::leanh::LeanObject,
    mut v___y_1941_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1942_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1942_ = l___private_Lean_Meta_Tactic_Grind_CasesMatch_0__Lean_Meta_Grind_casesMatch_mkMotiveAndRefls___lam__1(v_mvarId_1933_, v_discrs_1934_, v_xs_1935_, v_x_1936_, v___y_1937_, v___y_1938_, v___y_1939_, v___y_1940_);
    crate::leanh::lean_dec(v___y_1940_);
    crate::leanh::lean_dec_ref(v___y_1939_);
    crate::leanh::lean_dec(v___y_1938_);
    crate::leanh::lean_dec_ref(v___y_1937_);
    crate::leanh::lean_dec_ref(v_x_1936_);
    return v_res_1942_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_CasesMatch_0__Lean_Meta_Grind_casesMatch_mkMotiveAndRefls___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1943_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1944_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1943_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_1944_ = l_Lean_Level_ofNat(v___x_1943_);
    return v___x_1944_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_CasesMatch_0__Lean_Meta_Grind_casesMatch_mkMotiveAndRefls___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1945_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_dummy_1946_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1945_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_CasesMatch_0__Lean_Meta_Grind_casesMatch_mkMotiveAndRefls___closed__0), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_CasesMatch_0__Lean_Meta_Grind_casesMatch_mkMotiveAndRefls___closed__0_once), _init_l___private_Lean_Meta_Tactic_Grind_CasesMatch_0__Lean_Meta_Grind_casesMatch_mkMotiveAndRefls___closed__0);
    v_dummy_1946_ = l_Lean_mkSort(v___x_1945_);
    return v_dummy_1946_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_CasesMatch_0__Lean_Meta_Grind_casesMatch_mkMotiveAndRefls(
    mut v_mvarId_1947_: *mut crate::leanh::LeanObject,
    mut v_e_1948_: *mut crate::leanh::LeanObject,
    mut v_app_1949_: *mut crate::leanh::LeanObject,
    mut v_a_1950_: *mut crate::leanh::LeanObject,
    mut v_a_1951_: *mut crate::leanh::LeanObject,
    mut v_a_1952_: *mut crate::leanh::LeanObject,
    mut v_a_1953_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_params_1955_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_discrs_1956_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_dummy_1957_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1958_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1959_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_aux_1960_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1961_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1962_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1963_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1964_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1965_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1966_: u8 = 0;
    let mut v___x_1967_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1968_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1970_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1971_: u8 = 0;
    let mut v___x_1973_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1974_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1975_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_params_1955_ = crate::leanh::lean_ctor_get(v_app_1949_, 3);
                crate::leanh::lean_inc_ref(v_params_1955_);
                v_discrs_1956_ = crate::leanh::lean_ctor_get(v_app_1949_, 5);
                crate::leanh::lean_inc_ref(v_discrs_1956_);
                crate::leanh::lean_dec_ref(v_app_1949_);
                v_dummy_1957_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_CasesMatch_0__Lean_Meta_Grind_casesMatch_mkMotiveAndRefls___closed__1), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_CasesMatch_0__Lean_Meta_Grind_casesMatch_mkMotiveAndRefls___closed__1_once), _init_l___private_Lean_Meta_Tactic_Grind_CasesMatch_0__Lean_Meta_Grind_casesMatch_mkMotiveAndRefls___closed__1);
                v___x_1958_ = l_Lean_Expr_getAppFn(v_e_1948_);
                v___x_1959_ = l_Lean_mkAppN(v___x_1958_, v_params_1955_);
                crate::leanh::lean_dec_ref(v_params_1955_);
                v_aux_1960_ = l_Lean_Expr_app___override(v___x_1959_, v_dummy_1957_);
                crate::leanh::lean_inc(v_a_1953_);
                crate::leanh::lean_inc_ref(v_a_1952_);
                crate::leanh::lean_inc(v_a_1951_);
                crate::leanh::lean_inc_ref(v_a_1950_);
                v___x_1961_ =
                    lean_infer_type(v_aux_1960_, v_a_1950_, v_a_1951_, v_a_1952_, v_a_1953_);
                if crate::leanh::lean_obj_tag(v___x_1961_) == 0 {
                    v_a_1962_ = crate::leanh::lean_ctor_get(v___x_1961_, 0);
                    crate::leanh::lean_inc(v_a_1962_);
                    crate::leanh::lean_dec_ref_known(v___x_1961_, 1);
                    crate::leanh::lean_inc_ref(v_discrs_1956_);
                    v___f_1963_ = crate::leanh::lean_alloc_closure(l___private_Lean_Meta_Tactic_Grind_CasesMatch_0__Lean_Meta_Grind_casesMatch_mkMotiveAndRefls___lam__1___boxed as *mut core::ffi::c_void, 9, 2);
                    crate::leanh::lean_closure_set(v___f_1963_, 0, v_mvarId_1947_);
                    crate::leanh::lean_closure_set(v___f_1963_, 1, v_discrs_1956_);
                    v___x_1964_ = lean_array_get_size(v_discrs_1956_);
                    crate::leanh::lean_dec_ref(v_discrs_1956_);
                    v___x_1965_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1965_, 0, v___x_1964_);
                    v___x_1966_ = 0;
                    v___x_1967_ = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_Tactic_Grind_CasesMatch_0__Lean_Meta_Grind_casesMatch_mkMotiveAndRefls_spec__0___redArg(v_a_1962_, v___x_1965_, v___f_1963_, v___x_1966_, v___x_1966_, v_a_1950_, v_a_1951_, v_a_1952_, v_a_1953_);
                    return v___x_1967_;
                } else {
                    crate::leanh::lean_dec_ref(v_discrs_1956_);
                    crate::leanh::lean_dec(v_mvarId_1947_);
                    v_a_1968_ = crate::leanh::lean_ctor_get(v___x_1961_, 0);
                    v_isSharedCheck_1975_ = (!crate::leanh::lean_is_exclusive(v___x_1961_)) as u8;
                    if v_isSharedCheck_1975_ == 0 {
                        v___x_1970_ = v___x_1961_;
                        v_isShared_1971_ = v_isSharedCheck_1975_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1968_);
                        crate::leanh::lean_dec(v___x_1961_);
                        v___x_1970_ = crate::leanh::lean_box(0);
                        v_isShared_1971_ = v_isSharedCheck_1975_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_1971_ == 0 {
                    v___x_1973_ = v___x_1970_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1974_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1974_, 0, v_a_1968_);
                    v___x_1973_ = v_reuseFailAlloc_1974_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1973_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_CasesMatch_0__Lean_Meta_Grind_casesMatch_mkMotiveAndRefls___boxed(
    mut v_mvarId_1976_: *mut crate::leanh::LeanObject,
    mut v_e_1977_: *mut crate::leanh::LeanObject,
    mut v_app_1978_: *mut crate::leanh::LeanObject,
    mut v_a_1979_: *mut crate::leanh::LeanObject,
    mut v_a_1980_: *mut crate::leanh::LeanObject,
    mut v_a_1981_: *mut crate::leanh::LeanObject,
    mut v_a_1982_: *mut crate::leanh::LeanObject,
    mut v_a_1983_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1984_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1984_ = l___private_Lean_Meta_Tactic_Grind_CasesMatch_0__Lean_Meta_Grind_casesMatch_mkMotiveAndRefls(v_mvarId_1976_, v_e_1977_, v_app_1978_, v_a_1979_, v_a_1980_, v_a_1981_, v_a_1982_);
    crate::leanh::lean_dec(v_a_1982_);
    crate::leanh::lean_dec_ref(v_a_1981_);
    crate::leanh::lean_dec(v_a_1980_);
    crate::leanh::lean_dec_ref(v_a_1979_);
    crate::leanh::lean_dec_ref(v_e_1977_);
    return v_res_1984_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_CasesMatch_0__Lean_Meta_Grind_casesMatch_updateTags_spec__0___redArg(
    mut v_a_1985_: *mut crate::leanh::LeanObject,
    mut v_as_1986_: *mut crate::leanh::LeanObject,
    mut v_sz_1987_: usize,
    mut v_i_1988_: usize,
    mut v_b_1989_: *mut crate::leanh::LeanObject,
    mut v___y_1990_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1992_: u8 = 0;
    let mut v___x_1993_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1994_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1995_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1996_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1997_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1998_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1999_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2000_: usize = 0;
    let mut v___x_2001_: usize = 0;
    let mut v_a_2003_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2005_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2006_: u8 = 0;
    let mut v___x_2008_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2009_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2010_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1992_ = lean_usize_dec_lt(v_i_1988_, v_sz_1987_);
                if v___x_1992_ == 0 {
                    crate::leanh::lean_dec(v_a_1985_);
                    v___x_1993_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1993_, 0, v_b_1989_);
                    return v___x_1993_;
                } else {
                    v_a_1994_ = lean_array_uget_borrowed(v_as_1986_, v_i_1988_);
                    v___x_1995_ = l_Lean_Expr_mvarId_x21(v_a_1994_);
                    crate::leanh::lean_inc(v_b_1989_);
                    crate::leanh::lean_inc(v_a_1985_);
                    v___x_1996_ = l_Lean_Name_num___override(v_a_1985_, v_b_1989_);
                    v___x_1997_ =
                        l_Lean_MVarId_setTag___redArg(v___x_1995_, v___x_1996_, v___y_1990_);
                    if crate::leanh::lean_obj_tag(v___x_1997_) == 0 {
                        crate::leanh::lean_dec_ref_known(v___x_1997_, 1);
                        v___x_1998_ = crate::leanh::lean_unsigned_to_nat(1);
                        v___x_1999_ = lean_nat_add(v_b_1989_, v___x_1998_);
                        crate::leanh::lean_dec(v_b_1989_);
                        v___x_2000_ = 1usize;
                        v___x_2001_ = lean_usize_add(v_i_1988_, v___x_2000_);
                        v_i_1988_ = v___x_2001_;
                        v_b_1989_ = v___x_1999_;
                        state = 0;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v_b_1989_);
                        crate::leanh::lean_dec(v_a_1985_);
                        v_a_2003_ = crate::leanh::lean_ctor_get(v___x_1997_, 0);
                        v_isSharedCheck_2010_ =
                            (!crate::leanh::lean_is_exclusive(v___x_1997_)) as u8;
                        if v_isSharedCheck_2010_ == 0 {
                            v___x_2005_ = v___x_1997_;
                            v_isShared_2006_ = v_isSharedCheck_2010_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_2003_);
                            crate::leanh::lean_dec(v___x_1997_);
                            v___x_2005_ = crate::leanh::lean_box(0);
                            v_isShared_2006_ = v_isSharedCheck_2010_;
                            state = 1;
                            continue;
                        }
                    }
                }
            }
            1 => {
                if v_isShared_2006_ == 0 {
                    v___x_2008_ = v___x_2005_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2009_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2009_, 0, v_a_2003_);
                    v___x_2008_ = v_reuseFailAlloc_2009_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2008_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_CasesMatch_0__Lean_Meta_Grind_casesMatch_updateTags_spec__0___redArg___boxed(
    mut v_a_2011_: *mut crate::leanh::LeanObject,
    mut v_as_2012_: *mut crate::leanh::LeanObject,
    mut v_sz_2013_: *mut crate::leanh::LeanObject,
    mut v_i_2014_: *mut crate::leanh::LeanObject,
    mut v_b_2015_: *mut crate::leanh::LeanObject,
    mut v___y_2016_: *mut crate::leanh::LeanObject,
    mut v___y_2017_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_boxed_2018_: usize = 0;
    let mut v_i_boxed_2019_: usize = 0;
    let mut v_res_2020_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_2018_ = crate::leanh::lean_unbox_usize(v_sz_2013_);
    crate::leanh::lean_dec(v_sz_2013_);
    v_i_boxed_2019_ = crate::leanh::lean_unbox_usize(v_i_2014_);
    crate::leanh::lean_dec(v_i_2014_);
    v_res_2020_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_CasesMatch_0__Lean_Meta_Grind_casesMatch_updateTags_spec__0___redArg(v_a_2011_, v_as_2012_, v_sz_boxed_2018_, v_i_boxed_2019_, v_b_2015_, v___y_2016_);
    crate::leanh::lean_dec(v___y_2016_);
    crate::leanh::lean_dec_ref(v_as_2012_);
    return v_res_2020_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_CasesMatch_0__Lean_Meta_Grind_casesMatch_updateTags(
    mut v_mvarId_2021_: *mut crate::leanh::LeanObject,
    mut v_mvars_2022_: *mut crate::leanh::LeanObject,
    mut v_a_2023_: *mut crate::leanh::LeanObject,
    mut v_a_2024_: *mut crate::leanh::LeanObject,
    mut v_a_2025_: *mut crate::leanh::LeanObject,
    mut v_a_2026_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2028_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2029_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2030_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2031_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2032_: u8 = 0;
    let mut v_sz_2033_: usize = 0;
    let mut v___x_2034_: usize = 0;
    let mut v___x_2035_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2037_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2038_: u8 = 0;
    let mut v___x_2039_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2041_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2042_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2043_: u8 = 0;
    let mut v_unused_2044_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2045_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2047_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2048_: u8 = 0;
    let mut v___x_2050_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2051_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2052_: u8 = 0;
    let mut v___x_2053_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2054_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2055_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2056_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2057_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2058_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2060_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2061_: u8 = 0;
    let mut v___x_2063_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2064_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2065_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2028_ = l_Lean_MVarId_getTag(
                    v_mvarId_2021_,
                    v_a_2023_,
                    v_a_2024_,
                    v_a_2025_,
                    v_a_2026_,
                );
                if crate::leanh::lean_obj_tag(v___x_2028_) == 0 {
                    v_a_2029_ = crate::leanh::lean_ctor_get(v___x_2028_, 0);
                    crate::leanh::lean_inc(v_a_2029_);
                    crate::leanh::lean_dec_ref_known(v___x_2028_, 1);
                    v___x_2030_ = lean_array_get_size(v_mvars_2022_);
                    v___x_2031_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_2032_ = lean_nat_dec_eq(v___x_2030_, v___x_2031_);
                    if v___x_2032_ == 0 {
                        v_sz_2033_ = lean_array_size(v_mvars_2022_);
                        v___x_2034_ = 0usize;
                        v___x_2035_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_CasesMatch_0__Lean_Meta_Grind_casesMatch_updateTags_spec__0___redArg(v_a_2029_, v_mvars_2022_, v_sz_2033_, v___x_2034_, v___x_2031_, v_a_2024_);
                        if crate::leanh::lean_obj_tag(v___x_2035_) == 0 {
                            v_isSharedCheck_2043_ =
                                (!crate::leanh::lean_is_exclusive(v___x_2035_)) as u8;
                            if v_isSharedCheck_2043_ == 0 {
                                v_unused_2044_ = crate::leanh::lean_ctor_get(v___x_2035_, 0);
                                crate::leanh::lean_dec(v_unused_2044_);
                                v___x_2037_ = v___x_2035_;
                                v_isShared_2038_ = v_isSharedCheck_2043_;
                                state = 1;
                                continue;
                            } else {
                                crate::leanh::lean_dec(v___x_2035_);
                                v___x_2037_ = crate::leanh::lean_box(0);
                                v_isShared_2038_ = v_isSharedCheck_2043_;
                                state = 1;
                                continue;
                            }
                        } else {
                            v_a_2045_ = crate::leanh::lean_ctor_get(v___x_2035_, 0);
                            v_isSharedCheck_2052_ =
                                (!crate::leanh::lean_is_exclusive(v___x_2035_)) as u8;
                            if v_isSharedCheck_2052_ == 0 {
                                v___x_2047_ = v___x_2035_;
                                v_isShared_2048_ = v_isSharedCheck_2052_;
                                state = 3;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_2045_);
                                crate::leanh::lean_dec(v___x_2035_);
                                v___x_2047_ = crate::leanh::lean_box(0);
                                v_isShared_2048_ = v_isSharedCheck_2052_;
                                state = 3;
                                continue;
                            }
                        }
                    } else {
                        v___x_2053_ = l_Lean_instInhabitedExpr;
                        v___x_2054_ = crate::leanh::lean_unsigned_to_nat(0);
                        v___x_2055_ =
                            lean_array_get_borrowed(v___x_2053_, v_mvars_2022_, v___x_2054_);
                        v___x_2056_ = l_Lean_Expr_mvarId_x21(v___x_2055_);
                        v___x_2057_ =
                            l_Lean_MVarId_setTag___redArg(v___x_2056_, v_a_2029_, v_a_2024_);
                        return v___x_2057_;
                    }
                } else {
                    v_a_2058_ = crate::leanh::lean_ctor_get(v___x_2028_, 0);
                    v_isSharedCheck_2065_ = (!crate::leanh::lean_is_exclusive(v___x_2028_)) as u8;
                    if v_isSharedCheck_2065_ == 0 {
                        v___x_2060_ = v___x_2028_;
                        v_isShared_2061_ = v_isSharedCheck_2065_;
                        state = 5;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2058_);
                        crate::leanh::lean_dec(v___x_2028_);
                        v___x_2060_ = crate::leanh::lean_box(0);
                        v_isShared_2061_ = v_isSharedCheck_2065_;
                        state = 5;
                        continue;
                    }
                }
            }
            1 => {
                v___x_2039_ = crate::leanh::lean_box(0);
                if v_isShared_2038_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2037_, 0, v___x_2039_);
                    v___x_2041_ = v___x_2037_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2042_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2042_, 0, v___x_2039_);
                    v___x_2041_ = v_reuseFailAlloc_2042_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2041_;
            }
            3 => {
                if v_isShared_2048_ == 0 {
                    v___x_2050_ = v___x_2047_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2051_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2051_, 0, v_a_2045_);
                    v___x_2050_ = v_reuseFailAlloc_2051_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_2050_;
            }
            5 => {
                if v_isShared_2061_ == 0 {
                    v___x_2063_ = v___x_2060_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_2064_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2064_, 0, v_a_2058_);
                    v___x_2063_ = v_reuseFailAlloc_2064_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_2063_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_CasesMatch_0__Lean_Meta_Grind_casesMatch_updateTags___boxed(
    mut v_mvarId_2066_: *mut crate::leanh::LeanObject,
    mut v_mvars_2067_: *mut crate::leanh::LeanObject,
    mut v_a_2068_: *mut crate::leanh::LeanObject,
    mut v_a_2069_: *mut crate::leanh::LeanObject,
    mut v_a_2070_: *mut crate::leanh::LeanObject,
    mut v_a_2071_: *mut crate::leanh::LeanObject,
    mut v_a_2072_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2073_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2073_ =
        l___private_Lean_Meta_Tactic_Grind_CasesMatch_0__Lean_Meta_Grind_casesMatch_updateTags(
            v_mvarId_2066_,
            v_mvars_2067_,
            v_a_2068_,
            v_a_2069_,
            v_a_2070_,
            v_a_2071_,
        );
    crate::leanh::lean_dec(v_a_2071_);
    crate::leanh::lean_dec_ref(v_a_2070_);
    crate::leanh::lean_dec(v_a_2069_);
    crate::leanh::lean_dec_ref(v_a_2068_);
    crate::leanh::lean_dec_ref(v_mvars_2067_);
    return v_res_2073_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_CasesMatch_0__Lean_Meta_Grind_casesMatch_updateTags_spec__0(
    mut v_a_2074_: *mut crate::leanh::LeanObject,
    mut v_as_2075_: *mut crate::leanh::LeanObject,
    mut v_sz_2076_: usize,
    mut v_i_2077_: usize,
    mut v_b_2078_: *mut crate::leanh::LeanObject,
    mut v___y_2079_: *mut crate::leanh::LeanObject,
    mut v___y_2080_: *mut crate::leanh::LeanObject,
    mut v___y_2081_: *mut crate::leanh::LeanObject,
    mut v___y_2082_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2084_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2084_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_CasesMatch_0__Lean_Meta_Grind_casesMatch_updateTags_spec__0___redArg(v_a_2074_, v_as_2075_, v_sz_2076_, v_i_2077_, v_b_2078_, v___y_2080_);
    return v___x_2084_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_CasesMatch_0__Lean_Meta_Grind_casesMatch_updateTags_spec__0___boxed(
    mut v_a_2085_: *mut crate::leanh::LeanObject,
    mut v_as_2086_: *mut crate::leanh::LeanObject,
    mut v_sz_2087_: *mut crate::leanh::LeanObject,
    mut v_i_2088_: *mut crate::leanh::LeanObject,
    mut v_b_2089_: *mut crate::leanh::LeanObject,
    mut v___y_2090_: *mut crate::leanh::LeanObject,
    mut v___y_2091_: *mut crate::leanh::LeanObject,
    mut v___y_2092_: *mut crate::leanh::LeanObject,
    mut v___y_2093_: *mut crate::leanh::LeanObject,
    mut v___y_2094_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_boxed_2095_: usize = 0;
    let mut v_i_boxed_2096_: usize = 0;
    let mut v_res_2097_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_2095_ = crate::leanh::lean_unbox_usize(v_sz_2087_);
    crate::leanh::lean_dec(v_sz_2087_);
    v_i_boxed_2096_ = crate::leanh::lean_unbox_usize(v_i_2088_);
    crate::leanh::lean_dec(v_i_2088_);
    v_res_2097_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_CasesMatch_0__Lean_Meta_Grind_casesMatch_updateTags_spec__0(v_a_2085_, v_as_2086_, v_sz_boxed_2095_, v_i_boxed_2096_, v_b_2089_, v___y_2090_, v___y_2091_, v___y_2092_, v___y_2093_);
    crate::leanh::lean_dec(v___y_2093_);
    crate::leanh::lean_dec_ref(v___y_2092_);
    crate::leanh::lean_dec(v___y_2091_);
    crate::leanh::lean_dec_ref(v___y_2090_);
    crate::leanh::lean_dec_ref(v_as_2086_);
    return v_res_2097_;
}
pub unsafe fn l_Lean_MVarId_withContext___at___00Lean_Meta_Grind_casesMatch_spec__3___redArg(
    mut v_mvarId_2098_: *mut crate::leanh::LeanObject,
    mut v_x_2099_: *mut crate::leanh::LeanObject,
    mut v___y_2100_: *mut crate::leanh::LeanObject,
    mut v___y_2101_: *mut crate::leanh::LeanObject,
    mut v___y_2102_: *mut crate::leanh::LeanObject,
    mut v___y_2103_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2105_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2106_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2108_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2109_: u8 = 0;
    let mut v___x_2111_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2112_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2113_: u8 = 0;
    let mut v_a_2114_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2116_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2117_: u8 = 0;
    let mut v___x_2119_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2120_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2121_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2105_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(
                    crate::leanh::lean_box(0),
                    v_mvarId_2098_,
                    v_x_2099_,
                    v___y_2100_,
                    v___y_2101_,
                    v___y_2102_,
                    v___y_2103_,
                );
                if crate::leanh::lean_obj_tag(v___x_2105_) == 0 {
                    v_a_2106_ = crate::leanh::lean_ctor_get(v___x_2105_, 0);
                    v_isSharedCheck_2113_ = (!crate::leanh::lean_is_exclusive(v___x_2105_)) as u8;
                    if v_isSharedCheck_2113_ == 0 {
                        v___x_2108_ = v___x_2105_;
                        v_isShared_2109_ = v_isSharedCheck_2113_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2106_);
                        crate::leanh::lean_dec(v___x_2105_);
                        v___x_2108_ = crate::leanh::lean_box(0);
                        v_isShared_2109_ = v_isSharedCheck_2113_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_2114_ = crate::leanh::lean_ctor_get(v___x_2105_, 0);
                    v_isSharedCheck_2121_ = (!crate::leanh::lean_is_exclusive(v___x_2105_)) as u8;
                    if v_isSharedCheck_2121_ == 0 {
                        v___x_2116_ = v___x_2105_;
                        v_isShared_2117_ = v_isSharedCheck_2121_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2114_);
                        crate::leanh::lean_dec(v___x_2105_);
                        v___x_2116_ = crate::leanh::lean_box(0);
                        v_isShared_2117_ = v_isSharedCheck_2121_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_2109_ == 0 {
                    v___x_2111_ = v___x_2108_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2112_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2112_, 0, v_a_2106_);
                    v___x_2111_ = v_reuseFailAlloc_2112_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2111_;
            }
            3 => {
                if v_isShared_2117_ == 0 {
                    v___x_2119_ = v___x_2116_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2120_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2120_, 0, v_a_2114_);
                    v___x_2119_ = v_reuseFailAlloc_2120_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_2119_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_MVarId_withContext___at___00Lean_Meta_Grind_casesMatch_spec__3___redArg___boxed(
    mut v_mvarId_2122_: *mut crate::leanh::LeanObject,
    mut v_x_2123_: *mut crate::leanh::LeanObject,
    mut v___y_2124_: *mut crate::leanh::LeanObject,
    mut v___y_2125_: *mut crate::leanh::LeanObject,
    mut v___y_2126_: *mut crate::leanh::LeanObject,
    mut v___y_2127_: *mut crate::leanh::LeanObject,
    mut v___y_2128_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2129_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2129_ = l_Lean_MVarId_withContext___at___00Lean_Meta_Grind_casesMatch_spec__3___redArg(
        v_mvarId_2122_,
        v_x_2123_,
        v___y_2124_,
        v___y_2125_,
        v___y_2126_,
        v___y_2127_,
    );
    crate::leanh::lean_dec(v___y_2127_);
    crate::leanh::lean_dec_ref(v___y_2126_);
    crate::leanh::lean_dec(v___y_2125_);
    crate::leanh::lean_dec_ref(v___y_2124_);
    return v_res_2129_;
}
pub unsafe fn l_Lean_MVarId_withContext___at___00Lean_Meta_Grind_casesMatch_spec__3(
    mut v_00_u03b1_2130_: *mut crate::leanh::LeanObject,
    mut v_mvarId_2131_: *mut crate::leanh::LeanObject,
    mut v_x_2132_: *mut crate::leanh::LeanObject,
    mut v___y_2133_: *mut crate::leanh::LeanObject,
    mut v___y_2134_: *mut crate::leanh::LeanObject,
    mut v___y_2135_: *mut crate::leanh::LeanObject,
    mut v___y_2136_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2138_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2138_ = l_Lean_MVarId_withContext___at___00Lean_Meta_Grind_casesMatch_spec__3___redArg(
        v_mvarId_2131_,
        v_x_2132_,
        v___y_2133_,
        v___y_2134_,
        v___y_2135_,
        v___y_2136_,
    );
    return v___x_2138_;
}
pub unsafe fn l_Lean_MVarId_withContext___at___00Lean_Meta_Grind_casesMatch_spec__3___boxed(
    mut v_00_u03b1_2139_: *mut crate::leanh::LeanObject,
    mut v_mvarId_2140_: *mut crate::leanh::LeanObject,
    mut v_x_2141_: *mut crate::leanh::LeanObject,
    mut v___y_2142_: *mut crate::leanh::LeanObject,
    mut v___y_2143_: *mut crate::leanh::LeanObject,
    mut v___y_2144_: *mut crate::leanh::LeanObject,
    mut v___y_2145_: *mut crate::leanh::LeanObject,
    mut v___y_2146_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2147_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2147_ = l_Lean_MVarId_withContext___at___00Lean_Meta_Grind_casesMatch_spec__3(
        v_00_u03b1_2139_,
        v_mvarId_2140_,
        v_x_2141_,
        v___y_2142_,
        v___y_2143_,
        v___y_2144_,
        v___y_2145_,
    );
    crate::leanh::lean_dec(v___y_2145_);
    crate::leanh::lean_dec_ref(v___y_2144_);
    crate::leanh::lean_dec(v___y_2143_);
    crate::leanh::lean_dec_ref(v___y_2142_);
    return v_res_2147_;
}
pub unsafe fn l_List_mapTR_loop___at___00Lean_Meta_Grind_casesMatch_spec__2(
    mut v_a_2148_: *mut crate::leanh::LeanObject,
    mut v_a_2149_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2150_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_2151_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_2152_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2154_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2155_: u8 = 0;
    let mut v___x_2156_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2158_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2160_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2161_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_a_2148_) == 0 {
                    v___x_2150_ = l_List_reverse___redArg(v_a_2149_);
                    return v___x_2150_;
                } else {
                    v_head_2151_ = crate::leanh::lean_ctor_get(v_a_2148_, 0);
                    v_tail_2152_ = crate::leanh::lean_ctor_get(v_a_2148_, 1);
                    v_isSharedCheck_2161_ = (!crate::leanh::lean_is_exclusive(v_a_2148_)) as u8;
                    if v_isSharedCheck_2161_ == 0 {
                        v___x_2154_ = v_a_2148_;
                        v_isShared_2155_ = v_isSharedCheck_2161_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_tail_2152_);
                        crate::leanh::lean_inc(v_head_2151_);
                        crate::leanh::lean_dec(v_a_2148_);
                        v___x_2154_ = crate::leanh::lean_box(0);
                        v_isShared_2155_ = v_isSharedCheck_2161_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_2156_ = l_Lean_Expr_mvarId_x21(v_head_2151_);
                crate::leanh::lean_dec(v_head_2151_);
                if v_isShared_2155_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2154_, 1, v_a_2149_);
                    crate::leanh::lean_ctor_set(v___x_2154_, 0, v___x_2156_);
                    v___x_2158_ = v___x_2154_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2160_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2160_, 0, v___x_2156_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2160_, 1, v_a_2149_);
                    v___x_2158_ = v_reuseFailAlloc_2160_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_a_2148_ = v_tail_2152_;
                v_a_2149_ = v___x_2158_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Meta_Grind_casesMatch_spec__0_spec__0_spec__2_spec__7_spec__10_spec__12_spec__15___redArg___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2162_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2162_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
    );
    return v___x_2162_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Meta_Grind_casesMatch_spec__0_spec__0_spec__2_spec__7_spec__10_spec__12_spec__15___redArg___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2163_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2164_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2163_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Meta_Grind_casesMatch_spec__0_spec__0_spec__2_spec__7_spec__10_spec__12_spec__15___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Meta_Grind_casesMatch_spec__0_spec__0_spec__2_spec__7_spec__10_spec__12_spec__15___redArg___closed__0_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Meta_Grind_casesMatch_spec__0_spec__0_spec__2_spec__7_spec__10_spec__12_spec__15___redArg___closed__0);
    v___x_2164_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2164_, 0, v___x_2163_);
    return v___x_2164_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Meta_Grind_casesMatch_spec__0_spec__0_spec__2_spec__7_spec__10_spec__12_spec__15___redArg___closed__2()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2165_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2166_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2167_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2165_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Meta_Grind_casesMatch_spec__0_spec__0_spec__2_spec__7_spec__10_spec__12_spec__15___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Meta_Grind_casesMatch_spec__0_spec__0_spec__2_spec__7_spec__10_spec__12_spec__15___redArg___closed__1_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Meta_Grind_casesMatch_spec__0_spec__0_spec__2_spec__7_spec__10_spec__12_spec__15___redArg___closed__1);
    v___x_2166_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_2167_ = crate::leanh::lean_alloc_ctor(0, 10, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2167_, 0, v___x_2166_);
    crate::leanh::lean_ctor_set(v___x_2167_, 1, v___x_2166_);
    crate::leanh::lean_ctor_set(v___x_2167_, 2, v___x_2166_);
    crate::leanh::lean_ctor_set(v___x_2167_, 3, v___x_2166_);
    crate::leanh::lean_ctor_set(v___x_2167_, 4, v___x_2165_);
    crate::leanh::lean_ctor_set(v___x_2167_, 5, v___x_2165_);
    crate::leanh::lean_ctor_set(v___x_2167_, 6, v___x_2165_);
    crate::leanh::lean_ctor_set(v___x_2167_, 7, v___x_2165_);
    crate::leanh::lean_ctor_set(v___x_2167_, 8, v___x_2165_);
    crate::leanh::lean_ctor_set(v___x_2167_, 9, v___x_2165_);
    return v___x_2167_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Meta_Grind_casesMatch_spec__0_spec__0_spec__2_spec__7_spec__10_spec__12_spec__15___redArg___closed__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2168_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2169_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2170_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2168_ = crate::leanh::lean_unsigned_to_nat(32);
    v___x_2169_ = lean_mk_empty_array_with_capacity(v___x_2168_);
    v___x_2170_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2170_, 0, v___x_2169_);
    return v___x_2170_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Meta_Grind_casesMatch_spec__0_spec__0_spec__2_spec__7_spec__10_spec__12_spec__15___redArg___closed__4()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2171_: usize = 0;
    let mut v___x_2172_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2173_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2174_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2175_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2176_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2171_ = 5usize;
    v___x_2172_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_2173_ = crate::leanh::lean_unsigned_to_nat(32);
    v___x_2174_ = lean_mk_empty_array_with_capacity(v___x_2173_);
    v___x_2175_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Meta_Grind_casesMatch_spec__0_spec__0_spec__2_spec__7_spec__10_spec__12_spec__15___redArg___closed__3), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Meta_Grind_casesMatch_spec__0_spec__0_spec__2_spec__7_spec__10_spec__12_spec__15___redArg___closed__3_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Meta_Grind_casesMatch_spec__0_spec__0_spec__2_spec__7_spec__10_spec__12_spec__15___redArg___closed__3);
    v___x_2176_ = crate::leanh::lean_alloc_ctor(0, 4, (core::mem::size_of::<usize>() * 1) as u32);
    crate::leanh::lean_ctor_set(v___x_2176_, 0, v___x_2175_);
    crate::leanh::lean_ctor_set(v___x_2176_, 1, v___x_2174_);
    crate::leanh::lean_ctor_set(v___x_2176_, 2, v___x_2172_);
    crate::leanh::lean_ctor_set(v___x_2176_, 3, v___x_2172_);
    crate::leanh::lean_ctor_set_usize(v___x_2176_, 4, v___x_2171_);
    return v___x_2176_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Meta_Grind_casesMatch_spec__0_spec__0_spec__2_spec__7_spec__10_spec__12_spec__15___redArg___closed__5()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2177_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2178_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2179_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2180_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2177_ = crate::leanh::lean_box(1);
    v___x_2178_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Meta_Grind_casesMatch_spec__0_spec__0_spec__2_spec__7_spec__10_spec__12_spec__15___redArg___closed__4), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Meta_Grind_casesMatch_spec__0_spec__0_spec__2_spec__7_spec__10_spec__12_spec__15___redArg___closed__4_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Meta_Grind_casesMatch_spec__0_spec__0_spec__2_spec__7_spec__10_spec__12_spec__15___redArg___closed__4);
    v___x_2179_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Meta_Grind_casesMatch_spec__0_spec__0_spec__2_spec__7_spec__10_spec__12_spec__15___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Meta_Grind_casesMatch_spec__0_spec__0_spec__2_spec__7_spec__10_spec__12_spec__15___redArg___closed__1_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Meta_Grind_casesMatch_spec__0_spec__0_spec__2_spec__7_spec__10_spec__12_spec__15___redArg___closed__1);
    v___x_2180_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2180_, 0, v___x_2179_);
    crate::leanh::lean_ctor_set(v___x_2180_, 1, v___x_2178_);
    crate::leanh::lean_ctor_set(v___x_2180_, 2, v___x_2177_);
    return v___x_2180_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Meta_Grind_casesMatch_spec__0_spec__0_spec__2_spec__7_spec__10_spec__12_spec__15___redArg___closed__7()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2182_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2183_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2182_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Meta_Grind_casesMatch_spec__0_spec__0_spec__2_spec__7_spec__10_spec__12_spec__15___redArg___closed__6;
    v___x_2183_ = l_Lean_stringToMessageData(v___x_2182_);
    return v___x_2183_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Meta_Grind_casesMatch_spec__0_spec__0_spec__2_spec__7_spec__10_spec__12_spec__15___redArg___closed__9()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2185_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2186_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2185_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Meta_Grind_casesMatch_spec__0_spec__0_spec__2_spec__7_spec__10_spec__12_spec__15___redArg___closed__8;
    v___x_2186_ = l_Lean_stringToMessageData(v___x_2185_);
    return v___x_2186_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Meta_Grind_casesMatch_spec__0_spec__0_spec__2_spec__7_spec__10_spec__12_spec__15___redArg___closed__11()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2188_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2189_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2188_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Meta_Grind_casesMatch_spec__0_spec__0_spec__2_spec__7_spec__10_spec__12_spec__15___redArg___closed__10;
    v___x_2189_ = l_Lean_stringToMessageData(v___x_2188_);
    return v___x_2189_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Meta_Grind_casesMatch_spec__0_spec__0_spec__2_spec__7_spec__10_spec__12_spec__15___redArg___closed__13()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2191_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2192_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2191_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Meta_Grind_casesMatch_spec__0_spec__0_spec__2_spec__7_spec__10_spec__12_spec__15___redArg___closed__12;
    v___x_2192_ = l_Lean_stringToMessageData(v___x_2191_);
    return v___x_2192_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Meta_Grind_casesMatch_spec__0_spec__0_spec__2_spec__7_spec__10_spec__12_spec__15___redArg___closed__15()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2194_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2195_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2194_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Meta_Grind_casesMatch_spec__0_spec__0_spec__2_spec__7_spec__10_spec__12_spec__15___redArg___closed__14;
    v___x_2195_ = l_Lean_stringToMessageData(v___x_2194_);
    return v___x_2195_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Meta_Grind_casesMatch_spec__0_spec__0_spec__2_spec__7_spec__10_spec__12_spec__15___redArg___closed__17()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2197_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2198_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2197_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Meta_Grind_casesMatch_spec__0_spec__0_spec__2_spec__7_spec__10_spec__12_spec__15___redArg___closed__16;
    v___x_2198_ = l_Lean_stringToMessageData(v___x_2197_);
    return v___x_2198_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Meta_Grind_casesMatch_spec__0_spec__0_spec__2_spec__7_spec__10_spec__12_spec__15___redArg___closed__19()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2200_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2201_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2200_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Meta_Grind_casesMatch_spec__0_spec__0_spec__2_spec__7_spec__10_spec__12_spec__15___redArg___closed__18;
    v___x_2201_ = l_Lean_stringToMessageData(v___x_2200_);
    return v___x_2201_;
}
pub unsafe fn l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Meta_Grind_casesMatch_spec__0_spec__0_spec__2_spec__7_spec__10_spec__12_spec__15___redArg(
    mut v_msg_2202_: *mut crate::leanh::LeanObject,
    mut v_declHint_2203_: *mut crate::leanh::LeanObject,
    mut v___y_2204_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2206_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_2207_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2208_: u8 = 0;
    let mut v_isExporting_2209_: u8 = 0;
    let mut v___x_2210_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2211_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2212_: u8 = 0;
    let mut v___x_2213_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2214_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2215_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2216_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2217_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2218_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_c_2219_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2220_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2221_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2222_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2223_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2224_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2225_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2226_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2227_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2228_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2230_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2231_: u8 = 0;
    let mut v___x_2232_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2233_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2234_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mod_2235_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2236_: u8 = 0;
    let mut v___x_2237_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2238_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2239_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2240_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2241_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2242_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2243_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2244_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2245_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2246_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2248_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2249_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2250_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2251_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2252_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2253_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2254_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2255_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2256_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2257_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2258_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2259_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2261_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2262_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2263_: u8 = 0;
    let mut v___x_2264_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2206_ = lean_st_ref_get(v___y_2204_);
                v_env_2207_ = crate::leanh::lean_ctor_get(v___x_2206_, 0);
                crate::leanh::lean_inc_ref(v_env_2207_);
                crate::leanh::lean_dec(v___x_2206_);
                v___x_2208_ = l_Lean_Name_isAnonymous(v_declHint_2203_);
                if v___x_2208_ == 0 {
                    v_isExporting_2209_ = crate::leanh::lean_ctor_get_uint8(
                        v_env_2207_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 8) as u32,
                    );
                    if v_isExporting_2209_ == 0 {
                        crate::leanh::lean_dec_ref(v_env_2207_);
                        crate::leanh::lean_dec(v_declHint_2203_);
                        v___x_2210_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_2210_, 0, v_msg_2202_);
                        return v___x_2210_;
                    } else {
                        crate::leanh::lean_inc_ref(v_env_2207_);
                        v___x_2211_ = l_Lean_Environment_setExporting(v_env_2207_, v___x_2208_);
                        crate::leanh::lean_inc(v_declHint_2203_);
                        crate::leanh::lean_inc_ref(v___x_2211_);
                        v___x_2212_ = l_Lean_Environment_contains(
                            v___x_2211_,
                            v_declHint_2203_,
                            v_isExporting_2209_,
                        );
                        if v___x_2212_ == 0 {
                            crate::leanh::lean_dec_ref(v___x_2211_);
                            crate::leanh::lean_dec_ref(v_env_2207_);
                            crate::leanh::lean_dec(v_declHint_2203_);
                            v___x_2213_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_2213_, 0, v_msg_2202_);
                            return v___x_2213_;
                        } else {
                            v___x_2214_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Meta_Grind_casesMatch_spec__0_spec__0_spec__2_spec__7_spec__10_spec__12_spec__15___redArg___closed__2), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Meta_Grind_casesMatch_spec__0_spec__0_spec__2_spec__7_spec__10_spec__12_spec__15___redArg___closed__2_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Meta_Grind_casesMatch_spec__0_spec__0_spec__2_spec__7_spec__10_spec__12_spec__15___redArg___closed__2);
                            v___x_2215_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Meta_Grind_casesMatch_spec__0_spec__0_spec__2_spec__7_spec__10_spec__12_spec__15___redArg___closed__5), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Meta_Grind_casesMatch_spec__0_spec__0_spec__2_spec__7_spec__10_spec__12_spec__15___redArg___closed__5_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Meta_Grind_casesMatch_spec__0_spec__0_spec__2_spec__7_spec__10_spec__12_spec__15___redArg___closed__5);
                            v___x_2216_ = l_Lean_Options_empty;
                            v___x_2217_ = crate::leanh::lean_alloc_ctor(0, 4, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_2217_, 0, v___x_2211_);
                            crate::leanh::lean_ctor_set(v___x_2217_, 1, v___x_2214_);
                            crate::leanh::lean_ctor_set(v___x_2217_, 2, v___x_2215_);
                            crate::leanh::lean_ctor_set(v___x_2217_, 3, v___x_2216_);
                            crate::leanh::lean_inc(v_declHint_2203_);
                            v___x_2218_ =
                                l_Lean_MessageData_ofConstName(v_declHint_2203_, v___x_2208_);
                            v_c_2219_ = crate::leanh::lean_alloc_ctor(3, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v_c_2219_, 0, v___x_2217_);
                            crate::leanh::lean_ctor_set(v_c_2219_, 1, v___x_2218_);
                            v___x_2220_ = l_Lean_Environment_getModuleIdxFor_x3f(
                                v_env_2207_,
                                v_declHint_2203_,
                            );
                            if crate::leanh::lean_obj_tag(v___x_2220_) == 0 {
                                crate::leanh::lean_dec_ref(v_env_2207_);
                                crate::leanh::lean_dec(v_declHint_2203_);
                                v___x_2221_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Meta_Grind_casesMatch_spec__0_spec__0_spec__2_spec__7_spec__10_spec__12_spec__15___redArg___closed__7), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Meta_Grind_casesMatch_spec__0_spec__0_spec__2_spec__7_spec__10_spec__12_spec__15___redArg___closed__7_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Meta_Grind_casesMatch_spec__0_spec__0_spec__2_spec__7_spec__10_spec__12_spec__15___redArg___closed__7);
                                v___x_2222_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                                crate::leanh::lean_ctor_set(v___x_2222_, 0, v___x_2221_);
                                crate::leanh::lean_ctor_set(v___x_2222_, 1, v_c_2219_);
                                v___x_2223_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Meta_Grind_casesMatch_spec__0_spec__0_spec__2_spec__7_spec__10_spec__12_spec__15___redArg___closed__9), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Meta_Grind_casesMatch_spec__0_spec__0_spec__2_spec__7_spec__10_spec__12_spec__15___redArg___closed__9_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Meta_Grind_casesMatch_spec__0_spec__0_spec__2_spec__7_spec__10_spec__12_spec__15___redArg___closed__9);
                                v___x_2224_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                                crate::leanh::lean_ctor_set(v___x_2224_, 0, v___x_2222_);
                                crate::leanh::lean_ctor_set(v___x_2224_, 1, v___x_2223_);
                                v___x_2225_ = l_Lean_MessageData_note(v___x_2224_);
                                v___x_2226_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                                crate::leanh::lean_ctor_set(v___x_2226_, 0, v_msg_2202_);
                                crate::leanh::lean_ctor_set(v___x_2226_, 1, v___x_2225_);
                                v___x_2227_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                                crate::leanh::lean_ctor_set(v___x_2227_, 0, v___x_2226_);
                                return v___x_2227_;
                            } else {
                                v_val_2228_ = crate::leanh::lean_ctor_get(v___x_2220_, 0);
                                v_isSharedCheck_2263_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_2220_)) as u8;
                                if v_isSharedCheck_2263_ == 0 {
                                    v___x_2230_ = v___x_2220_;
                                    v_isShared_2231_ = v_isSharedCheck_2263_;
                                    state = 1;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_val_2228_);
                                    crate::leanh::lean_dec(v___x_2220_);
                                    v___x_2230_ = crate::leanh::lean_box(0);
                                    v_isShared_2231_ = v_isSharedCheck_2263_;
                                    state = 1;
                                    continue;
                                }
                            }
                        }
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_env_2207_);
                    crate::leanh::lean_dec(v_declHint_2203_);
                    v___x_2264_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2264_, 0, v_msg_2202_);
                    return v___x_2264_;
                }
            }
            1 => {
                v___x_2232_ = crate::leanh::lean_box(0);
                v___x_2233_ = l_Lean_Environment_header(v_env_2207_);
                crate::leanh::lean_dec_ref(v_env_2207_);
                v___x_2234_ = l_Lean_EnvironmentHeader_moduleNames(v___x_2233_);
                v_mod_2235_ = lean_array_get(v___x_2232_, v___x_2234_, v_val_2228_);
                crate::leanh::lean_dec(v_val_2228_);
                crate::leanh::lean_dec_ref(v___x_2234_);
                v___x_2236_ = l_Lean_isPrivateName(v_declHint_2203_);
                crate::leanh::lean_dec(v_declHint_2203_);
                if v___x_2236_ == 0 {
                    v___x_2237_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Meta_Grind_casesMatch_spec__0_spec__0_spec__2_spec__7_spec__10_spec__12_spec__15___redArg___closed__11), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Meta_Grind_casesMatch_spec__0_spec__0_spec__2_spec__7_spec__10_spec__12_spec__15___redArg___closed__11_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Meta_Grind_casesMatch_spec__0_spec__0_spec__2_spec__7_spec__10_spec__12_spec__15___redArg___closed__11);
                    v___x_2238_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2238_, 0, v___x_2237_);
                    crate::leanh::lean_ctor_set(v___x_2238_, 1, v_c_2219_);
                    v___x_2239_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Meta_Grind_casesMatch_spec__0_spec__0_spec__2_spec__7_spec__10_spec__12_spec__15___redArg___closed__13), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Meta_Grind_casesMatch_spec__0_spec__0_spec__2_spec__7_spec__10_spec__12_spec__15___redArg___closed__13_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Meta_Grind_casesMatch_spec__0_spec__0_spec__2_spec__7_spec__10_spec__12_spec__15___redArg___closed__13);
                    v___x_2240_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2240_, 0, v___x_2238_);
                    crate::leanh::lean_ctor_set(v___x_2240_, 1, v___x_2239_);
                    v___x_2241_ = l_Lean_MessageData_ofName(v_mod_2235_);
                    v___x_2242_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2242_, 0, v___x_2240_);
                    crate::leanh::lean_ctor_set(v___x_2242_, 1, v___x_2241_);
                    v___x_2243_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Meta_Grind_casesMatch_spec__0_spec__0_spec__2_spec__7_spec__10_spec__12_spec__15___redArg___closed__15), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Meta_Grind_casesMatch_spec__0_spec__0_spec__2_spec__7_spec__10_spec__12_spec__15___redArg___closed__15_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Meta_Grind_casesMatch_spec__0_spec__0_spec__2_spec__7_spec__10_spec__12_spec__15___redArg___closed__15);
                    v___x_2244_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2244_, 0, v___x_2242_);
                    crate::leanh::lean_ctor_set(v___x_2244_, 1, v___x_2243_);
                    v___x_2245_ = l_Lean_MessageData_note(v___x_2244_);
                    v___x_2246_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2246_, 0, v_msg_2202_);
                    crate::leanh::lean_ctor_set(v___x_2246_, 1, v___x_2245_);
                    if v_isShared_2231_ == 0 {
                        crate::leanh::lean_ctor_set_tag(v___x_2230_, 0);
                        crate::leanh::lean_ctor_set(v___x_2230_, 0, v___x_2246_);
                        v___x_2248_ = v___x_2230_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_2249_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2249_, 0, v___x_2246_);
                        v___x_2248_ = v_reuseFailAlloc_2249_;
                        state = 2;
                        continue;
                    }
                } else {
                    v___x_2250_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Meta_Grind_casesMatch_spec__0_spec__0_spec__2_spec__7_spec__10_spec__12_spec__15___redArg___closed__7), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Meta_Grind_casesMatch_spec__0_spec__0_spec__2_spec__7_spec__10_spec__12_spec__15___redArg___closed__7_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Meta_Grind_casesMatch_spec__0_spec__0_spec__2_spec__7_spec__10_spec__12_spec__15___redArg___closed__7);
                    v___x_2251_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2251_, 0, v___x_2250_);
                    crate::leanh::lean_ctor_set(v___x_2251_, 1, v_c_2219_);
                    v___x_2252_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Meta_Grind_casesMatch_spec__0_spec__0_spec__2_spec__7_spec__10_spec__12_spec__15___redArg___closed__17), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Meta_Grind_casesMatch_spec__0_spec__0_spec__2_spec__7_spec__10_spec__12_spec__15___redArg___closed__17_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Meta_Grind_casesMatch_spec__0_spec__0_spec__2_spec__7_spec__10_spec__12_spec__15___redArg___closed__17);
                    v___x_2253_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2253_, 0, v___x_2251_);
                    crate::leanh::lean_ctor_set(v___x_2253_, 1, v___x_2252_);
                    v___x_2254_ = l_Lean_MessageData_ofName(v_mod_2235_);
                    v___x_2255_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2255_, 0, v___x_2253_);
                    crate::leanh::lean_ctor_set(v___x_2255_, 1, v___x_2254_);
                    v___x_2256_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Meta_Grind_casesMatch_spec__0_spec__0_spec__2_spec__7_spec__10_spec__12_spec__15___redArg___closed__19), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Meta_Grind_casesMatch_spec__0_spec__0_spec__2_spec__7_spec__10_spec__12_spec__15___redArg___closed__19_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Meta_Grind_casesMatch_spec__0_spec__0_spec__2_spec__7_spec__10_spec__12_spec__15___redArg___closed__19);
                    v___x_2257_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2257_, 0, v___x_2255_);
                    crate::leanh::lean_ctor_set(v___x_2257_, 1, v___x_2256_);
                    v___x_2258_ = l_Lean_MessageData_note(v___x_2257_);
                    v___x_2259_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2259_, 0, v_msg_2202_);
                    crate::leanh::lean_ctor_set(v___x_2259_, 1, v___x_2258_);
                    if v_isShared_2231_ == 0 {
                        crate::leanh::lean_ctor_set_tag(v___x_2230_, 0);
                        crate::leanh::lean_ctor_set(v___x_2230_, 0, v___x_2259_);
                        v___x_2261_ = v___x_2230_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_2262_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2262_, 0, v___x_2259_);
                        v___x_2261_ = v_reuseFailAlloc_2262_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_2248_;
            }
            3 => {
                return v___x_2261_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Meta_Grind_casesMatch_spec__0_spec__0_spec__2_spec__7_spec__10_spec__12_spec__15___redArg___boxed(
    mut v_msg_2265_: *mut crate::leanh::LeanObject,
    mut v_declHint_2266_: *mut crate::leanh::LeanObject,
    mut v___y_2267_: *mut crate::leanh::LeanObject,
    mut v___y_2268_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2269_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2269_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Meta_Grind_casesMatch_spec__0_spec__0_spec__2_spec__7_spec__10_spec__12_spec__15___redArg(v_msg_2265_, v_declHint_2266_, v___y_2267_);
    crate::leanh::lean_dec(v___y_2267_);
    return v_res_2269_;
}
pub unsafe fn l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Meta_Grind_casesMatch_spec__0_spec__0_spec__2_spec__7_spec__10_spec__12(
    mut v_msg_2270_: *mut crate::leanh::LeanObject,
    mut v_declHint_2271_: *mut crate::leanh::LeanObject,
    mut v___y_2272_: *mut crate::leanh::LeanObject,
    mut v___y_2273_: *mut crate::leanh::LeanObject,
    mut v___y_2274_: *mut crate::leanh::LeanObject,
    mut v___y_2275_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2277_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2278_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2280_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2281_: u8 = 0;
    let mut v___x_2282_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2283_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2285_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2286_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2287_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2277_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Meta_Grind_casesMatch_spec__0_spec__0_spec__2_spec__7_spec__10_spec__12_spec__15___redArg(v_msg_2270_, v_declHint_2271_, v___y_2275_);
                v_a_2278_ = crate::leanh::lean_ctor_get(v___x_2277_, 0);
                v_isSharedCheck_2287_ = (!crate::leanh::lean_is_exclusive(v___x_2277_)) as u8;
                if v_isSharedCheck_2287_ == 0 {
                    v___x_2280_ = v___x_2277_;
                    v_isShared_2281_ = v_isSharedCheck_2287_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_a_2278_);
                    crate::leanh::lean_dec(v___x_2277_);
                    v___x_2280_ = crate::leanh::lean_box(0);
                    v_isShared_2281_ = v_isSharedCheck_2287_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_2282_ = l_Lean_unknownIdentifierMessageTag;
                v___x_2283_ = crate::leanh::lean_alloc_ctor(8, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2283_, 0, v___x_2282_);
                crate::leanh::lean_ctor_set(v___x_2283_, 1, v_a_2278_);
                if v_isShared_2281_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2280_, 0, v___x_2283_);
                    v___x_2285_ = v___x_2280_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2286_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2286_, 0, v___x_2283_);
                    v___x_2285_ = v_reuseFailAlloc_2286_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2285_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Meta_Grind_casesMatch_spec__0_spec__0_spec__2_spec__7_spec__10_spec__12___boxed(
    mut v_msg_2288_: *mut crate::leanh::LeanObject,
    mut v_declHint_2289_: *mut crate::leanh::LeanObject,
    mut v___y_2290_: *mut crate::leanh::LeanObject,
    mut v___y_2291_: *mut crate::leanh::LeanObject,
    mut v___y_2292_: *mut crate::leanh::LeanObject,
    mut v___y_2293_: *mut crate::leanh::LeanObject,
    mut v___y_2294_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2295_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2295_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Meta_Grind_casesMatch_spec__0_spec__0_spec__2_spec__7_spec__10_spec__12(v_msg_2288_, v_declHint_2289_, v___y_2290_, v___y_2291_, v___y_2292_, v___y_2293_);
    crate::leanh::lean_dec(v___y_2293_);
    crate::leanh::lean_dec_ref(v___y_2292_);
    crate::leanh::lean_dec(v___y_2291_);
    crate::leanh::lean_dec_ref(v___y_2290_);
    return v_res_2295_;
}
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Meta_Grind_casesMatch_spec__0_spec__0_spec__2_spec__7_spec__10_spec__13_spec__17_spec__19(
    mut v_msgData_2296_: *mut crate::leanh::LeanObject,
    mut v___y_2297_: *mut crate::leanh::LeanObject,
    mut v___y_2298_: *mut crate::leanh::LeanObject,
    mut v___y_2299_: *mut crate::leanh::LeanObject,
    mut v___y_2300_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2302_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_2303_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2304_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_2305_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_lctx_2306_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_2307_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2308_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2309_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2310_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2302_ = lean_st_ref_get(v___y_2300_);
    v_env_2303_ = crate::leanh::lean_ctor_get(v___x_2302_, 0);
    crate::leanh::lean_inc_ref(v_env_2303_);
    crate::leanh::lean_dec(v___x_2302_);
    v___x_2304_ = lean_st_ref_get(v___y_2298_);
    v_mctx_2305_ = crate::leanh::lean_ctor_get(v___x_2304_, 0);
    crate::leanh::lean_inc_ref(v_mctx_2305_);
    crate::leanh::lean_dec(v___x_2304_);
    v_lctx_2306_ = crate::leanh::lean_ctor_get(v___y_2297_, 2);
    v_options_2307_ = crate::leanh::lean_ctor_get(v___y_2299_, 2);
    crate::leanh::lean_inc_ref(v_options_2307_);
    crate::leanh::lean_inc_ref(v_lctx_2306_);
    v___x_2308_ = crate::leanh::lean_alloc_ctor(0, 4, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2308_, 0, v_env_2303_);
    crate::leanh::lean_ctor_set(v___x_2308_, 1, v_mctx_2305_);
    crate::leanh::lean_ctor_set(v___x_2308_, 2, v_lctx_2306_);
    crate::leanh::lean_ctor_set(v___x_2308_, 3, v_options_2307_);
    v___x_2309_ = crate::leanh::lean_alloc_ctor(3, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2309_, 0, v___x_2308_);
    crate::leanh::lean_ctor_set(v___x_2309_, 1, v_msgData_2296_);
    v___x_2310_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2310_, 0, v___x_2309_);
    return v___x_2310_;
}
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Meta_Grind_casesMatch_spec__0_spec__0_spec__2_spec__7_spec__10_spec__13_spec__17_spec__19___boxed(
    mut v_msgData_2311_: *mut crate::leanh::LeanObject,
    mut v___y_2312_: *mut crate::leanh::LeanObject,
    mut v___y_2313_: *mut crate::leanh::LeanObject,
    mut v___y_2314_: *mut crate::leanh::LeanObject,
    mut v___y_2315_: *mut crate::leanh::LeanObject,
    mut v___y_2316_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2317_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2317_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Meta_Grind_casesMatch_spec__0_spec__0_spec__2_spec__7_spec__10_spec__13_spec__17_spec__19(v_msgData_2311_, v___y_2312_, v___y_2313_, v___y_2314_, v___y_2315_);
    crate::leanh::lean_dec(v___y_2315_);
    crate::leanh::lean_dec_ref(v___y_2314_);
    crate::leanh::lean_dec(v___y_2313_);
    crate::leanh::lean_dec_ref(v___y_2312_);
    return v_res_2317_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Meta_Grind_casesMatch_spec__0_spec__0_spec__2_spec__7_spec__10_spec__13_spec__17___redArg(
    mut v_msg_2318_: *mut crate::leanh::LeanObject,
    mut v___y_2319_: *mut crate::leanh::LeanObject,
    mut v___y_2320_: *mut crate::leanh::LeanObject,
    mut v___y_2321_: *mut crate::leanh::LeanObject,
    mut v___y_2322_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_ref_2324_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2325_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2326_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2328_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2329_: u8 = 0;
    let mut v___x_2330_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2332_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2333_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2334_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ref_2324_ = crate::leanh::lean_ctor_get(v___y_2321_, 5);
                v___x_2325_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Meta_Grind_casesMatch_spec__0_spec__0_spec__2_spec__7_spec__10_spec__13_spec__17_spec__19(v_msg_2318_, v___y_2319_, v___y_2320_, v___y_2321_, v___y_2322_);
                v_a_2326_ = crate::leanh::lean_ctor_get(v___x_2325_, 0);
                v_isSharedCheck_2334_ = (!crate::leanh::lean_is_exclusive(v___x_2325_)) as u8;
                if v_isSharedCheck_2334_ == 0 {
                    v___x_2328_ = v___x_2325_;
                    v_isShared_2329_ = v_isSharedCheck_2334_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_a_2326_);
                    crate::leanh::lean_dec(v___x_2325_);
                    v___x_2328_ = crate::leanh::lean_box(0);
                    v_isShared_2329_ = v_isSharedCheck_2334_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                crate::leanh::lean_inc(v_ref_2324_);
                v___x_2330_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2330_, 0, v_ref_2324_);
                crate::leanh::lean_ctor_set(v___x_2330_, 1, v_a_2326_);
                if v_isShared_2329_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_2328_, 1);
                    crate::leanh::lean_ctor_set(v___x_2328_, 0, v___x_2330_);
                    v___x_2332_ = v___x_2328_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2333_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2333_, 0, v___x_2330_);
                    v___x_2332_ = v_reuseFailAlloc_2333_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2332_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Meta_Grind_casesMatch_spec__0_spec__0_spec__2_spec__7_spec__10_spec__13_spec__17___redArg___boxed(
    mut v_msg_2335_: *mut crate::leanh::LeanObject,
    mut v___y_2336_: *mut crate::leanh::LeanObject,
    mut v___y_2337_: *mut crate::leanh::LeanObject,
    mut v___y_2338_: *mut crate::leanh::LeanObject,
    mut v___y_2339_: *mut crate::leanh::LeanObject,
    mut v___y_2340_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2341_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2341_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Meta_Grind_casesMatch_spec__0_spec__0_spec__2_spec__7_spec__10_spec__13_spec__17___redArg(v_msg_2335_, v___y_2336_, v___y_2337_, v___y_2338_, v___y_2339_);
    crate::leanh::lean_dec(v___y_2339_);
    crate::leanh::lean_dec_ref(v___y_2338_);
    crate::leanh::lean_dec(v___y_2337_);
    crate::leanh::lean_dec_ref(v___y_2336_);
    return v_res_2341_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Meta_Grind_casesMatch_spec__0_spec__0_spec__2_spec__7_spec__10_spec__13___redArg(
    mut v_ref_2342_: *mut crate::leanh::LeanObject,
    mut v_msg_2343_: *mut crate::leanh::LeanObject,
    mut v___y_2344_: *mut crate::leanh::LeanObject,
    mut v___y_2345_: *mut crate::leanh::LeanObject,
    mut v___y_2346_: *mut crate::leanh::LeanObject,
    mut v___y_2347_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_fileName_2349_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fileMap_2350_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_2351_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_currRecDepth_2352_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_maxRecDepth_2353_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_2354_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_currNamespace_2355_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_openDecls_2356_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_initHeartbeats_2357_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_maxHeartbeats_2358_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_quotContext_2359_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_currMacroScope_2360_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_diag_2361_: u8 = 0;
    let mut v_cancelTk_x3f_2362_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_suppressElabErrors_2363_: u8 = 0;
    let mut v_inheritedTraceOptions_2364_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_2365_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2366_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2367_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_fileName_2349_ = crate::leanh::lean_ctor_get(v___y_2346_, 0);
    v_fileMap_2350_ = crate::leanh::lean_ctor_get(v___y_2346_, 1);
    v_options_2351_ = crate::leanh::lean_ctor_get(v___y_2346_, 2);
    v_currRecDepth_2352_ = crate::leanh::lean_ctor_get(v___y_2346_, 3);
    v_maxRecDepth_2353_ = crate::leanh::lean_ctor_get(v___y_2346_, 4);
    v_ref_2354_ = crate::leanh::lean_ctor_get(v___y_2346_, 5);
    v_currNamespace_2355_ = crate::leanh::lean_ctor_get(v___y_2346_, 6);
    v_openDecls_2356_ = crate::leanh::lean_ctor_get(v___y_2346_, 7);
    v_initHeartbeats_2357_ = crate::leanh::lean_ctor_get(v___y_2346_, 8);
    v_maxHeartbeats_2358_ = crate::leanh::lean_ctor_get(v___y_2346_, 9);
    v_quotContext_2359_ = crate::leanh::lean_ctor_get(v___y_2346_, 10);
    v_currMacroScope_2360_ = crate::leanh::lean_ctor_get(v___y_2346_, 11);
    v_diag_2361_ = crate::leanh::lean_ctor_get_uint8(
        v___y_2346_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 14) as u32,
    );
    v_cancelTk_x3f_2362_ = crate::leanh::lean_ctor_get(v___y_2346_, 12);
    v_suppressElabErrors_2363_ = crate::leanh::lean_ctor_get_uint8(
        v___y_2346_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 14 + 1) as u32,
    );
    v_inheritedTraceOptions_2364_ = crate::leanh::lean_ctor_get(v___y_2346_, 13);
    v_ref_2365_ = l_Lean_replaceRef(v_ref_2342_, v_ref_2354_);
    crate::leanh::lean_inc_ref(v_inheritedTraceOptions_2364_);
    crate::leanh::lean_inc(v_cancelTk_x3f_2362_);
    crate::leanh::lean_inc(v_currMacroScope_2360_);
    crate::leanh::lean_inc(v_quotContext_2359_);
    crate::leanh::lean_inc(v_maxHeartbeats_2358_);
    crate::leanh::lean_inc(v_initHeartbeats_2357_);
    crate::leanh::lean_inc(v_openDecls_2356_);
    crate::leanh::lean_inc(v_currNamespace_2355_);
    crate::leanh::lean_inc(v_maxRecDepth_2353_);
    crate::leanh::lean_inc(v_currRecDepth_2352_);
    crate::leanh::lean_inc_ref(v_options_2351_);
    crate::leanh::lean_inc_ref(v_fileMap_2350_);
    crate::leanh::lean_inc_ref(v_fileName_2349_);
    v___x_2366_ = crate::leanh::lean_alloc_ctor(0, 14, (2) as u32);
    crate::leanh::lean_ctor_set(v___x_2366_, 0, v_fileName_2349_);
    crate::leanh::lean_ctor_set(v___x_2366_, 1, v_fileMap_2350_);
    crate::leanh::lean_ctor_set(v___x_2366_, 2, v_options_2351_);
    crate::leanh::lean_ctor_set(v___x_2366_, 3, v_currRecDepth_2352_);
    crate::leanh::lean_ctor_set(v___x_2366_, 4, v_maxRecDepth_2353_);
    crate::leanh::lean_ctor_set(v___x_2366_, 5, v_ref_2365_);
    crate::leanh::lean_ctor_set(v___x_2366_, 6, v_currNamespace_2355_);
    crate::leanh::lean_ctor_set(v___x_2366_, 7, v_openDecls_2356_);
    crate::leanh::lean_ctor_set(v___x_2366_, 8, v_initHeartbeats_2357_);
    crate::leanh::lean_ctor_set(v___x_2366_, 9, v_maxHeartbeats_2358_);
    crate::leanh::lean_ctor_set(v___x_2366_, 10, v_quotContext_2359_);
    crate::leanh::lean_ctor_set(v___x_2366_, 11, v_currMacroScope_2360_);
    crate::leanh::lean_ctor_set(v___x_2366_, 12, v_cancelTk_x3f_2362_);
    crate::leanh::lean_ctor_set(v___x_2366_, 13, v_inheritedTraceOptions_2364_);
    crate::leanh::lean_ctor_set_uint8(
        v___x_2366_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 14) as u32,
        v_diag_2361_,
    );
    crate::leanh::lean_ctor_set_uint8(
        v___x_2366_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 14 + 1) as u32,
        v_suppressElabErrors_2363_,
    );
    v___x_2367_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Meta_Grind_casesMatch_spec__0_spec__0_spec__2_spec__7_spec__10_spec__13_spec__17___redArg(v_msg_2343_, v___y_2344_, v___y_2345_, v___x_2366_, v___y_2347_);
    crate::leanh::lean_dec_ref_known(v___x_2366_, 14);
    return v___x_2367_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Meta_Grind_casesMatch_spec__0_spec__0_spec__2_spec__7_spec__10_spec__13___redArg___boxed(
    mut v_ref_2368_: *mut crate::leanh::LeanObject,
    mut v_msg_2369_: *mut crate::leanh::LeanObject,
    mut v___y_2370_: *mut crate::leanh::LeanObject,
    mut v___y_2371_: *mut crate::leanh::LeanObject,
    mut v___y_2372_: *mut crate::leanh::LeanObject,
    mut v___y_2373_: *mut crate::leanh::LeanObject,
    mut v___y_2374_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2375_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2375_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Meta_Grind_casesMatch_spec__0_spec__0_spec__2_spec__7_spec__10_spec__13___redArg(v_ref_2368_, v_msg_2369_, v___y_2370_, v___y_2371_, v___y_2372_, v___y_2373_);
    crate::leanh::lean_dec(v___y_2373_);
    crate::leanh::lean_dec_ref(v___y_2372_);
    crate::leanh::lean_dec(v___y_2371_);
    crate::leanh::lean_dec_ref(v___y_2370_);
    crate::leanh::lean_dec(v_ref_2368_);
    return v_res_2375_;
}
pub unsafe fn l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Meta_Grind_casesMatch_spec__0_spec__0_spec__2_spec__7_spec__10___redArg(
    mut v_ref_2376_: *mut crate::leanh::LeanObject,
    mut v_msg_2377_: *mut crate::leanh::LeanObject,
    mut v_declHint_2378_: *mut crate::leanh::LeanObject,
    mut v___y_2379_: *mut crate::leanh::LeanObject,
    mut v___y_2380_: *mut crate::leanh::LeanObject,
    mut v___y_2381_: *mut crate::leanh::LeanObject,
    mut v___y_2382_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2384_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2385_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2386_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2384_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Meta_Grind_casesMatch_spec__0_spec__0_spec__2_spec__7_spec__10_spec__12(v_msg_2377_, v_declHint_2378_, v___y_2379_, v___y_2380_, v___y_2381_, v___y_2382_);
    v_a_2385_ = crate::leanh::lean_ctor_get(v___x_2384_, 0);
    crate::leanh::lean_inc(v_a_2385_);
    crate::leanh::lean_dec_ref(v___x_2384_);
    v___x_2386_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Meta_Grind_casesMatch_spec__0_spec__0_spec__2_spec__7_spec__10_spec__13___redArg(v_ref_2376_, v_a_2385_, v___y_2379_, v___y_2380_, v___y_2381_, v___y_2382_);
    return v___x_2386_;
}
pub unsafe fn l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Meta_Grind_casesMatch_spec__0_spec__0_spec__2_spec__7_spec__10___redArg___boxed(
    mut v_ref_2387_: *mut crate::leanh::LeanObject,
    mut v_msg_2388_: *mut crate::leanh::LeanObject,
    mut v_declHint_2389_: *mut crate::leanh::LeanObject,
    mut v___y_2390_: *mut crate::leanh::LeanObject,
    mut v___y_2391_: *mut crate::leanh::LeanObject,
    mut v___y_2392_: *mut crate::leanh::LeanObject,
    mut v___y_2393_: *mut crate::leanh::LeanObject,
    mut v___y_2394_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2395_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2395_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Meta_Grind_casesMatch_spec__0_spec__0_spec__2_spec__7_spec__10___redArg(v_ref_2387_, v_msg_2388_, v_declHint_2389_, v___y_2390_, v___y_2391_, v___y_2392_, v___y_2393_);
    crate::leanh::lean_dec(v___y_2393_);
    crate::leanh::lean_dec_ref(v___y_2392_);
    crate::leanh::lean_dec(v___y_2391_);
    crate::leanh::lean_dec_ref(v___y_2390_);
    crate::leanh::lean_dec(v_ref_2387_);
    return v_res_2395_;
}
pub unsafe fn _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Meta_Grind_casesMatch_spec__0_spec__0_spec__2_spec__7___redArg___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2397_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2398_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2397_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Meta_Grind_casesMatch_spec__0_spec__0_spec__2_spec__7___redArg___closed__0;
    v___x_2398_ = l_Lean_stringToMessageData(v___x_2397_);
    return v___x_2398_;
}
pub unsafe fn _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Meta_Grind_casesMatch_spec__0_spec__0_spec__2_spec__7___redArg___closed__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2400_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2401_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2400_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Meta_Grind_casesMatch_spec__0_spec__0_spec__2_spec__7___redArg___closed__2;
    v___x_2401_ = l_Lean_stringToMessageData(v___x_2400_);
    return v___x_2401_;
}
pub unsafe fn l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Meta_Grind_casesMatch_spec__0_spec__0_spec__2_spec__7___redArg(
    mut v_ref_2402_: *mut crate::leanh::LeanObject,
    mut v_constName_2403_: *mut crate::leanh::LeanObject,
    mut v___y_2404_: *mut crate::leanh::LeanObject,
    mut v___y_2405_: *mut crate::leanh::LeanObject,
    mut v___y_2406_: *mut crate::leanh::LeanObject,
    mut v___y_2407_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2409_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2410_: u8 = 0;
    let mut v___x_2411_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2412_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2413_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2414_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2415_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2409_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Meta_Grind_casesMatch_spec__0_spec__0_spec__2_spec__7___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Meta_Grind_casesMatch_spec__0_spec__0_spec__2_spec__7___redArg___closed__1_once), _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Meta_Grind_casesMatch_spec__0_spec__0_spec__2_spec__7___redArg___closed__1);
    v___x_2410_ = 0;
    crate::leanh::lean_inc(v_constName_2403_);
    v___x_2411_ = l_Lean_MessageData_ofConstName(v_constName_2403_, v___x_2410_);
    v___x_2412_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2412_, 0, v___x_2409_);
    crate::leanh::lean_ctor_set(v___x_2412_, 1, v___x_2411_);
    v___x_2413_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Meta_Grind_casesMatch_spec__0_spec__0_spec__2_spec__7___redArg___closed__3), core::ptr::addr_of_mut!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Meta_Grind_casesMatch_spec__0_spec__0_spec__2_spec__7___redArg___closed__3_once), _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Meta_Grind_casesMatch_spec__0_spec__0_spec__2_spec__7___redArg___closed__3);
    v___x_2414_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2414_, 0, v___x_2412_);
    crate::leanh::lean_ctor_set(v___x_2414_, 1, v___x_2413_);
    v___x_2415_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Meta_Grind_casesMatch_spec__0_spec__0_spec__2_spec__7_spec__10___redArg(v_ref_2402_, v___x_2414_, v_constName_2403_, v___y_2404_, v___y_2405_, v___y_2406_, v___y_2407_);
    return v___x_2415_;
}
pub unsafe fn l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Meta_Grind_casesMatch_spec__0_spec__0_spec__2_spec__7___redArg___boxed(
    mut v_ref_2416_: *mut crate::leanh::LeanObject,
    mut v_constName_2417_: *mut crate::leanh::LeanObject,
    mut v___y_2418_: *mut crate::leanh::LeanObject,
    mut v___y_2419_: *mut crate::leanh::LeanObject,
    mut v___y_2420_: *mut crate::leanh::LeanObject,
    mut v___y_2421_: *mut crate::leanh::LeanObject,
    mut v___y_2422_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2423_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2423_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Meta_Grind_casesMatch_spec__0_spec__0_spec__2_spec__7___redArg(v_ref_2416_, v_constName_2417_, v___y_2418_, v___y_2419_, v___y_2420_, v___y_2421_);
    crate::leanh::lean_dec(v___y_2421_);
    crate::leanh::lean_dec_ref(v___y_2420_);
    crate::leanh::lean_dec(v___y_2419_);
    crate::leanh::lean_dec_ref(v___y_2418_);
    crate::leanh::lean_dec(v_ref_2416_);
    return v_res_2423_;
}
pub unsafe fn l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Meta_Grind_casesMatch_spec__0_spec__0_spec__2___redArg(
    mut v_constName_2424_: *mut crate::leanh::LeanObject,
    mut v___y_2425_: *mut crate::leanh::LeanObject,
    mut v___y_2426_: *mut crate::leanh::LeanObject,
    mut v___y_2427_: *mut crate::leanh::LeanObject,
    mut v___y_2428_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_ref_2430_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2431_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_ref_2430_ = crate::leanh::lean_ctor_get(v___y_2427_, 5);
    v___x_2431_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Meta_Grind_casesMatch_spec__0_spec__0_spec__2_spec__7___redArg(v_ref_2430_, v_constName_2424_, v___y_2425_, v___y_2426_, v___y_2427_, v___y_2428_);
    return v___x_2431_;
}
pub unsafe fn l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Meta_Grind_casesMatch_spec__0_spec__0_spec__2___redArg___boxed(
    mut v_constName_2432_: *mut crate::leanh::LeanObject,
    mut v___y_2433_: *mut crate::leanh::LeanObject,
    mut v___y_2434_: *mut crate::leanh::LeanObject,
    mut v___y_2435_: *mut crate::leanh::LeanObject,
    mut v___y_2436_: *mut crate::leanh::LeanObject,
    mut v___y_2437_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2438_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2438_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Meta_Grind_casesMatch_spec__0_spec__0_spec__2___redArg(v_constName_2432_, v___y_2433_, v___y_2434_, v___y_2435_, v___y_2436_);
    crate::leanh::lean_dec(v___y_2436_);
    crate::leanh::lean_dec_ref(v___y_2435_);
    crate::leanh::lean_dec(v___y_2434_);
    crate::leanh::lean_dec_ref(v___y_2433_);
    return v_res_2438_;
}
pub unsafe fn l_Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Meta_Grind_casesMatch_spec__0_spec__0(
    mut v_constName_2439_: *mut crate::leanh::LeanObject,
    mut v___y_2440_: *mut crate::leanh::LeanObject,
    mut v___y_2441_: *mut crate::leanh::LeanObject,
    mut v___y_2442_: *mut crate::leanh::LeanObject,
    mut v___y_2443_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2445_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_2446_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2447_: u8 = 0;
    let mut v___x_2448_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2449_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2450_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2452_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2453_: u8 = 0;
    let mut v___x_2455_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2456_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2457_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2445_ = lean_st_ref_get(v___y_2443_);
                v_env_2446_ = crate::leanh::lean_ctor_get(v___x_2445_, 0);
                crate::leanh::lean_inc_ref(v_env_2446_);
                crate::leanh::lean_dec(v___x_2445_);
                v___x_2447_ = 0;
                crate::leanh::lean_inc(v_constName_2439_);
                v___x_2448_ =
                    l_Lean_Environment_find_x3f(v_env_2446_, v_constName_2439_, v___x_2447_);
                if crate::leanh::lean_obj_tag(v___x_2448_) == 0 {
                    v___x_2449_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Meta_Grind_casesMatch_spec__0_spec__0_spec__2___redArg(v_constName_2439_, v___y_2440_, v___y_2441_, v___y_2442_, v___y_2443_);
                    return v___x_2449_;
                } else {
                    crate::leanh::lean_dec(v_constName_2439_);
                    v_val_2450_ = crate::leanh::lean_ctor_get(v___x_2448_, 0);
                    v_isSharedCheck_2457_ = (!crate::leanh::lean_is_exclusive(v___x_2448_)) as u8;
                    if v_isSharedCheck_2457_ == 0 {
                        v___x_2452_ = v___x_2448_;
                        v_isShared_2453_ = v_isSharedCheck_2457_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_val_2450_);
                        crate::leanh::lean_dec(v___x_2448_);
                        v___x_2452_ = crate::leanh::lean_box(0);
                        v_isShared_2453_ = v_isSharedCheck_2457_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_2453_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_2452_, 0);
                    v___x_2455_ = v___x_2452_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2456_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2456_, 0, v_val_2450_);
                    v___x_2455_ = v_reuseFailAlloc_2456_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2455_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Meta_Grind_casesMatch_spec__0_spec__0___boxed(
    mut v_constName_2458_: *mut crate::leanh::LeanObject,
    mut v___y_2459_: *mut crate::leanh::LeanObject,
    mut v___y_2460_: *mut crate::leanh::LeanObject,
    mut v___y_2461_: *mut crate::leanh::LeanObject,
    mut v___y_2462_: *mut crate::leanh::LeanObject,
    mut v___y_2463_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2464_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2464_ = l_Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Meta_Grind_casesMatch_spec__0_spec__0(v_constName_2458_, v___y_2459_, v___y_2460_, v___y_2461_, v___y_2462_);
    crate::leanh::lean_dec(v___y_2462_);
    crate::leanh::lean_dec_ref(v___y_2461_);
    crate::leanh::lean_dec(v___y_2460_);
    crate::leanh::lean_dec_ref(v___y_2459_);
    return v_res_2464_;
}
pub unsafe fn l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Meta_Grind_casesMatch_spec__0_spec__2___redArg(
    mut v_declName_2465_: *mut crate::leanh::LeanObject,
    mut v___y_2466_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2468_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_2469_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2470_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2471_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2468_ = lean_st_ref_get(v___y_2466_);
    v_env_2469_ = crate::leanh::lean_ctor_get(v___x_2468_, 0);
    crate::leanh::lean_inc_ref(v_env_2469_);
    crate::leanh::lean_dec(v___x_2468_);
    v___x_2470_ = l_Lean_Meta_Match_Extension_getMatcherInfo_x3f(v_env_2469_, v_declName_2465_);
    v___x_2471_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2471_, 0, v___x_2470_);
    return v___x_2471_;
}
pub unsafe fn l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Meta_Grind_casesMatch_spec__0_spec__2___redArg___boxed(
    mut v_declName_2472_: *mut crate::leanh::LeanObject,
    mut v___y_2473_: *mut crate::leanh::LeanObject,
    mut v___y_2474_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2475_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2475_ = l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Meta_Grind_casesMatch_spec__0_spec__2___redArg(v_declName_2472_, v___y_2473_);
    crate::leanh::lean_dec(v___y_2473_);
    return v_res_2475_;
}
pub unsafe fn _init_l_panic___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Meta_Grind_casesMatch_spec__0_spec__1___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2476_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2476_ = l_instMonadEIO(crate::leanh::lean_box(0));
    return v___x_2476_;
}
pub unsafe fn l_panic___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Meta_Grind_casesMatch_spec__0_spec__1(
    mut v_msg_2481_: *mut crate::leanh::LeanObject,
    mut v___y_2482_: *mut crate::leanh::LeanObject,
    mut v___y_2483_: *mut crate::leanh::LeanObject,
    mut v___y_2484_: *mut crate::leanh::LeanObject,
    mut v___y_2485_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2487_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2488_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toApplicative_2489_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2491_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2492_: u8 = 0;
    let mut v_toFunctor_2493_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeq_2494_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeqLeft_2495_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeqRight_2496_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2498_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2499_: u8 = 0;
    let mut v___f_2500_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2501_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2502_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2503_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2504_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2505_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2506_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2507_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2509_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2511_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2512_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toApplicative_2513_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2515_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2516_: u8 = 0;
    let mut v_toFunctor_2517_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeq_2518_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeqLeft_2519_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeqRight_2520_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2522_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2523_: u8 = 0;
    let mut v___f_2524_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2525_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2526_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2527_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2528_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2529_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2530_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2531_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2533_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2535_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2536_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2537_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4013__overap_2538_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2539_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2540_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2541_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2542_: u8 = 0;
    let mut v_unused_2543_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2544_: u8 = 0;
    let mut v_unused_2545_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2546_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2547_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2548_: u8 = 0;
    let mut v_unused_2549_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2550_: u8 = 0;
    let mut v_unused_2551_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2487_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_panic___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Meta_Grind_casesMatch_spec__0_spec__1___closed__0), core::ptr::addr_of_mut!(l_panic___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Meta_Grind_casesMatch_spec__0_spec__1___closed__0_once), _init_l_panic___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Meta_Grind_casesMatch_spec__0_spec__1___closed__0);
                v___x_2488_ = l_StateRefT_x27_instMonad___redArg(v___x_2487_);
                v_toApplicative_2489_ = crate::leanh::lean_ctor_get(v___x_2488_, 0);
                v_isSharedCheck_2550_ = (!crate::leanh::lean_is_exclusive(v___x_2488_)) as u8;
                if v_isSharedCheck_2550_ == 0 {
                    v_unused_2551_ = crate::leanh::lean_ctor_get(v___x_2488_, 1);
                    crate::leanh::lean_dec(v_unused_2551_);
                    v___x_2491_ = v___x_2488_;
                    v_isShared_2492_ = v_isSharedCheck_2550_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_toApplicative_2489_);
                    crate::leanh::lean_dec(v___x_2488_);
                    v___x_2491_ = crate::leanh::lean_box(0);
                    v_isShared_2492_ = v_isSharedCheck_2550_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_toFunctor_2493_ = crate::leanh::lean_ctor_get(v_toApplicative_2489_, 0);
                v_toSeq_2494_ = crate::leanh::lean_ctor_get(v_toApplicative_2489_, 2);
                v_toSeqLeft_2495_ = crate::leanh::lean_ctor_get(v_toApplicative_2489_, 3);
                v_toSeqRight_2496_ = crate::leanh::lean_ctor_get(v_toApplicative_2489_, 4);
                v_isSharedCheck_2548_ =
                    (!crate::leanh::lean_is_exclusive(v_toApplicative_2489_)) as u8;
                if v_isSharedCheck_2548_ == 0 {
                    v_unused_2549_ = crate::leanh::lean_ctor_get(v_toApplicative_2489_, 1);
                    crate::leanh::lean_dec(v_unused_2549_);
                    v___x_2498_ = v_toApplicative_2489_;
                    v_isShared_2499_ = v_isSharedCheck_2548_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_toSeqRight_2496_);
                    crate::leanh::lean_inc(v_toSeqLeft_2495_);
                    crate::leanh::lean_inc(v_toSeq_2494_);
                    crate::leanh::lean_inc(v_toFunctor_2493_);
                    crate::leanh::lean_dec(v_toApplicative_2489_);
                    v___x_2498_ = crate::leanh::lean_box(0);
                    v_isShared_2499_ = v_isSharedCheck_2548_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___f_2500_ = l_panic___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Meta_Grind_casesMatch_spec__0_spec__1___closed__1;
                v___f_2501_ = l_panic___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Meta_Grind_casesMatch_spec__0_spec__1___closed__2;
                crate::leanh::lean_inc_ref(v_toFunctor_2493_);
                v___f_2502_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__0 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_2502_, 0, v_toFunctor_2493_);
                v___f_2503_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_2503_, 0, v_toFunctor_2493_);
                v___x_2504_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2504_, 0, v___f_2502_);
                crate::leanh::lean_ctor_set(v___x_2504_, 1, v___f_2503_);
                v___f_2505_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_2505_, 0, v_toSeqRight_2496_);
                v___f_2506_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__3 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_2506_, 0, v_toSeqLeft_2495_);
                v___f_2507_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__4 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_2507_, 0, v_toSeq_2494_);
                if v_isShared_2499_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2498_, 4, v___f_2505_);
                    crate::leanh::lean_ctor_set(v___x_2498_, 3, v___f_2506_);
                    crate::leanh::lean_ctor_set(v___x_2498_, 2, v___f_2507_);
                    crate::leanh::lean_ctor_set(v___x_2498_, 1, v___f_2500_);
                    crate::leanh::lean_ctor_set(v___x_2498_, 0, v___x_2504_);
                    v___x_2509_ = v___x_2498_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2547_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2547_, 0, v___x_2504_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2547_, 1, v___f_2500_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2547_, 2, v___f_2507_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2547_, 3, v___f_2506_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2547_, 4, v___f_2505_);
                    v___x_2509_ = v_reuseFailAlloc_2547_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_2492_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2491_, 1, v___f_2501_);
                    crate::leanh::lean_ctor_set(v___x_2491_, 0, v___x_2509_);
                    v___x_2511_ = v___x_2491_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2546_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2546_, 0, v___x_2509_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2546_, 1, v___f_2501_);
                    v___x_2511_ = v_reuseFailAlloc_2546_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_2512_ = l_StateRefT_x27_instMonad___redArg(v___x_2511_);
                v_toApplicative_2513_ = crate::leanh::lean_ctor_get(v___x_2512_, 0);
                v_isSharedCheck_2544_ = (!crate::leanh::lean_is_exclusive(v___x_2512_)) as u8;
                if v_isSharedCheck_2544_ == 0 {
                    v_unused_2545_ = crate::leanh::lean_ctor_get(v___x_2512_, 1);
                    crate::leanh::lean_dec(v_unused_2545_);
                    v___x_2515_ = v___x_2512_;
                    v_isShared_2516_ = v_isSharedCheck_2544_;
                    state = 5;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_toApplicative_2513_);
                    crate::leanh::lean_dec(v___x_2512_);
                    v___x_2515_ = crate::leanh::lean_box(0);
                    v_isShared_2516_ = v_isSharedCheck_2544_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v_toFunctor_2517_ = crate::leanh::lean_ctor_get(v_toApplicative_2513_, 0);
                v_toSeq_2518_ = crate::leanh::lean_ctor_get(v_toApplicative_2513_, 2);
                v_toSeqLeft_2519_ = crate::leanh::lean_ctor_get(v_toApplicative_2513_, 3);
                v_toSeqRight_2520_ = crate::leanh::lean_ctor_get(v_toApplicative_2513_, 4);
                v_isSharedCheck_2542_ =
                    (!crate::leanh::lean_is_exclusive(v_toApplicative_2513_)) as u8;
                if v_isSharedCheck_2542_ == 0 {
                    v_unused_2543_ = crate::leanh::lean_ctor_get(v_toApplicative_2513_, 1);
                    crate::leanh::lean_dec(v_unused_2543_);
                    v___x_2522_ = v_toApplicative_2513_;
                    v_isShared_2523_ = v_isSharedCheck_2542_;
                    state = 6;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_toSeqRight_2520_);
                    crate::leanh::lean_inc(v_toSeqLeft_2519_);
                    crate::leanh::lean_inc(v_toSeq_2518_);
                    crate::leanh::lean_inc(v_toFunctor_2517_);
                    crate::leanh::lean_dec(v_toApplicative_2513_);
                    v___x_2522_ = crate::leanh::lean_box(0);
                    v_isShared_2523_ = v_isSharedCheck_2542_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                v___f_2524_ = l_panic___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Meta_Grind_casesMatch_spec__0_spec__1___closed__3;
                v___f_2525_ = l_panic___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Meta_Grind_casesMatch_spec__0_spec__1___closed__4;
                crate::leanh::lean_inc_ref(v_toFunctor_2517_);
                v___f_2526_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__0 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_2526_, 0, v_toFunctor_2517_);
                v___f_2527_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_2527_, 0, v_toFunctor_2517_);
                v___x_2528_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2528_, 0, v___f_2526_);
                crate::leanh::lean_ctor_set(v___x_2528_, 1, v___f_2527_);
                v___f_2529_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_2529_, 0, v_toSeqRight_2520_);
                v___f_2530_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__3 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_2530_, 0, v_toSeqLeft_2519_);
                v___f_2531_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__4 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_2531_, 0, v_toSeq_2518_);
                if v_isShared_2523_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2522_, 4, v___f_2529_);
                    crate::leanh::lean_ctor_set(v___x_2522_, 3, v___f_2530_);
                    crate::leanh::lean_ctor_set(v___x_2522_, 2, v___f_2531_);
                    crate::leanh::lean_ctor_set(v___x_2522_, 1, v___f_2524_);
                    crate::leanh::lean_ctor_set(v___x_2522_, 0, v___x_2528_);
                    v___x_2533_ = v___x_2522_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_2541_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2541_, 0, v___x_2528_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2541_, 1, v___f_2524_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2541_, 2, v___f_2531_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2541_, 3, v___f_2530_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2541_, 4, v___f_2529_);
                    v___x_2533_ = v_reuseFailAlloc_2541_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                if v_isShared_2516_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2515_, 1, v___f_2525_);
                    crate::leanh::lean_ctor_set(v___x_2515_, 0, v___x_2533_);
                    v___x_2535_ = v___x_2515_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_2540_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2540_, 0, v___x_2533_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2540_, 1, v___f_2525_);
                    v___x_2535_ = v_reuseFailAlloc_2540_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                v___x_2536_ = l_Lean_Meta_Match_instInhabitedAltParamInfo_default;
                v___x_2537_ = l_instInhabitedOfMonad___redArg(v___x_2535_, v___x_2536_);
                v___x_4013__overap_2538_ = lean_panic_fn_borrowed(v___x_2537_, v_msg_2481_);
                crate::leanh::lean_dec(v___x_2537_);
                crate::leanh::lean_inc(v___y_2485_);
                crate::leanh::lean_inc_ref(v___y_2484_);
                crate::leanh::lean_inc(v___y_2483_);
                crate::leanh::lean_inc_ref(v___y_2482_);
                v___x_2539_ = crate::leanh::lean_apply_5(
                    v___x_4013__overap_2538_,
                    v___y_2482_,
                    v___y_2483_,
                    v___y_2484_,
                    v___y_2485_,
                    crate::leanh::lean_box(0),
                );
                return v___x_2539_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_panic___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Meta_Grind_casesMatch_spec__0_spec__1___boxed(
    mut v_msg_2552_: *mut crate::leanh::LeanObject,
    mut v___y_2553_: *mut crate::leanh::LeanObject,
    mut v___y_2554_: *mut crate::leanh::LeanObject,
    mut v___y_2555_: *mut crate::leanh::LeanObject,
    mut v___y_2556_: *mut crate::leanh::LeanObject,
    mut v___y_2557_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2558_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2558_ = l_panic___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Meta_Grind_casesMatch_spec__0_spec__1(v_msg_2552_, v___y_2553_, v___y_2554_, v___y_2555_, v___y_2556_);
    crate::leanh::lean_dec(v___y_2556_);
    crate::leanh::lean_dec_ref(v___y_2555_);
    crate::leanh::lean_dec(v___y_2554_);
    crate::leanh::lean_dec_ref(v___y_2553_);
    return v_res_2558_;
}
pub unsafe fn _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Meta_Grind_casesMatch_spec__0_spec__3___closed__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2562_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2563_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2564_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2565_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2566_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2567_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2562_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Meta_Grind_casesMatch_spec__0_spec__3___closed__2;
    v___x_2563_ = crate::leanh::lean_unsigned_to_nat(53);
    v___x_2564_ = crate::leanh::lean_unsigned_to_nat(62);
    v___x_2565_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Meta_Grind_casesMatch_spec__0_spec__3___closed__1;
    v___x_2566_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Meta_Grind_casesMatch_spec__0_spec__3___closed__0;
    v___x_2567_ = l_mkPanicMessageWithDecl(
        v___x_2566_,
        v___x_2565_,
        v___x_2564_,
        v___x_2563_,
        v___x_2562_,
    );
    return v___x_2567_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Meta_Grind_casesMatch_spec__0_spec__3(
    mut v_sz_2568_: usize,
    mut v_i_2569_: usize,
    mut v_bs_2570_: *mut crate::leanh::LeanObject,
    mut v___y_2571_: *mut crate::leanh::LeanObject,
    mut v___y_2572_: *mut crate::leanh::LeanObject,
    mut v___y_2573_: *mut crate::leanh::LeanObject,
    mut v___y_2574_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2576_: u8 = 0;
    let mut v___x_2577_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_2578_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2579_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2580_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2581_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_2582_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2584_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2585_: usize = 0;
    let mut v___x_2586_: usize = 0;
    let mut v___x_2587_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2589_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_numFields_2590_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2591_: u8 = 0;
    let mut v___x_2592_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2593_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2594_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2595_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2596_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2598_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2599_: u8 = 0;
    let mut v___x_2601_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2602_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2603_: u8 = 0;
    let mut v_a_2604_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2606_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2607_: u8 = 0;
    let mut v___x_2609_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2610_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2611_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2576_ = lean_usize_dec_lt(v_i_2569_, v_sz_2568_);
                if v___x_2576_ == 0 {
                    v___x_2577_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2577_, 0, v_bs_2570_);
                    return v___x_2577_;
                } else {
                    v_v_2578_ = lean_array_uget_borrowed(v_bs_2570_, v_i_2569_);
                    crate::leanh::lean_inc(v_v_2578_);
                    v___x_2579_ = l_Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Meta_Grind_casesMatch_spec__0_spec__0(v_v_2578_, v___y_2571_, v___y_2572_, v___y_2573_, v___y_2574_);
                    if crate::leanh::lean_obj_tag(v___x_2579_) == 0 {
                        v_a_2580_ = crate::leanh::lean_ctor_get(v___x_2579_, 0);
                        crate::leanh::lean_inc(v_a_2580_);
                        crate::leanh::lean_dec_ref_known(v___x_2579_, 1);
                        v___x_2581_ = crate::leanh::lean_unsigned_to_nat(0);
                        v_bs_x27_2582_ = lean_array_uset(v_bs_2570_, v_i_2569_, v___x_2581_);
                        if crate::leanh::lean_obj_tag(v_a_2580_) == 6 {
                            v_val_2589_ = crate::leanh::lean_ctor_get(v_a_2580_, 0);
                            crate::leanh::lean_inc_ref(v_val_2589_);
                            crate::leanh::lean_dec_ref_known(v_a_2580_, 1);
                            v_numFields_2590_ = crate::leanh::lean_ctor_get(v_val_2589_, 4);
                            crate::leanh::lean_inc(v_numFields_2590_);
                            crate::leanh::lean_dec_ref(v_val_2589_);
                            v___x_2591_ = 0;
                            v___x_2592_ = crate::leanh::lean_alloc_ctor(0, 2, (1) as u32);
                            crate::leanh::lean_ctor_set(v___x_2592_, 0, v_numFields_2590_);
                            crate::leanh::lean_ctor_set(v___x_2592_, 1, v___x_2581_);
                            crate::leanh::lean_ctor_set_uint8(
                                v___x_2592_,
                                (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2) as u32,
                                v___x_2591_,
                            );
                            v_a_2584_ = v___x_2592_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_dec(v_a_2580_);
                            v___x_2593_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Meta_Grind_casesMatch_spec__0_spec__3___closed__3), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Meta_Grind_casesMatch_spec__0_spec__3___closed__3_once), _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Meta_Grind_casesMatch_spec__0_spec__3___closed__3);
                            v___x_2594_ = l_panic___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Meta_Grind_casesMatch_spec__0_spec__1(v___x_2593_, v___y_2571_, v___y_2572_, v___y_2573_, v___y_2574_);
                            if crate::leanh::lean_obj_tag(v___x_2594_) == 0 {
                                v_a_2595_ = crate::leanh::lean_ctor_get(v___x_2594_, 0);
                                crate::leanh::lean_inc(v_a_2595_);
                                crate::leanh::lean_dec_ref_known(v___x_2594_, 1);
                                v_a_2584_ = v_a_2595_;
                                state = 1;
                                continue;
                            } else {
                                crate::leanh::lean_dec_ref(v_bs_x27_2582_);
                                v_a_2596_ = crate::leanh::lean_ctor_get(v___x_2594_, 0);
                                v_isSharedCheck_2603_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_2594_)) as u8;
                                if v_isSharedCheck_2603_ == 0 {
                                    v___x_2598_ = v___x_2594_;
                                    v_isShared_2599_ = v_isSharedCheck_2603_;
                                    state = 2;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_a_2596_);
                                    crate::leanh::lean_dec(v___x_2594_);
                                    v___x_2598_ = crate::leanh::lean_box(0);
                                    v_isShared_2599_ = v_isSharedCheck_2603_;
                                    state = 2;
                                    continue;
                                }
                            }
                        }
                    } else {
                        crate::leanh::lean_dec_ref(v_bs_2570_);
                        v_a_2604_ = crate::leanh::lean_ctor_get(v___x_2579_, 0);
                        v_isSharedCheck_2611_ =
                            (!crate::leanh::lean_is_exclusive(v___x_2579_)) as u8;
                        if v_isSharedCheck_2611_ == 0 {
                            v___x_2606_ = v___x_2579_;
                            v_isShared_2607_ = v_isSharedCheck_2611_;
                            state = 4;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_2604_);
                            crate::leanh::lean_dec(v___x_2579_);
                            v___x_2606_ = crate::leanh::lean_box(0);
                            v_isShared_2607_ = v_isSharedCheck_2611_;
                            state = 4;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v___x_2585_ = 1usize;
                v___x_2586_ = lean_usize_add(v_i_2569_, v___x_2585_);
                v___x_2587_ = lean_array_uset(v_bs_x27_2582_, v_i_2569_, v_a_2584_);
                v_i_2569_ = v___x_2586_;
                v_bs_2570_ = v___x_2587_;
                state = 0;
                continue;
            }
            2 => {
                if v_isShared_2599_ == 0 {
                    v___x_2601_ = v___x_2598_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2602_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2602_, 0, v_a_2596_);
                    v___x_2601_ = v_reuseFailAlloc_2602_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_2601_;
            }
            4 => {
                if v_isShared_2607_ == 0 {
                    v___x_2609_ = v___x_2606_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_2610_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2610_, 0, v_a_2604_);
                    v___x_2609_ = v_reuseFailAlloc_2610_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_2609_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Meta_Grind_casesMatch_spec__0_spec__3___boxed(
    mut v_sz_2612_: *mut crate::leanh::LeanObject,
    mut v_i_2613_: *mut crate::leanh::LeanObject,
    mut v_bs_2614_: *mut crate::leanh::LeanObject,
    mut v___y_2615_: *mut crate::leanh::LeanObject,
    mut v___y_2616_: *mut crate::leanh::LeanObject,
    mut v___y_2617_: *mut crate::leanh::LeanObject,
    mut v___y_2618_: *mut crate::leanh::LeanObject,
    mut v___y_2619_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_boxed_2620_: usize = 0;
    let mut v_i_boxed_2621_: usize = 0;
    let mut v_res_2622_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_2620_ = crate::leanh::lean_unbox_usize(v_sz_2612_);
    crate::leanh::lean_dec(v_sz_2612_);
    v_i_boxed_2621_ = crate::leanh::lean_unbox_usize(v_i_2613_);
    crate::leanh::lean_dec(v_i_2613_);
    v_res_2622_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Meta_Grind_casesMatch_spec__0_spec__3(v_sz_boxed_2620_, v_i_boxed_2621_, v_bs_2614_, v___y_2615_, v___y_2616_, v___y_2617_, v___y_2618_);
    crate::leanh::lean_dec(v___y_2618_);
    crate::leanh::lean_dec_ref(v___y_2617_);
    crate::leanh::lean_dec(v___y_2616_);
    crate::leanh::lean_dec_ref(v___y_2615_);
    return v_res_2622_;
}
pub unsafe fn _init_l_Lean_Meta_matchMatcherApp_x3f___at___00Lean_Meta_Grind_casesMatch_spec__0___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2623_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_dummy_2624_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2623_ = crate::leanh::lean_box(0);
    v_dummy_2624_ = l_Lean_Expr_sort___override(v___x_2623_);
    return v_dummy_2624_;
}
pub unsafe fn _init_l_Lean_Meta_matchMatcherApp_x3f___at___00Lean_Meta_Grind_casesMatch_spec__0___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2625_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2626_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2627_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2625_ = crate::leanh::lean_box(0);
    v___x_2626_ = crate::leanh::lean_unsigned_to_nat(16);
    v___x_2627_ = lean_mk_array(v___x_2626_, v___x_2625_);
    return v___x_2627_;
}
pub unsafe fn _init_l_Lean_Meta_matchMatcherApp_x3f___at___00Lean_Meta_Grind_casesMatch_spec__0___closed__2()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2628_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2629_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2630_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2628_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Meta_matchMatcherApp_x3f___at___00Lean_Meta_Grind_casesMatch_spec__0___closed__1), core::ptr::addr_of_mut!(l_Lean_Meta_matchMatcherApp_x3f___at___00Lean_Meta_Grind_casesMatch_spec__0___closed__1_once), _init_l_Lean_Meta_matchMatcherApp_x3f___at___00Lean_Meta_Grind_casesMatch_spec__0___closed__1);
    v___x_2629_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_2630_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2630_, 0, v___x_2629_);
    crate::leanh::lean_ctor_set(v___x_2630_, 1, v___x_2628_);
    return v___x_2630_;
}
pub unsafe fn l_Lean_Meta_matchMatcherApp_x3f___at___00Lean_Meta_Grind_casesMatch_spec__0(
    mut v_e_2633_: *mut crate::leanh::LeanObject,
    mut v_alsoCasesOn_2634_: u8,
    mut v___y_2635_: *mut crate::leanh::LeanObject,
    mut v___y_2636_: *mut crate::leanh::LeanObject,
    mut v___y_2637_: *mut crate::leanh::LeanObject,
    mut v___y_2638_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2641_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2642_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2643_: u8 = 0;
    let mut v___x_2644_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2645_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2646_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_declName_2647_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_us_2648_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2649_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2650_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2652_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2653_: u8 = 0;
    let mut v_val_2654_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2656_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2657_: u8 = 0;
    let mut v_dummy_2658_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nargs_2659_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2660_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2661_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2662_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_args_2663_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2664_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2665_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2666_: u8 = 0;
    let mut v_numParams_2667_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_numDiscrs_2668_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2669_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2670_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2671_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2672_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2673_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2674_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2675_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2676_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2677_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2678_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2679_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2680_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2681_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2682_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2683_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2684_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2685_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2687_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2689_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2690_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2691_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2692_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2694_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2695_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2696_: u8 = 0;
    let mut v___x_2697_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_2698_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2699_: u8 = 0;
    let mut v_indName_2700_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2701_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2702_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2704_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2705_: u8 = 0;
    let mut v_val_2706_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2708_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2709_: u8 = 0;
    let mut v_toConstantVal_2710_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_numParams_2711_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_numIndices_2712_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ctors_2713_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nargs_2714_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_dummy_2715_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2716_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2717_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2718_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_args_2719_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2720_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2721_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2722_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2723_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2724_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2725_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2726_: u8 = 0;
    let mut v___x_2727_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2729_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2730_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2731_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_params_2732_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2733_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_motive_2734_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_discrs_2735_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2736_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2737_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_discrInfos_2738_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_alts_2739_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2741_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2742_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2743_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_2744_: usize = 0;
    let mut v___x_2745_: usize = 0;
    let mut v___x_2746_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2747_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2749_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2750_: u8 = 0;
    let mut v_start_2751_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_stop_2752_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_start_2753_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_stop_2754_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2755_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2756_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2757_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2758_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2759_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2760_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2761_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2762_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2763_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2764_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2766_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2768_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2769_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2770_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2771_: u8 = 0;
    let mut v_a_2772_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2774_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2775_: u8 = 0;
    let mut v___x_2777_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2778_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2779_: u8 = 0;
    let mut v_lower_2781_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_upper_2782_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_levelParams_2783_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2784_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2785_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2786_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2787_: u8 = 0;
    let mut v___x_2788_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2789_: u8 = 0;
    let mut v_isSharedCheck_2790_: u8 = 0;
    let mut v___x_2791_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2793_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2794_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2795_: u8 = 0;
    let mut v_a_2796_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2798_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2799_: u8 = 0;
    let mut v___x_2801_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2802_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2803_: u8 = 0;
    let mut v_isSharedCheck_2804_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2643_ = l_Lean_Expr_isApp(v_e_2633_);
                if v___x_2643_ == 0 {
                    crate::leanh::lean_dec_ref(v_e_2633_);
                    v___x_2644_ = crate::leanh::lean_box(0);
                    v___x_2645_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2645_, 0, v___x_2644_);
                    return v___x_2645_;
                } else {
                    v___x_2646_ = l_Lean_Expr_getAppFn(v_e_2633_);
                    if crate::leanh::lean_obj_tag(v___x_2646_) == 4 {
                        v_declName_2647_ = crate::leanh::lean_ctor_get(v___x_2646_, 0);
                        crate::leanh::lean_inc_n(v_declName_2647_, 2);
                        v_us_2648_ = crate::leanh::lean_ctor_get(v___x_2646_, 1);
                        crate::leanh::lean_inc(v_us_2648_);
                        crate::leanh::lean_dec_ref_known(v___x_2646_, 2);
                        v___x_2649_ = l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Meta_Grind_casesMatch_spec__0_spec__2___redArg(v_declName_2647_, v___y_2638_);
                        v_a_2650_ = crate::leanh::lean_ctor_get(v___x_2649_, 0);
                        v_isSharedCheck_2804_ =
                            (!crate::leanh::lean_is_exclusive(v___x_2649_)) as u8;
                        if v_isSharedCheck_2804_ == 0 {
                            v___x_2652_ = v___x_2649_;
                            v_isShared_2653_ = v_isSharedCheck_2804_;
                            state = 2;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_2650_);
                            crate::leanh::lean_dec(v___x_2649_);
                            v___x_2652_ = crate::leanh::lean_box(0);
                            v_isShared_2653_ = v_isSharedCheck_2804_;
                            state = 2;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec_ref(v___x_2646_);
                        crate::leanh::lean_dec_ref(v_e_2633_);
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_2641_ = crate::leanh::lean_box(0);
                v___x_2642_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2642_, 0, v___x_2641_);
                return v___x_2642_;
            }
            2 => {
                if crate::leanh::lean_obj_tag(v_a_2650_) == 1 {
                    v_val_2654_ = crate::leanh::lean_ctor_get(v_a_2650_, 0);
                    v_isSharedCheck_2696_ = (!crate::leanh::lean_is_exclusive(v_a_2650_)) as u8;
                    if v_isSharedCheck_2696_ == 0 {
                        v___x_2656_ = v_a_2650_;
                        v_isShared_2657_ = v_isSharedCheck_2696_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_val_2654_);
                        crate::leanh::lean_dec(v_a_2650_);
                        v___x_2656_ = crate::leanh::lean_box(0);
                        v_isShared_2657_ = v_isSharedCheck_2696_;
                        state = 3;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_2652_);
                    crate::leanh::lean_dec(v_a_2650_);
                    v___x_2697_ = lean_st_ref_get(v___y_2638_);
                    if v_alsoCasesOn_2634_ == 0 {
                        crate::leanh::lean_dec(v___x_2697_);
                        crate::leanh::lean_dec(v_us_2648_);
                        crate::leanh::lean_dec(v_declName_2647_);
                        crate::leanh::lean_dec_ref(v_e_2633_);
                        state = 1;
                        continue;
                    } else {
                        v_env_2698_ = crate::leanh::lean_ctor_get(v___x_2697_, 0);
                        crate::leanh::lean_inc_ref(v_env_2698_);
                        crate::leanh::lean_dec(v___x_2697_);
                        crate::leanh::lean_inc(v_declName_2647_);
                        v___x_2699_ = l_Lean_isCasesOnRecursor(v_env_2698_, v_declName_2647_);
                        if v___x_2699_ == 0 {
                            crate::leanh::lean_dec(v_us_2648_);
                            crate::leanh::lean_dec(v_declName_2647_);
                            crate::leanh::lean_dec_ref(v_e_2633_);
                            state = 1;
                            continue;
                        } else {
                            v_indName_2700_ = l_Lean_Name_getPrefix(v_declName_2647_);
                            v___x_2701_ = l_Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Meta_Grind_casesMatch_spec__0_spec__0(v_indName_2700_, v___y_2635_, v___y_2636_, v___y_2637_, v___y_2638_);
                            if crate::leanh::lean_obj_tag(v___x_2701_) == 0 {
                                v_a_2702_ = crate::leanh::lean_ctor_get(v___x_2701_, 0);
                                v_isSharedCheck_2795_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_2701_)) as u8;
                                if v_isSharedCheck_2795_ == 0 {
                                    v___x_2704_ = v___x_2701_;
                                    v_isShared_2705_ = v_isSharedCheck_2795_;
                                    state = 7;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_a_2702_);
                                    crate::leanh::lean_dec(v___x_2701_);
                                    v___x_2704_ = crate::leanh::lean_box(0);
                                    v_isShared_2705_ = v_isSharedCheck_2795_;
                                    state = 7;
                                    continue;
                                }
                            } else {
                                crate::leanh::lean_dec(v_us_2648_);
                                crate::leanh::lean_dec(v_declName_2647_);
                                crate::leanh::lean_dec_ref(v_e_2633_);
                                v_a_2796_ = crate::leanh::lean_ctor_get(v___x_2701_, 0);
                                v_isSharedCheck_2803_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_2701_)) as u8;
                                if v_isSharedCheck_2803_ == 0 {
                                    v___x_2798_ = v___x_2701_;
                                    v_isShared_2799_ = v_isSharedCheck_2803_;
                                    state = 18;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_a_2796_);
                                    crate::leanh::lean_dec(v___x_2701_);
                                    v___x_2798_ = crate::leanh::lean_box(0);
                                    v_isShared_2799_ = v_isSharedCheck_2803_;
                                    state = 18;
                                    continue;
                                }
                            }
                        }
                    }
                }
            }
            3 => {
                v_dummy_2658_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Meta_matchMatcherApp_x3f___at___00Lean_Meta_Grind_casesMatch_spec__0___closed__0), core::ptr::addr_of_mut!(l_Lean_Meta_matchMatcherApp_x3f___at___00Lean_Meta_Grind_casesMatch_spec__0___closed__0_once), _init_l_Lean_Meta_matchMatcherApp_x3f___at___00Lean_Meta_Grind_casesMatch_spec__0___closed__0);
                v_nargs_2659_ = l_Lean_Expr_getAppNumArgs(v_e_2633_);
                crate::leanh::lean_inc(v_nargs_2659_);
                v___x_2660_ = lean_mk_array(v_nargs_2659_, v_dummy_2658_);
                v___x_2661_ = crate::leanh::lean_unsigned_to_nat(1);
                v___x_2662_ = lean_nat_sub(v_nargs_2659_, v___x_2661_);
                crate::leanh::lean_dec(v_nargs_2659_);
                v_args_2663_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(
                    v_e_2633_,
                    v___x_2660_,
                    v___x_2662_,
                );
                v___x_2664_ = lean_array_get_size(v_args_2663_);
                v___x_2665_ = l_Lean_Meta_Match_MatcherInfo_arity(v_val_2654_);
                v___x_2666_ = lean_nat_dec_lt(v___x_2664_, v___x_2665_);
                crate::leanh::lean_dec(v___x_2665_);
                if v___x_2666_ == 0 {
                    v_numParams_2667_ = crate::leanh::lean_ctor_get(v_val_2654_, 0);
                    v_numDiscrs_2668_ = crate::leanh::lean_ctor_get(v_val_2654_, 1);
                    v___x_2669_ = lean_array_mk(v_us_2648_);
                    v___x_2670_ = crate::leanh::lean_unsigned_to_nat(0);
                    crate::leanh::lean_inc(v_numParams_2667_);
                    v___x_2671_ =
                        l_Array_extract___redArg(v_args_2663_, v___x_2670_, v_numParams_2667_);
                    v___x_2672_ = l_Lean_instInhabitedExpr;
                    v___x_2673_ = l_Lean_Meta_Match_MatcherInfo_getMotivePos(v_val_2654_);
                    v___x_2674_ = lean_array_get(v___x_2672_, v_args_2663_, v___x_2673_);
                    crate::leanh::lean_dec(v___x_2673_);
                    v___x_2675_ = lean_nat_add(v_numParams_2667_, v___x_2661_);
                    v___x_2676_ = lean_nat_add(v___x_2675_, v_numDiscrs_2668_);
                    crate::leanh::lean_inc(v___x_2676_);
                    crate::leanh::lean_inc_ref_n(v_args_2663_, 2);
                    v___x_2677_ =
                        l_Array_toSubarray___redArg(v_args_2663_, v___x_2675_, v___x_2676_);
                    v___x_2678_ = l_Subarray_copy___redArg(v___x_2677_);
                    v___x_2679_ = l_Lean_Meta_Match_MatcherInfo_numAlts(v_val_2654_);
                    v___x_2680_ = lean_nat_add(v___x_2676_, v___x_2679_);
                    crate::leanh::lean_dec(v___x_2679_);
                    crate::leanh::lean_inc(v___x_2680_);
                    v___x_2681_ =
                        l_Array_toSubarray___redArg(v_args_2663_, v___x_2676_, v___x_2680_);
                    v___x_2682_ = l_Subarray_copy___redArg(v___x_2681_);
                    v___x_2683_ =
                        l_Array_toSubarray___redArg(v_args_2663_, v___x_2680_, v___x_2664_);
                    v___x_2684_ = l_Subarray_copy___redArg(v___x_2683_);
                    v___x_2685_ = crate::leanh::lean_alloc_ctor(0, 8, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2685_, 0, v_val_2654_);
                    crate::leanh::lean_ctor_set(v___x_2685_, 1, v_declName_2647_);
                    crate::leanh::lean_ctor_set(v___x_2685_, 2, v___x_2669_);
                    crate::leanh::lean_ctor_set(v___x_2685_, 3, v___x_2671_);
                    crate::leanh::lean_ctor_set(v___x_2685_, 4, v___x_2674_);
                    crate::leanh::lean_ctor_set(v___x_2685_, 5, v___x_2678_);
                    crate::leanh::lean_ctor_set(v___x_2685_, 6, v___x_2682_);
                    crate::leanh::lean_ctor_set(v___x_2685_, 7, v___x_2684_);
                    if v_isShared_2657_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_2656_, 0, v___x_2685_);
                        v___x_2687_ = v___x_2656_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_2691_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2691_, 0, v___x_2685_);
                        v___x_2687_ = v_reuseFailAlloc_2691_;
                        state = 4;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_args_2663_);
                    crate::leanh::lean_del_object(v___x_2656_);
                    crate::leanh::lean_dec(v_val_2654_);
                    crate::leanh::lean_dec(v_us_2648_);
                    crate::leanh::lean_dec(v_declName_2647_);
                    v___x_2692_ = crate::leanh::lean_box(0);
                    if v_isShared_2653_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_2652_, 0, v___x_2692_);
                        v___x_2694_ = v___x_2652_;
                        state = 6;
                        continue;
                    } else {
                        v_reuseFailAlloc_2695_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2695_, 0, v___x_2692_);
                        v___x_2694_ = v_reuseFailAlloc_2695_;
                        state = 6;
                        continue;
                    }
                }
            }
            4 => {
                if v_isShared_2653_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2652_, 0, v___x_2687_);
                    v___x_2689_ = v___x_2652_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_2690_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2690_, 0, v___x_2687_);
                    v___x_2689_ = v_reuseFailAlloc_2690_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_2689_;
            }
            6 => {
                return v___x_2694_;
            }
            7 => {
                if crate::leanh::lean_obj_tag(v_a_2702_) == 5 {
                    v_val_2706_ = crate::leanh::lean_ctor_get(v_a_2702_, 0);
                    v_isSharedCheck_2790_ = (!crate::leanh::lean_is_exclusive(v_a_2702_)) as u8;
                    if v_isSharedCheck_2790_ == 0 {
                        v___x_2708_ = v_a_2702_;
                        v_isShared_2709_ = v_isSharedCheck_2790_;
                        state = 8;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_val_2706_);
                        crate::leanh::lean_dec(v_a_2702_);
                        v___x_2708_ = crate::leanh::lean_box(0);
                        v_isShared_2709_ = v_isSharedCheck_2790_;
                        state = 8;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_a_2702_);
                    crate::leanh::lean_dec(v_us_2648_);
                    crate::leanh::lean_dec(v_declName_2647_);
                    crate::leanh::lean_dec_ref(v_e_2633_);
                    v___x_2791_ = crate::leanh::lean_box(0);
                    if v_isShared_2705_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_2704_, 0, v___x_2791_);
                        v___x_2793_ = v___x_2704_;
                        state = 17;
                        continue;
                    } else {
                        v_reuseFailAlloc_2794_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2794_, 0, v___x_2791_);
                        v___x_2793_ = v_reuseFailAlloc_2794_;
                        state = 17;
                        continue;
                    }
                }
            }
            8 => {
                v_toConstantVal_2710_ = crate::leanh::lean_ctor_get(v_val_2706_, 0);
                crate::leanh::lean_inc_ref(v_toConstantVal_2710_);
                v_numParams_2711_ = crate::leanh::lean_ctor_get(v_val_2706_, 1);
                crate::leanh::lean_inc(v_numParams_2711_);
                v_numIndices_2712_ = crate::leanh::lean_ctor_get(v_val_2706_, 2);
                crate::leanh::lean_inc(v_numIndices_2712_);
                v_ctors_2713_ = crate::leanh::lean_ctor_get(v_val_2706_, 4);
                crate::leanh::lean_inc(v_ctors_2713_);
                v_nargs_2714_ = l_Lean_Expr_getAppNumArgs(v_e_2633_);
                v_dummy_2715_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Meta_matchMatcherApp_x3f___at___00Lean_Meta_Grind_casesMatch_spec__0___closed__0), core::ptr::addr_of_mut!(l_Lean_Meta_matchMatcherApp_x3f___at___00Lean_Meta_Grind_casesMatch_spec__0___closed__0_once), _init_l_Lean_Meta_matchMatcherApp_x3f___at___00Lean_Meta_Grind_casesMatch_spec__0___closed__0);
                crate::leanh::lean_inc(v_nargs_2714_);
                v___x_2716_ = lean_mk_array(v_nargs_2714_, v_dummy_2715_);
                v___x_2717_ = crate::leanh::lean_unsigned_to_nat(1);
                v___x_2718_ = lean_nat_sub(v_nargs_2714_, v___x_2717_);
                crate::leanh::lean_dec(v_nargs_2714_);
                v_args_2719_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(
                    v_e_2633_,
                    v___x_2716_,
                    v___x_2718_,
                );
                v___x_2720_ = lean_nat_add(v_numParams_2711_, v___x_2717_);
                v___x_2721_ = lean_nat_add(v___x_2720_, v_numIndices_2712_);
                v___x_2722_ = lean_nat_add(v___x_2721_, v___x_2717_);
                crate::leanh::lean_dec(v___x_2721_);
                v___x_2723_ = l_Lean_InductiveVal_numCtors(v_val_2706_);
                crate::leanh::lean_dec_ref(v_val_2706_);
                v___x_2724_ = lean_nat_add(v___x_2722_, v___x_2723_);
                crate::leanh::lean_dec(v___x_2723_);
                v___x_2725_ = lean_array_get_size(v_args_2719_);
                v___x_2726_ = lean_nat_dec_le(v___x_2724_, v___x_2725_);
                if v___x_2726_ == 0 {
                    crate::leanh::lean_dec(v___x_2724_);
                    crate::leanh::lean_dec(v___x_2722_);
                    crate::leanh::lean_dec(v___x_2720_);
                    crate::leanh::lean_dec_ref(v_args_2719_);
                    crate::leanh::lean_dec(v_ctors_2713_);
                    crate::leanh::lean_dec(v_numIndices_2712_);
                    crate::leanh::lean_dec(v_numParams_2711_);
                    crate::leanh::lean_dec_ref(v_toConstantVal_2710_);
                    crate::leanh::lean_del_object(v___x_2708_);
                    crate::leanh::lean_dec(v_us_2648_);
                    crate::leanh::lean_dec(v_declName_2647_);
                    v___x_2727_ = crate::leanh::lean_box(0);
                    if v_isShared_2705_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_2704_, 0, v___x_2727_);
                        v___x_2729_ = v___x_2704_;
                        state = 9;
                        continue;
                    } else {
                        v_reuseFailAlloc_2730_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2730_, 0, v___x_2727_);
                        v___x_2729_ = v_reuseFailAlloc_2730_;
                        state = 9;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_2704_);
                    v___x_2731_ = crate::leanh::lean_unsigned_to_nat(0);
                    crate::leanh::lean_inc(v_numParams_2711_);
                    crate::leanh::lean_inc_ref_n(v_args_2719_, 3);
                    v_params_2732_ =
                        l_Array_toSubarray___redArg(v_args_2719_, v___x_2731_, v_numParams_2711_);
                    v___x_2733_ = l_Lean_instInhabitedExpr;
                    v_motive_2734_ = lean_array_get(v___x_2733_, v_args_2719_, v_numParams_2711_);
                    crate::leanh::lean_dec(v_numParams_2711_);
                    crate::leanh::lean_inc(v___x_2722_);
                    v_discrs_2735_ =
                        l_Array_toSubarray___redArg(v_args_2719_, v___x_2720_, v___x_2722_);
                    v___x_2736_ = lean_nat_add(v_numIndices_2712_, v___x_2717_);
                    crate::leanh::lean_dec(v_numIndices_2712_);
                    v___x_2737_ = crate::leanh::lean_box(0);
                    v_discrInfos_2738_ = lean_mk_array(v___x_2736_, v___x_2737_);
                    crate::leanh::lean_inc(v___x_2724_);
                    v_alts_2739_ =
                        l_Array_toSubarray___redArg(v_args_2719_, v___x_2722_, v___x_2724_);
                    v___x_2789_ = lean_nat_dec_le(v___x_2724_, v___x_2731_);
                    if v___x_2789_ == 0 {
                        v_lower_2781_ = v___x_2724_;
                        v_upper_2782_ = v___x_2725_;
                        state = 16;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v___x_2724_);
                        v_lower_2781_ = v___x_2731_;
                        v_upper_2782_ = v___x_2725_;
                        state = 16;
                        continue;
                    }
                }
            }
            9 => {
                return v___x_2729_;
            }
            10 => {
                v___x_2743_ = lean_array_mk(v_ctors_2713_);
                v_sz_2744_ = lean_array_size(v___x_2743_);
                v___x_2745_ = 0usize;
                v___x_2746_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Meta_Grind_casesMatch_spec__0_spec__3(v_sz_2744_, v___x_2745_, v___x_2743_, v___y_2635_, v___y_2636_, v___y_2637_, v___y_2638_);
                if crate::leanh::lean_obj_tag(v___x_2746_) == 0 {
                    v_a_2747_ = crate::leanh::lean_ctor_get(v___x_2746_, 0);
                    v_isSharedCheck_2771_ = (!crate::leanh::lean_is_exclusive(v___x_2746_)) as u8;
                    if v_isSharedCheck_2771_ == 0 {
                        v___x_2749_ = v___x_2746_;
                        v_isShared_2750_ = v_isSharedCheck_2771_;
                        state = 11;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2747_);
                        crate::leanh::lean_dec(v___x_2746_);
                        v___x_2749_ = crate::leanh::lean_box(0);
                        v_isShared_2750_ = v_isSharedCheck_2771_;
                        state = 11;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v___y_2742_);
                    crate::leanh::lean_dec_ref(v___y_2741_);
                    crate::leanh::lean_dec_ref(v_alts_2739_);
                    crate::leanh::lean_dec_ref(v_discrInfos_2738_);
                    crate::leanh::lean_dec_ref(v_discrs_2735_);
                    crate::leanh::lean_dec(v_motive_2734_);
                    crate::leanh::lean_dec_ref(v_params_2732_);
                    crate::leanh::lean_del_object(v___x_2708_);
                    crate::leanh::lean_dec(v_us_2648_);
                    crate::leanh::lean_dec(v_declName_2647_);
                    v_a_2772_ = crate::leanh::lean_ctor_get(v___x_2746_, 0);
                    v_isSharedCheck_2779_ = (!crate::leanh::lean_is_exclusive(v___x_2746_)) as u8;
                    if v_isSharedCheck_2779_ == 0 {
                        v___x_2774_ = v___x_2746_;
                        v_isShared_2775_ = v_isSharedCheck_2779_;
                        state = 14;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2772_);
                        crate::leanh::lean_dec(v___x_2746_);
                        v___x_2774_ = crate::leanh::lean_box(0);
                        v_isShared_2775_ = v_isSharedCheck_2779_;
                        state = 14;
                        continue;
                    }
                }
            }
            11 => {
                v_start_2751_ = crate::leanh::lean_ctor_get(v_params_2732_, 1);
                crate::leanh::lean_inc(v_start_2751_);
                v_stop_2752_ = crate::leanh::lean_ctor_get(v_params_2732_, 2);
                crate::leanh::lean_inc(v_stop_2752_);
                v_start_2753_ = crate::leanh::lean_ctor_get(v_discrs_2735_, 1);
                crate::leanh::lean_inc(v_start_2753_);
                v_stop_2754_ = crate::leanh::lean_ctor_get(v_discrs_2735_, 2);
                crate::leanh::lean_inc(v_stop_2754_);
                v___x_2755_ = lean_nat_sub(v_stop_2752_, v_start_2751_);
                crate::leanh::lean_dec(v_start_2751_);
                crate::leanh::lean_dec(v_stop_2752_);
                v___x_2756_ = lean_nat_sub(v_stop_2754_, v_start_2753_);
                crate::leanh::lean_dec(v_start_2753_);
                crate::leanh::lean_dec(v_stop_2754_);
                v___x_2757_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Meta_matchMatcherApp_x3f___at___00Lean_Meta_Grind_casesMatch_spec__0___closed__2), core::ptr::addr_of_mut!(l_Lean_Meta_matchMatcherApp_x3f___at___00Lean_Meta_Grind_casesMatch_spec__0___closed__2_once), _init_l_Lean_Meta_matchMatcherApp_x3f___at___00Lean_Meta_Grind_casesMatch_spec__0___closed__2);
                v___x_2758_ = crate::leanh::lean_alloc_ctor(0, 6, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2758_, 0, v___x_2755_);
                crate::leanh::lean_ctor_set(v___x_2758_, 1, v___x_2756_);
                crate::leanh::lean_ctor_set(v___x_2758_, 2, v_a_2747_);
                crate::leanh::lean_ctor_set(v___x_2758_, 3, v___y_2742_);
                crate::leanh::lean_ctor_set(v___x_2758_, 4, v_discrInfos_2738_);
                crate::leanh::lean_ctor_set(v___x_2758_, 5, v___x_2757_);
                v___x_2759_ = lean_array_mk(v_us_2648_);
                v___x_2760_ = l_Subarray_copy___redArg(v_params_2732_);
                v___x_2761_ = l_Subarray_copy___redArg(v_discrs_2735_);
                v___x_2762_ = l_Subarray_copy___redArg(v_alts_2739_);
                v___x_2763_ = l_Subarray_copy___redArg(v___y_2741_);
                v___x_2764_ = crate::leanh::lean_alloc_ctor(0, 8, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2764_, 0, v___x_2758_);
                crate::leanh::lean_ctor_set(v___x_2764_, 1, v_declName_2647_);
                crate::leanh::lean_ctor_set(v___x_2764_, 2, v___x_2759_);
                crate::leanh::lean_ctor_set(v___x_2764_, 3, v___x_2760_);
                crate::leanh::lean_ctor_set(v___x_2764_, 4, v_motive_2734_);
                crate::leanh::lean_ctor_set(v___x_2764_, 5, v___x_2761_);
                crate::leanh::lean_ctor_set(v___x_2764_, 6, v___x_2762_);
                crate::leanh::lean_ctor_set(v___x_2764_, 7, v___x_2763_);
                if v_isShared_2709_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_2708_, 1);
                    crate::leanh::lean_ctor_set(v___x_2708_, 0, v___x_2764_);
                    v___x_2766_ = v___x_2708_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_2770_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2770_, 0, v___x_2764_);
                    v___x_2766_ = v_reuseFailAlloc_2770_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                if v_isShared_2750_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2749_, 0, v___x_2766_);
                    v___x_2768_ = v___x_2749_;
                    state = 13;
                    continue;
                } else {
                    v_reuseFailAlloc_2769_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2769_, 0, v___x_2766_);
                    v___x_2768_ = v_reuseFailAlloc_2769_;
                    state = 13;
                    continue;
                }
            }
            13 => {
                return v___x_2768_;
            }
            14 => {
                if v_isShared_2775_ == 0 {
                    v___x_2777_ = v___x_2774_;
                    state = 15;
                    continue;
                } else {
                    v_reuseFailAlloc_2778_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2778_, 0, v_a_2772_);
                    v___x_2777_ = v_reuseFailAlloc_2778_;
                    state = 15;
                    continue;
                }
            }
            15 => {
                return v___x_2777_;
            }
            16 => {
                v_levelParams_2783_ = crate::leanh::lean_ctor_get(v_toConstantVal_2710_, 1);
                crate::leanh::lean_inc(v_levelParams_2783_);
                crate::leanh::lean_dec_ref(v_toConstantVal_2710_);
                v___x_2784_ =
                    l_Array_toSubarray___redArg(v_args_2719_, v_lower_2781_, v_upper_2782_);
                v___x_2785_ = l_List_lengthTR___redArg(v_levelParams_2783_);
                crate::leanh::lean_dec(v_levelParams_2783_);
                v___x_2786_ = l_List_lengthTR___redArg(v_us_2648_);
                v___x_2787_ = lean_nat_dec_eq(v___x_2785_, v___x_2786_);
                crate::leanh::lean_dec(v___x_2786_);
                crate::leanh::lean_dec(v___x_2785_);
                if v___x_2787_ == 0 {
                    v___x_2788_ = l_Lean_Meta_matchMatcherApp_x3f___at___00Lean_Meta_Grind_casesMatch_spec__0___closed__3;
                    v___y_2741_ = v___x_2784_;
                    v___y_2742_ = v___x_2788_;
                    state = 10;
                    continue;
                } else {
                    v___y_2741_ = v___x_2784_;
                    v___y_2742_ = v___x_2737_;
                    state = 10;
                    continue;
                }
            }
            17 => {
                return v___x_2793_;
            }
            18 => {
                if v_isShared_2799_ == 0 {
                    v___x_2801_ = v___x_2798_;
                    state = 19;
                    continue;
                } else {
                    v_reuseFailAlloc_2802_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2802_, 0, v_a_2796_);
                    v___x_2801_ = v_reuseFailAlloc_2802_;
                    state = 19;
                    continue;
                }
            }
            19 => {
                return v___x_2801_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_matchMatcherApp_x3f___at___00Lean_Meta_Grind_casesMatch_spec__0___boxed(
    mut v_e_2805_: *mut crate::leanh::LeanObject,
    mut v_alsoCasesOn_2806_: *mut crate::leanh::LeanObject,
    mut v___y_2807_: *mut crate::leanh::LeanObject,
    mut v___y_2808_: *mut crate::leanh::LeanObject,
    mut v___y_2809_: *mut crate::leanh::LeanObject,
    mut v___y_2810_: *mut crate::leanh::LeanObject,
    mut v___y_2811_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_alsoCasesOn_boxed_2812_: u8 = 0;
    let mut v_res_2813_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_alsoCasesOn_boxed_2812_ = (crate::leanh::lean_unbox(v_alsoCasesOn_2806_) as u8);
    v_res_2813_ = l_Lean_Meta_matchMatcherApp_x3f___at___00Lean_Meta_Grind_casesMatch_spec__0(
        v_e_2805_,
        v_alsoCasesOn_boxed_2812_,
        v___y_2807_,
        v___y_2808_,
        v___y_2809_,
        v___y_2810_,
    );
    crate::leanh::lean_dec(v___y_2810_);
    crate::leanh::lean_dec_ref(v___y_2809_);
    crate::leanh::lean_dec(v___y_2808_);
    crate::leanh::lean_dec_ref(v___y_2807_);
    return v_res_2813_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_casesMatch_spec__1_spec__5_spec__8_spec__11_spec__13___redArg(
    mut v_x_2814_: *mut crate::leanh::LeanObject,
    mut v_x_2815_: *mut crate::leanh::LeanObject,
    mut v_x_2816_: *mut crate::leanh::LeanObject,
    mut v_x_2817_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_ks_2818_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_vs_2819_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2821_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2822_: u8 = 0;
    let mut v___x_2823_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2824_: u8 = 0;
    let mut v___x_2825_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2826_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2828_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2829_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_x27_2830_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2831_: u8 = 0;
    let mut v___x_2833_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2834_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2835_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2837_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2838_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2839_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2841_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2842_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2843_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ks_2818_ = crate::leanh::lean_ctor_get(v_x_2814_, 0);
                v_vs_2819_ = crate::leanh::lean_ctor_get(v_x_2814_, 1);
                v_isSharedCheck_2843_ = (!crate::leanh::lean_is_exclusive(v_x_2814_)) as u8;
                if v_isSharedCheck_2843_ == 0 {
                    v___x_2821_ = v_x_2814_;
                    v_isShared_2822_ = v_isSharedCheck_2843_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_vs_2819_);
                    crate::leanh::lean_inc(v_ks_2818_);
                    crate::leanh::lean_dec(v_x_2814_);
                    v___x_2821_ = crate::leanh::lean_box(0);
                    v_isShared_2822_ = v_isSharedCheck_2843_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_2823_ = lean_array_get_size(v_ks_2818_);
                v___x_2824_ = lean_nat_dec_lt(v_x_2815_, v___x_2823_);
                if v___x_2824_ == 0 {
                    crate::leanh::lean_dec(v_x_2815_);
                    v___x_2825_ = lean_array_push(v_ks_2818_, v_x_2816_);
                    v___x_2826_ = lean_array_push(v_vs_2819_, v_x_2817_);
                    if v_isShared_2822_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_2821_, 1, v___x_2826_);
                        crate::leanh::lean_ctor_set(v___x_2821_, 0, v___x_2825_);
                        v___x_2828_ = v___x_2821_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_2829_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2829_, 0, v___x_2825_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2829_, 1, v___x_2826_);
                        v___x_2828_ = v_reuseFailAlloc_2829_;
                        state = 2;
                        continue;
                    }
                } else {
                    v_k_x27_2830_ = lean_array_fget_borrowed(v_ks_2818_, v_x_2815_);
                    v___x_2831_ = l_Lean_instBEqMVarId_beq(v_x_2816_, v_k_x27_2830_);
                    if v___x_2831_ == 0 {
                        if v_isShared_2822_ == 0 {
                            v___x_2833_ = v___x_2821_;
                            state = 3;
                            continue;
                        } else {
                            v_reuseFailAlloc_2837_ =
                                crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_2837_, 0, v_ks_2818_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_2837_, 1, v_vs_2819_);
                            v___x_2833_ = v_reuseFailAlloc_2837_;
                            state = 3;
                            continue;
                        }
                    } else {
                        v___x_2838_ = lean_array_fset(v_ks_2818_, v_x_2815_, v_x_2816_);
                        v___x_2839_ = lean_array_fset(v_vs_2819_, v_x_2815_, v_x_2817_);
                        crate::leanh::lean_dec(v_x_2815_);
                        if v_isShared_2822_ == 0 {
                            crate::leanh::lean_ctor_set(v___x_2821_, 1, v___x_2839_);
                            crate::leanh::lean_ctor_set(v___x_2821_, 0, v___x_2838_);
                            v___x_2841_ = v___x_2821_;
                            state = 4;
                            continue;
                        } else {
                            v_reuseFailAlloc_2842_ =
                                crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_2842_, 0, v___x_2838_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_2842_, 1, v___x_2839_);
                            v___x_2841_ = v_reuseFailAlloc_2842_;
                            state = 4;
                            continue;
                        }
                    }
                }
            }
            2 => {
                return v___x_2828_;
            }
            3 => {
                v___x_2834_ = crate::leanh::lean_unsigned_to_nat(1);
                v___x_2835_ = lean_nat_add(v_x_2815_, v___x_2834_);
                crate::leanh::lean_dec(v_x_2815_);
                v_x_2814_ = v___x_2833_;
                v_x_2815_ = v___x_2835_;
                state = 0;
                continue;
            }
            4 => {
                return v___x_2841_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_casesMatch_spec__1_spec__5_spec__8_spec__11___redArg(
    mut v_n_2844_: *mut crate::leanh::LeanObject,
    mut v_k_2845_: *mut crate::leanh::LeanObject,
    mut v_v_2846_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2847_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2848_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2847_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_2848_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_casesMatch_spec__1_spec__5_spec__8_spec__11_spec__13___redArg(v_n_2844_, v___x_2847_, v_k_2845_, v_v_2846_);
    return v___x_2848_;
}
pub unsafe fn _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_casesMatch_spec__1_spec__5_spec__8___redArg___closed__0()
-> usize {
    let mut v___x_2849_: usize = 0;
    let mut v___x_2850_: usize = 0;
    let mut v___x_2851_: usize = 0;
    v___x_2849_ = 5usize;
    v___x_2850_ = 1usize;
    v___x_2851_ = lean_usize_shift_left(v___x_2850_, v___x_2849_);
    return v___x_2851_;
}
pub unsafe fn _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_casesMatch_spec__1_spec__5_spec__8___redArg___closed__1()
-> usize {
    let mut v___x_2852_: usize = 0;
    let mut v___x_2853_: usize = 0;
    let mut v___x_2854_: usize = 0;
    v___x_2852_ = 1usize;
    v___x_2853_ = crate::leanh::lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_casesMatch_spec__1_spec__5_spec__8___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_casesMatch_spec__1_spec__5_spec__8___redArg___closed__0_once), _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_casesMatch_spec__1_spec__5_spec__8___redArg___closed__0);
    v___x_2854_ = lean_usize_sub(v___x_2853_, v___x_2852_);
    return v___x_2854_;
}
pub unsafe fn _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_casesMatch_spec__1_spec__5_spec__8___redArg___closed__2()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2855_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2855_ = l_Lean_PersistentHashMap_mkEmptyEntries(
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
    );
    return v___x_2855_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_casesMatch_spec__1_spec__5_spec__8___redArg(
    mut v_x_2856_: *mut crate::leanh::LeanObject,
    mut v_x_2857_: usize,
    mut v_x_2858_: usize,
    mut v_x_2859_: *mut crate::leanh::LeanObject,
    mut v_x_2860_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_es_2861_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2862_: usize = 0;
    let mut v___x_2863_: usize = 0;
    let mut v___x_2864_: usize = 0;
    let mut v___x_2865_: usize = 0;
    let mut v_j_2866_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2867_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2868_: u8 = 0;
    let mut v___x_2870_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2871_: u8 = 0;
    let mut v_v_2872_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2873_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_xs_x27_2874_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2876_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2877_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2879_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2880_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_key_2881_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2882_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2884_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2885_: u8 = 0;
    let mut v___x_2886_: u8 = 0;
    let mut v___x_2887_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2888_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2890_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2891_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2892_: u8 = 0;
    let mut v_node_2893_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2895_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2896_: u8 = 0;
    let mut v___x_2897_: usize = 0;
    let mut v___x_2898_: usize = 0;
    let mut v___x_2899_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2901_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2902_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2903_: u8 = 0;
    let mut v___x_2904_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2905_: u8 = 0;
    let mut v_unused_2906_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ks_2907_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_vs_2908_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2910_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2911_: u8 = 0;
    let mut v___x_2913_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_newNode_2914_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2916_: u8 = 0;
    let mut v_ks_2917_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_vs_2918_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2919_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2920_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2921_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2922_: usize = 0;
    let mut v___x_2923_: u8 = 0;
    let mut v___x_2924_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2925_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2926_: u8 = 0;
    let mut v_reuseFailAlloc_2927_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2928_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_2856_) == 0 {
                    v_es_2861_ = crate::leanh::lean_ctor_get(v_x_2856_, 0);
                    v___x_2862_ = 5usize;
                    v___x_2863_ = 1usize;
                    v___x_2864_ = crate::leanh::lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_casesMatch_spec__1_spec__5_spec__8___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_casesMatch_spec__1_spec__5_spec__8___redArg___closed__1_once), _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_casesMatch_spec__1_spec__5_spec__8___redArg___closed__1);
                    v___x_2865_ = lean_usize_land(v_x_2857_, v___x_2864_);
                    v_j_2866_ = lean_usize_to_nat(v___x_2865_);
                    v___x_2867_ = lean_array_get_size(v_es_2861_);
                    v___x_2868_ = lean_nat_dec_lt(v_j_2866_, v___x_2867_);
                    if v___x_2868_ == 0 {
                        crate::leanh::lean_dec(v_j_2866_);
                        crate::leanh::lean_dec(v_x_2860_);
                        crate::leanh::lean_dec(v_x_2859_);
                        return v_x_2856_;
                    } else {
                        crate::leanh::lean_inc_ref(v_es_2861_);
                        v_isSharedCheck_2905_ = (!crate::leanh::lean_is_exclusive(v_x_2856_)) as u8;
                        if v_isSharedCheck_2905_ == 0 {
                            v_unused_2906_ = crate::leanh::lean_ctor_get(v_x_2856_, 0);
                            crate::leanh::lean_dec(v_unused_2906_);
                            v___x_2870_ = v_x_2856_;
                            v_isShared_2871_ = v_isSharedCheck_2905_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_dec(v_x_2856_);
                            v___x_2870_ = crate::leanh::lean_box(0);
                            v_isShared_2871_ = v_isSharedCheck_2905_;
                            state = 1;
                            continue;
                        }
                    }
                } else {
                    v_ks_2907_ = crate::leanh::lean_ctor_get(v_x_2856_, 0);
                    v_vs_2908_ = crate::leanh::lean_ctor_get(v_x_2856_, 1);
                    v_isSharedCheck_2928_ = (!crate::leanh::lean_is_exclusive(v_x_2856_)) as u8;
                    if v_isSharedCheck_2928_ == 0 {
                        v___x_2910_ = v_x_2856_;
                        v_isShared_2911_ = v_isSharedCheck_2928_;
                        state = 8;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_vs_2908_);
                        crate::leanh::lean_inc(v_ks_2907_);
                        crate::leanh::lean_dec(v_x_2856_);
                        v___x_2910_ = crate::leanh::lean_box(0);
                        v_isShared_2911_ = v_isSharedCheck_2928_;
                        state = 8;
                        continue;
                    }
                }
            }
            1 => {
                v_v_2872_ = lean_array_fget(v_es_2861_, v_j_2866_);
                v___x_2873_ = crate::leanh::lean_box(0);
                v_xs_x27_2874_ = lean_array_fset(v_es_2861_, v_j_2866_, v___x_2873_);
                match crate::leanh::lean_obj_tag(v_v_2872_) {
                    0 => {
                        v_key_2881_ = crate::leanh::lean_ctor_get(v_v_2872_, 0);
                        v_val_2882_ = crate::leanh::lean_ctor_get(v_v_2872_, 1);
                        v_isSharedCheck_2892_ = (!crate::leanh::lean_is_exclusive(v_v_2872_)) as u8;
                        if v_isSharedCheck_2892_ == 0 {
                            v___x_2884_ = v_v_2872_;
                            v_isShared_2885_ = v_isSharedCheck_2892_;
                            state = 4;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_val_2882_);
                            crate::leanh::lean_inc(v_key_2881_);
                            crate::leanh::lean_dec(v_v_2872_);
                            v___x_2884_ = crate::leanh::lean_box(0);
                            v_isShared_2885_ = v_isSharedCheck_2892_;
                            state = 4;
                            continue;
                        }
                    }
                    1 => {
                        v_node_2893_ = crate::leanh::lean_ctor_get(v_v_2872_, 0);
                        v_isSharedCheck_2903_ = (!crate::leanh::lean_is_exclusive(v_v_2872_)) as u8;
                        if v_isSharedCheck_2903_ == 0 {
                            v___x_2895_ = v_v_2872_;
                            v_isShared_2896_ = v_isSharedCheck_2903_;
                            state = 6;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_node_2893_);
                            crate::leanh::lean_dec(v_v_2872_);
                            v___x_2895_ = crate::leanh::lean_box(0);
                            v_isShared_2896_ = v_isSharedCheck_2903_;
                            state = 6;
                            continue;
                        }
                    }
                    _ => {
                        v___x_2904_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_2904_, 0, v_x_2859_);
                        crate::leanh::lean_ctor_set(v___x_2904_, 1, v_x_2860_);
                        v___y_2876_ = v___x_2904_;
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                v___x_2877_ = lean_array_fset(v_xs_x27_2874_, v_j_2866_, v___y_2876_);
                crate::leanh::lean_dec(v_j_2866_);
                if v_isShared_2871_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2870_, 0, v___x_2877_);
                    v___x_2879_ = v___x_2870_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2880_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2880_, 0, v___x_2877_);
                    v___x_2879_ = v_reuseFailAlloc_2880_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_2879_;
            }
            4 => {
                v___x_2886_ = l_Lean_instBEqMVarId_beq(v_x_2859_, v_key_2881_);
                if v___x_2886_ == 0 {
                    crate::leanh::lean_del_object(v___x_2884_);
                    v___x_2887_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(
                        v_key_2881_,
                        v_val_2882_,
                        v_x_2859_,
                        v_x_2860_,
                    );
                    v___x_2888_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2888_, 0, v___x_2887_);
                    v___y_2876_ = v___x_2888_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_dec(v_val_2882_);
                    crate::leanh::lean_dec(v_key_2881_);
                    if v_isShared_2885_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_2884_, 1, v_x_2860_);
                        crate::leanh::lean_ctor_set(v___x_2884_, 0, v_x_2859_);
                        v___x_2890_ = v___x_2884_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_2891_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2891_, 0, v_x_2859_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2891_, 1, v_x_2860_);
                        v___x_2890_ = v_reuseFailAlloc_2891_;
                        state = 5;
                        continue;
                    }
                }
            }
            5 => {
                v___y_2876_ = v___x_2890_;
                state = 2;
                continue;
            }
            6 => {
                v___x_2897_ = lean_usize_shift_right(v_x_2857_, v___x_2862_);
                v___x_2898_ = lean_usize_add(v_x_2858_, v___x_2863_);
                v___x_2899_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_casesMatch_spec__1_spec__5_spec__8___redArg(v_node_2893_, v___x_2897_, v___x_2898_, v_x_2859_, v_x_2860_);
                if v_isShared_2896_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2895_, 0, v___x_2899_);
                    v___x_2901_ = v___x_2895_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_2902_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2902_, 0, v___x_2899_);
                    v___x_2901_ = v_reuseFailAlloc_2902_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                v___y_2876_ = v___x_2901_;
                state = 2;
                continue;
            }
            8 => {
                if v_isShared_2911_ == 0 {
                    v___x_2913_ = v___x_2910_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_2927_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2927_, 0, v_ks_2907_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2927_, 1, v_vs_2908_);
                    v___x_2913_ = v_reuseFailAlloc_2927_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                v_newNode_2914_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_casesMatch_spec__1_spec__5_spec__8_spec__11___redArg(v___x_2913_, v_x_2859_, v_x_2860_);
                v___x_2922_ = 7usize;
                v___x_2923_ = lean_usize_dec_le(v___x_2922_, v_x_2858_);
                if v___x_2923_ == 0 {
                    v___x_2924_ =
                        l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_2914_);
                    v___x_2925_ = crate::leanh::lean_unsigned_to_nat(4);
                    v___x_2926_ = lean_nat_dec_lt(v___x_2924_, v___x_2925_);
                    crate::leanh::lean_dec(v___x_2924_);
                    v___y_2916_ = v___x_2926_;
                    state = 10;
                    continue;
                } else {
                    v___y_2916_ = v___x_2923_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                if v___y_2916_ == 0 {
                    v_ks_2917_ = crate::leanh::lean_ctor_get(v_newNode_2914_, 0);
                    crate::leanh::lean_inc_ref(v_ks_2917_);
                    v_vs_2918_ = crate::leanh::lean_ctor_get(v_newNode_2914_, 1);
                    crate::leanh::lean_inc_ref(v_vs_2918_);
                    crate::leanh::lean_dec_ref(v_newNode_2914_);
                    v___x_2919_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___x_2920_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_casesMatch_spec__1_spec__5_spec__8___redArg___closed__2), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_casesMatch_spec__1_spec__5_spec__8___redArg___closed__2_once), _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_casesMatch_spec__1_spec__5_spec__8___redArg___closed__2);
                    v___x_2921_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_casesMatch_spec__1_spec__5_spec__8_spec__12___redArg(v_x_2858_, v_ks_2917_, v_vs_2918_, v___x_2919_, v___x_2920_);
                    crate::leanh::lean_dec_ref(v_vs_2918_);
                    crate::leanh::lean_dec_ref(v_ks_2917_);
                    return v___x_2921_;
                } else {
                    return v_newNode_2914_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_casesMatch_spec__1_spec__5_spec__8_spec__12___redArg(
    mut v_depth_2929_: usize,
    mut v_keys_2930_: *mut crate::leanh::LeanObject,
    mut v_vals_2931_: *mut crate::leanh::LeanObject,
    mut v_i_2932_: *mut crate::leanh::LeanObject,
    mut v_entries_2933_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2934_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2935_: u8 = 0;
    let mut v_k_2936_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_2937_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2938_: u64 = 0;
    let mut v_h_2939_: usize = 0;
    let mut v___x_2940_: usize = 0;
    let mut v___x_2941_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2942_: usize = 0;
    let mut v___x_2943_: usize = 0;
    let mut v___x_2944_: usize = 0;
    let mut v_h_2945_: usize = 0;
    let mut v___x_2946_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2947_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2934_ = lean_array_get_size(v_keys_2930_);
                v___x_2935_ = lean_nat_dec_lt(v_i_2932_, v___x_2934_);
                if v___x_2935_ == 0 {
                    crate::leanh::lean_dec(v_i_2932_);
                    return v_entries_2933_;
                } else {
                    v_k_2936_ = lean_array_fget_borrowed(v_keys_2930_, v_i_2932_);
                    v_v_2937_ = lean_array_fget_borrowed(v_vals_2931_, v_i_2932_);
                    v___x_2938_ = l_Lean_instHashableMVarId_hash(v_k_2936_);
                    v_h_2939_ = lean_uint64_to_usize(v___x_2938_);
                    v___x_2940_ = 5usize;
                    v___x_2941_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_2942_ = 1usize;
                    v___x_2943_ = lean_usize_sub(v_depth_2929_, v___x_2942_);
                    v___x_2944_ = lean_usize_mul(v___x_2940_, v___x_2943_);
                    v_h_2945_ = lean_usize_shift_right(v_h_2939_, v___x_2944_);
                    v___x_2946_ = lean_nat_add(v_i_2932_, v___x_2941_);
                    crate::leanh::lean_dec(v_i_2932_);
                    crate::leanh::lean_inc(v_v_2937_);
                    crate::leanh::lean_inc(v_k_2936_);
                    v___x_2947_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_casesMatch_spec__1_spec__5_spec__8___redArg(v_entries_2933_, v_h_2945_, v_depth_2929_, v_k_2936_, v_v_2937_);
                    v_i_2932_ = v___x_2946_;
                    v_entries_2933_ = v___x_2947_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_casesMatch_spec__1_spec__5_spec__8_spec__12___redArg___boxed(
    mut v_depth_2949_: *mut crate::leanh::LeanObject,
    mut v_keys_2950_: *mut crate::leanh::LeanObject,
    mut v_vals_2951_: *mut crate::leanh::LeanObject,
    mut v_i_2952_: *mut crate::leanh::LeanObject,
    mut v_entries_2953_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_depth_boxed_2954_: usize = 0;
    let mut v_res_2955_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_depth_boxed_2954_ = crate::leanh::lean_unbox_usize(v_depth_2949_);
    crate::leanh::lean_dec(v_depth_2949_);
    v_res_2955_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_casesMatch_spec__1_spec__5_spec__8_spec__12___redArg(v_depth_boxed_2954_, v_keys_2950_, v_vals_2951_, v_i_2952_, v_entries_2953_);
    crate::leanh::lean_dec_ref(v_vals_2951_);
    crate::leanh::lean_dec_ref(v_keys_2950_);
    return v_res_2955_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_casesMatch_spec__1_spec__5_spec__8___redArg___boxed(
    mut v_x_2956_: *mut crate::leanh::LeanObject,
    mut v_x_2957_: *mut crate::leanh::LeanObject,
    mut v_x_2958_: *mut crate::leanh::LeanObject,
    mut v_x_2959_: *mut crate::leanh::LeanObject,
    mut v_x_2960_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_9013__boxed_2961_: usize = 0;
    let mut v_x_9014__boxed_2962_: usize = 0;
    let mut v_res_2963_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_9013__boxed_2961_ = crate::leanh::lean_unbox_usize(v_x_2957_);
    crate::leanh::lean_dec(v_x_2957_);
    v_x_9014__boxed_2962_ = crate::leanh::lean_unbox_usize(v_x_2958_);
    crate::leanh::lean_dec(v_x_2958_);
    v_res_2963_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_casesMatch_spec__1_spec__5_spec__8___redArg(v_x_2956_, v_x_9013__boxed_2961_, v_x_9014__boxed_2962_, v_x_2959_, v_x_2960_);
    return v_res_2963_;
}
pub unsafe fn l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_casesMatch_spec__1_spec__5___redArg(
    mut v_x_2964_: *mut crate::leanh::LeanObject,
    mut v_x_2965_: *mut crate::leanh::LeanObject,
    mut v_x_2966_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2967_: u64 = 0;
    let mut v___x_2968_: usize = 0;
    let mut v___x_2969_: usize = 0;
    let mut v___x_2970_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2967_ = l_Lean_instHashableMVarId_hash(v_x_2965_);
    v___x_2968_ = lean_uint64_to_usize(v___x_2967_);
    v___x_2969_ = 1usize;
    v___x_2970_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_casesMatch_spec__1_spec__5_spec__8___redArg(v_x_2964_, v___x_2968_, v___x_2969_, v_x_2965_, v_x_2966_);
    return v___x_2970_;
}
pub unsafe fn l_Lean_MVarId_assign___at___00Lean_Meta_Grind_casesMatch_spec__1___redArg(
    mut v_mvarId_2971_: *mut crate::leanh::LeanObject,
    mut v_val_2972_: *mut crate::leanh::LeanObject,
    mut v___y_2973_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2975_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_2976_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_cache_2977_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_zetaDeltaFVarIds_2978_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_postponed_2979_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_diag_2980_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2982_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2983_: u8 = 0;
    let mut v_depth_2984_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_levelAssignDepth_2985_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_lmvarCounter_2986_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mvarCounter_2987_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_lDecls_2988_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_decls_2989_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_userNames_2990_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_lAssignment_2991_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_eAssignment_2992_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_dAssignment_2993_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2995_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2996_: u8 = 0;
    let mut v___x_2997_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2999_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3001_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3002_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3003_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3004_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3005_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3006_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3007_: u8 = 0;
    let mut v_isSharedCheck_3008_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2975_ = lean_st_ref_take(v___y_2973_);
                v_mctx_2976_ = crate::leanh::lean_ctor_get(v___x_2975_, 0);
                v_cache_2977_ = crate::leanh::lean_ctor_get(v___x_2975_, 1);
                v_zetaDeltaFVarIds_2978_ = crate::leanh::lean_ctor_get(v___x_2975_, 2);
                v_postponed_2979_ = crate::leanh::lean_ctor_get(v___x_2975_, 3);
                v_diag_2980_ = crate::leanh::lean_ctor_get(v___x_2975_, 4);
                v_isSharedCheck_3008_ = (!crate::leanh::lean_is_exclusive(v___x_2975_)) as u8;
                if v_isSharedCheck_3008_ == 0 {
                    v___x_2982_ = v___x_2975_;
                    v_isShared_2983_ = v_isSharedCheck_3008_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_diag_2980_);
                    crate::leanh::lean_inc(v_postponed_2979_);
                    crate::leanh::lean_inc(v_zetaDeltaFVarIds_2978_);
                    crate::leanh::lean_inc(v_cache_2977_);
                    crate::leanh::lean_inc(v_mctx_2976_);
                    crate::leanh::lean_dec(v___x_2975_);
                    v___x_2982_ = crate::leanh::lean_box(0);
                    v_isShared_2983_ = v_isSharedCheck_3008_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_depth_2984_ = crate::leanh::lean_ctor_get(v_mctx_2976_, 0);
                v_levelAssignDepth_2985_ = crate::leanh::lean_ctor_get(v_mctx_2976_, 1);
                v_lmvarCounter_2986_ = crate::leanh::lean_ctor_get(v_mctx_2976_, 2);
                v_mvarCounter_2987_ = crate::leanh::lean_ctor_get(v_mctx_2976_, 3);
                v_lDecls_2988_ = crate::leanh::lean_ctor_get(v_mctx_2976_, 4);
                v_decls_2989_ = crate::leanh::lean_ctor_get(v_mctx_2976_, 5);
                v_userNames_2990_ = crate::leanh::lean_ctor_get(v_mctx_2976_, 6);
                v_lAssignment_2991_ = crate::leanh::lean_ctor_get(v_mctx_2976_, 7);
                v_eAssignment_2992_ = crate::leanh::lean_ctor_get(v_mctx_2976_, 8);
                v_dAssignment_2993_ = crate::leanh::lean_ctor_get(v_mctx_2976_, 9);
                v_isSharedCheck_3007_ = (!crate::leanh::lean_is_exclusive(v_mctx_2976_)) as u8;
                if v_isSharedCheck_3007_ == 0 {
                    v___x_2995_ = v_mctx_2976_;
                    v_isShared_2996_ = v_isSharedCheck_3007_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_dAssignment_2993_);
                    crate::leanh::lean_inc(v_eAssignment_2992_);
                    crate::leanh::lean_inc(v_lAssignment_2991_);
                    crate::leanh::lean_inc(v_userNames_2990_);
                    crate::leanh::lean_inc(v_decls_2989_);
                    crate::leanh::lean_inc(v_lDecls_2988_);
                    crate::leanh::lean_inc(v_mvarCounter_2987_);
                    crate::leanh::lean_inc(v_lmvarCounter_2986_);
                    crate::leanh::lean_inc(v_levelAssignDepth_2985_);
                    crate::leanh::lean_inc(v_depth_2984_);
                    crate::leanh::lean_dec(v_mctx_2976_);
                    v___x_2995_ = crate::leanh::lean_box(0);
                    v_isShared_2996_ = v_isSharedCheck_3007_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_2997_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_casesMatch_spec__1_spec__5___redArg(v_eAssignment_2992_, v_mvarId_2971_, v_val_2972_);
                if v_isShared_2996_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2995_, 8, v___x_2997_);
                    v___x_2999_ = v___x_2995_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_3006_ = crate::leanh::lean_alloc_ctor(0, 10, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3006_, 0, v_depth_2984_);
                    crate::leanh::lean_ctor_set(
                        v_reuseFailAlloc_3006_,
                        1,
                        v_levelAssignDepth_2985_,
                    );
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3006_, 2, v_lmvarCounter_2986_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3006_, 3, v_mvarCounter_2987_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3006_, 4, v_lDecls_2988_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3006_, 5, v_decls_2989_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3006_, 6, v_userNames_2990_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3006_, 7, v_lAssignment_2991_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3006_, 8, v___x_2997_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3006_, 9, v_dAssignment_2993_);
                    v___x_2999_ = v_reuseFailAlloc_3006_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_2983_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2982_, 0, v___x_2999_);
                    v___x_3001_ = v___x_2982_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3005_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3005_, 0, v___x_2999_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3005_, 1, v_cache_2977_);
                    crate::leanh::lean_ctor_set(
                        v_reuseFailAlloc_3005_,
                        2,
                        v_zetaDeltaFVarIds_2978_,
                    );
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3005_, 3, v_postponed_2979_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3005_, 4, v_diag_2980_);
                    v___x_3001_ = v_reuseFailAlloc_3005_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_3002_ = lean_st_ref_set(v___y_2973_, v___x_3001_);
                v___x_3003_ = crate::leanh::lean_box(0);
                v___x_3004_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3004_, 0, v___x_3003_);
                return v___x_3004_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_MVarId_assign___at___00Lean_Meta_Grind_casesMatch_spec__1___redArg___boxed(
    mut v_mvarId_3009_: *mut crate::leanh::LeanObject,
    mut v_val_3010_: *mut crate::leanh::LeanObject,
    mut v___y_3011_: *mut crate::leanh::LeanObject,
    mut v___y_3012_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3013_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3013_ = l_Lean_MVarId_assign___at___00Lean_Meta_Grind_casesMatch_spec__1___redArg(
        v_mvarId_3009_,
        v_val_3010_,
        v___y_3011_,
    );
    crate::leanh::lean_dec(v___y_3011_);
    return v_res_3013_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_casesMatch___lam__0___closed__4()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3020_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3021_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3020_ = l_Lean_Meta_Grind_casesMatch___lam__0___closed__3;
    v___x_3021_ = l_Lean_stringToMessageData(v___x_3020_);
    return v___x_3021_;
}
pub unsafe fn l_Lean_Meta_Grind_casesMatch___lam__0(
    mut v_e_3022_: *mut crate::leanh::LeanObject,
    mut v___x_3023_: u8,
    mut v_mvarId_3024_: *mut crate::leanh::LeanObject,
    mut v___y_3025_: *mut crate::leanh::LeanObject,
    mut v___y_3026_: *mut crate::leanh::LeanObject,
    mut v___y_3027_: *mut crate::leanh::LeanObject,
    mut v___y_3028_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3030_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3031_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3032_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3033_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3034_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_3035_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3036_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3037_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3038_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toMatcherInfo_3039_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_matcherName_3040_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_matcherLevels_3041_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_params_3042_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_discrs_3043_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_alts_3044_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_us_3046_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3047_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3048_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3049_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3050_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3051_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3052_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_splitterName_3053_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3054_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3055_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3056_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3057_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3058_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3059_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3060_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3061_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3062_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3063_: u8 = 0;
    let mut v___x_3064_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3065_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_3066_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3067_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3068_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3069_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3070_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3072_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3073_: u8 = 0;
    let mut v___x_3074_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3075_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3076_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3078_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3079_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3080_: u8 = 0;
    let mut v_unused_3081_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3082_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3084_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3085_: u8 = 0;
    let mut v___x_3087_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3088_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3089_: u8 = 0;
    let mut v_a_3090_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3092_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3093_: u8 = 0;
    let mut v___x_3095_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3096_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3097_: u8 = 0;
    let mut v_a_3098_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3100_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3101_: u8 = 0;
    let mut v___x_3103_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3104_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3105_: u8 = 0;
    let mut v_a_3106_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3108_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3109_: u8 = 0;
    let mut v___x_3111_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3112_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3113_: u8 = 0;
    let mut v_uElimPos_x3f_3114_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3115_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3116_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3117_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3118_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3119_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3121_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3122_: u8 = 0;
    let mut v___x_3124_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3125_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3126_: u8 = 0;
    let mut v_a_3127_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3129_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3130_: u8 = 0;
    let mut v___x_3132_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3133_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3134_: u8 = 0;
    let mut v_a_3135_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3137_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3138_: u8 = 0;
    let mut v___x_3140_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3141_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3142_: u8 = 0;
    let mut v___x_3143_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3144_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3145_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3146_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3147_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3148_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3149_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3151_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3152_: u8 = 0;
    let mut v___x_3154_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3155_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3156_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                crate::leanh::lean_inc_ref(v_e_3022_);
                v___x_3030_ =
                    l_Lean_Meta_matchMatcherApp_x3f___at___00Lean_Meta_Grind_casesMatch_spec__0(
                        v_e_3022_,
                        v___x_3023_,
                        v___y_3025_,
                        v___y_3026_,
                        v___y_3027_,
                        v___y_3028_,
                    );
                if crate::leanh::lean_obj_tag(v___x_3030_) == 0 {
                    v_a_3031_ = crate::leanh::lean_ctor_get(v___x_3030_, 0);
                    crate::leanh::lean_inc(v_a_3031_);
                    crate::leanh::lean_dec_ref_known(v___x_3030_, 1);
                    if crate::leanh::lean_obj_tag(v_a_3031_) == 1 {
                        v_val_3032_ = crate::leanh::lean_ctor_get(v_a_3031_, 0);
                        crate::leanh::lean_inc_n(v_val_3032_, 2);
                        crate::leanh::lean_dec_ref_known(v_a_3031_, 1);
                        crate::leanh::lean_inc(v_mvarId_3024_);
                        v___x_3033_ = l___private_Lean_Meta_Tactic_Grind_CasesMatch_0__Lean_Meta_Grind_casesMatch_mkMotiveAndRefls(v_mvarId_3024_, v_e_3022_, v_val_3032_, v___y_3025_, v___y_3026_, v___y_3027_, v___y_3028_);
                        crate::leanh::lean_dec_ref(v_e_3022_);
                        if crate::leanh::lean_obj_tag(v___x_3033_) == 0 {
                            v_a_3034_ = crate::leanh::lean_ctor_get(v___x_3033_, 0);
                            crate::leanh::lean_inc(v_a_3034_);
                            crate::leanh::lean_dec_ref_known(v___x_3033_, 1);
                            v_fst_3035_ = crate::leanh::lean_ctor_get(v_a_3034_, 0);
                            crate::leanh::lean_inc(v_fst_3035_);
                            v_snd_3036_ = crate::leanh::lean_ctor_get(v_a_3034_, 1);
                            crate::leanh::lean_inc(v_snd_3036_);
                            crate::leanh::lean_dec(v_a_3034_);
                            crate::leanh::lean_inc(v_mvarId_3024_);
                            v___x_3037_ = l_Lean_MVarId_getType(
                                v_mvarId_3024_,
                                v___y_3025_,
                                v___y_3026_,
                                v___y_3027_,
                                v___y_3028_,
                            );
                            if crate::leanh::lean_obj_tag(v___x_3037_) == 0 {
                                v_a_3038_ = crate::leanh::lean_ctor_get(v___x_3037_, 0);
                                crate::leanh::lean_inc(v_a_3038_);
                                crate::leanh::lean_dec_ref_known(v___x_3037_, 1);
                                v_toMatcherInfo_3039_ = crate::leanh::lean_ctor_get(v_val_3032_, 0);
                                crate::leanh::lean_inc_ref(v_toMatcherInfo_3039_);
                                v_matcherName_3040_ = crate::leanh::lean_ctor_get(v_val_3032_, 1);
                                crate::leanh::lean_inc(v_matcherName_3040_);
                                v_matcherLevels_3041_ = crate::leanh::lean_ctor_get(v_val_3032_, 2);
                                crate::leanh::lean_inc_ref(v_matcherLevels_3041_);
                                v_params_3042_ = crate::leanh::lean_ctor_get(v_val_3032_, 3);
                                crate::leanh::lean_inc_ref(v_params_3042_);
                                v_discrs_3043_ = crate::leanh::lean_ctor_get(v_val_3032_, 5);
                                crate::leanh::lean_inc_ref(v_discrs_3043_);
                                v_alts_3044_ = crate::leanh::lean_ctor_get(v_val_3032_, 6);
                                crate::leanh::lean_inc_ref(v_alts_3044_);
                                crate::leanh::lean_dec(v_val_3032_);
                                v_uElimPos_x3f_3114_ =
                                    crate::leanh::lean_ctor_get(v_toMatcherInfo_3039_, 3);
                                crate::leanh::lean_inc(v_uElimPos_x3f_3114_);
                                crate::leanh::lean_dec_ref(v_toMatcherInfo_3039_);
                                if crate::leanh::lean_obj_tag(v_uElimPos_x3f_3114_) == 1 {
                                    v_val_3115_ =
                                        crate::leanh::lean_ctor_get(v_uElimPos_x3f_3114_, 0);
                                    crate::leanh::lean_inc(v_val_3115_);
                                    crate::leanh::lean_dec_ref_known(v_uElimPos_x3f_3114_, 1);
                                    v___x_3116_ = l_Lean_Meta_getLevel(
                                        v_a_3038_,
                                        v___y_3025_,
                                        v___y_3026_,
                                        v___y_3027_,
                                        v___y_3028_,
                                    );
                                    if crate::leanh::lean_obj_tag(v___x_3116_) == 0 {
                                        v_a_3117_ = crate::leanh::lean_ctor_get(v___x_3116_, 0);
                                        crate::leanh::lean_inc(v_a_3117_);
                                        crate::leanh::lean_dec_ref_known(v___x_3116_, 1);
                                        v___x_3118_ = lean_array_set(
                                            v_matcherLevels_3041_,
                                            v_val_3115_,
                                            v_a_3117_,
                                        );
                                        crate::leanh::lean_dec(v_val_3115_);
                                        v_us_3046_ = v___x_3118_;
                                        v___y_3047_ = v___y_3025_;
                                        v___y_3048_ = v___y_3026_;
                                        v___y_3049_ = v___y_3027_;
                                        v___y_3050_ = v___y_3028_;
                                        state = 1;
                                        continue;
                                    } else {
                                        crate::leanh::lean_dec(v_val_3115_);
                                        crate::leanh::lean_dec_ref(v_alts_3044_);
                                        crate::leanh::lean_dec_ref(v_discrs_3043_);
                                        crate::leanh::lean_dec_ref(v_params_3042_);
                                        crate::leanh::lean_dec_ref(v_matcherLevels_3041_);
                                        crate::leanh::lean_dec(v_matcherName_3040_);
                                        crate::leanh::lean_dec(v_snd_3036_);
                                        crate::leanh::lean_dec(v_fst_3035_);
                                        crate::leanh::lean_dec(v___y_3028_);
                                        crate::leanh::lean_dec_ref(v___y_3027_);
                                        crate::leanh::lean_dec(v___y_3026_);
                                        crate::leanh::lean_dec_ref(v___y_3025_);
                                        crate::leanh::lean_dec(v_mvarId_3024_);
                                        v_a_3119_ = crate::leanh::lean_ctor_get(v___x_3116_, 0);
                                        v_isSharedCheck_3126_ =
                                            (!crate::leanh::lean_is_exclusive(v___x_3116_)) as u8;
                                        if v_isSharedCheck_3126_ == 0 {
                                            v___x_3121_ = v___x_3116_;
                                            v_isShared_3122_ = v_isSharedCheck_3126_;
                                            state = 12;
                                            continue;
                                        } else {
                                            crate::leanh::lean_inc(v_a_3119_);
                                            crate::leanh::lean_dec(v___x_3116_);
                                            v___x_3121_ = crate::leanh::lean_box(0);
                                            v_isShared_3122_ = v_isSharedCheck_3126_;
                                            state = 12;
                                            continue;
                                        }
                                    }
                                } else {
                                    crate::leanh::lean_dec(v_uElimPos_x3f_3114_);
                                    crate::leanh::lean_dec(v_a_3038_);
                                    v_us_3046_ = v_matcherLevels_3041_;
                                    v___y_3047_ = v___y_3025_;
                                    v___y_3048_ = v___y_3026_;
                                    v___y_3049_ = v___y_3027_;
                                    v___y_3050_ = v___y_3028_;
                                    state = 1;
                                    continue;
                                }
                            } else {
                                crate::leanh::lean_dec(v_snd_3036_);
                                crate::leanh::lean_dec(v_fst_3035_);
                                crate::leanh::lean_dec(v_val_3032_);
                                crate::leanh::lean_dec(v___y_3028_);
                                crate::leanh::lean_dec_ref(v___y_3027_);
                                crate::leanh::lean_dec(v___y_3026_);
                                crate::leanh::lean_dec_ref(v___y_3025_);
                                crate::leanh::lean_dec(v_mvarId_3024_);
                                v_a_3127_ = crate::leanh::lean_ctor_get(v___x_3037_, 0);
                                v_isSharedCheck_3134_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_3037_)) as u8;
                                if v_isSharedCheck_3134_ == 0 {
                                    v___x_3129_ = v___x_3037_;
                                    v_isShared_3130_ = v_isSharedCheck_3134_;
                                    state = 14;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_a_3127_);
                                    crate::leanh::lean_dec(v___x_3037_);
                                    v___x_3129_ = crate::leanh::lean_box(0);
                                    v_isShared_3130_ = v_isSharedCheck_3134_;
                                    state = 14;
                                    continue;
                                }
                            }
                        } else {
                            crate::leanh::lean_dec(v_val_3032_);
                            crate::leanh::lean_dec(v___y_3028_);
                            crate::leanh::lean_dec_ref(v___y_3027_);
                            crate::leanh::lean_dec(v___y_3026_);
                            crate::leanh::lean_dec_ref(v___y_3025_);
                            crate::leanh::lean_dec(v_mvarId_3024_);
                            v_a_3135_ = crate::leanh::lean_ctor_get(v___x_3033_, 0);
                            v_isSharedCheck_3142_ =
                                (!crate::leanh::lean_is_exclusive(v___x_3033_)) as u8;
                            if v_isSharedCheck_3142_ == 0 {
                                v___x_3137_ = v___x_3033_;
                                v_isShared_3138_ = v_isSharedCheck_3142_;
                                state = 16;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_3135_);
                                crate::leanh::lean_dec(v___x_3033_);
                                v___x_3137_ = crate::leanh::lean_box(0);
                                v_isShared_3138_ = v_isSharedCheck_3142_;
                                state = 16;
                                continue;
                            }
                        }
                    } else {
                        crate::leanh::lean_dec(v_a_3031_);
                        v___x_3143_ = l_Lean_Meta_Grind_casesMatch___lam__0___closed__2;
                        v___x_3144_ = crate::leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(
                                l_Lean_Meta_Grind_casesMatch___lam__0___closed__4
                            ),
                            core::ptr::addr_of_mut!(
                                l_Lean_Meta_Grind_casesMatch___lam__0___closed__4_once
                            ),
                            _init_l_Lean_Meta_Grind_casesMatch___lam__0___closed__4,
                        );
                        v___x_3145_ = l_Lean_indentExpr(v_e_3022_);
                        v___x_3146_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_3146_, 0, v___x_3144_);
                        crate::leanh::lean_ctor_set(v___x_3146_, 1, v___x_3145_);
                        v___x_3147_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_3147_, 0, v___x_3146_);
                        v___x_3148_ = l_Lean_Meta_throwTacticEx___redArg(
                            v___x_3143_,
                            v_mvarId_3024_,
                            v___x_3147_,
                            v___y_3025_,
                            v___y_3026_,
                            v___y_3027_,
                            v___y_3028_,
                        );
                        crate::leanh::lean_dec(v___y_3028_);
                        crate::leanh::lean_dec_ref(v___y_3027_);
                        crate::leanh::lean_dec(v___y_3026_);
                        crate::leanh::lean_dec_ref(v___y_3025_);
                        return v___x_3148_;
                    }
                } else {
                    crate::leanh::lean_dec(v___y_3028_);
                    crate::leanh::lean_dec_ref(v___y_3027_);
                    crate::leanh::lean_dec(v___y_3026_);
                    crate::leanh::lean_dec_ref(v___y_3025_);
                    crate::leanh::lean_dec(v_mvarId_3024_);
                    crate::leanh::lean_dec_ref(v_e_3022_);
                    v_a_3149_ = crate::leanh::lean_ctor_get(v___x_3030_, 0);
                    v_isSharedCheck_3156_ = (!crate::leanh::lean_is_exclusive(v___x_3030_)) as u8;
                    if v_isSharedCheck_3156_ == 0 {
                        v___x_3151_ = v___x_3030_;
                        v_isShared_3152_ = v_isSharedCheck_3156_;
                        state = 18;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3149_);
                        crate::leanh::lean_dec(v___x_3030_);
                        v___x_3151_ = crate::leanh::lean_box(0);
                        v_isShared_3152_ = v_isSharedCheck_3156_;
                        state = 18;
                        continue;
                    }
                }
            }
            1 => {
                crate::leanh::lean_inc(v___y_3050_);
                crate::leanh::lean_inc_ref(v___y_3049_);
                crate::leanh::lean_inc(v___y_3048_);
                crate::leanh::lean_inc_ref(v___y_3047_);
                v___x_3051_ = lean_get_match_equations_for(
                    v_matcherName_3040_,
                    v___y_3047_,
                    v___y_3048_,
                    v___y_3049_,
                    v___y_3050_,
                );
                if crate::leanh::lean_obj_tag(v___x_3051_) == 0 {
                    v_a_3052_ = crate::leanh::lean_ctor_get(v___x_3051_, 0);
                    crate::leanh::lean_inc(v_a_3052_);
                    crate::leanh::lean_dec_ref_known(v___x_3051_, 1);
                    v_splitterName_3053_ = crate::leanh::lean_ctor_get(v_a_3052_, 1);
                    crate::leanh::lean_inc(v_splitterName_3053_);
                    crate::leanh::lean_dec(v_a_3052_);
                    v___x_3054_ = lean_array_to_list(v_us_3046_);
                    v___x_3055_ = l_Lean_mkConst(v_splitterName_3053_, v___x_3054_);
                    v___x_3056_ = l_Lean_mkAppN(v___x_3055_, v_params_3042_);
                    crate::leanh::lean_dec_ref(v_params_3042_);
                    v___x_3057_ = l_Lean_Expr_app___override(v___x_3056_, v_fst_3035_);
                    v___x_3058_ = l_Lean_mkAppN(v___x_3057_, v_discrs_3043_);
                    crate::leanh::lean_dec_ref(v_discrs_3043_);
                    crate::leanh::lean_inc(v___y_3050_);
                    crate::leanh::lean_inc_ref(v___y_3049_);
                    crate::leanh::lean_inc(v___y_3048_);
                    crate::leanh::lean_inc_ref(v___y_3047_);
                    crate::leanh::lean_inc_ref(v___x_3058_);
                    v___x_3059_ = lean_infer_type(
                        v___x_3058_,
                        v___y_3047_,
                        v___y_3048_,
                        v___y_3049_,
                        v___y_3050_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_3059_) == 0 {
                        v_a_3060_ = crate::leanh::lean_ctor_get(v___x_3059_, 0);
                        crate::leanh::lean_inc(v_a_3060_);
                        crate::leanh::lean_dec_ref_known(v___x_3059_, 1);
                        v___x_3061_ = lean_array_get_size(v_alts_3044_);
                        crate::leanh::lean_dec_ref(v_alts_3044_);
                        v___x_3062_ = l___private_Lean_Meta_Tactic_Grind_CasesMatch_0__Lean_Meta_Grind_addMatchCondsToSplitter(v_a_3060_, v___x_3061_);
                        v___x_3063_ = 2;
                        v___x_3064_ = l_Lean_Meta_forallMetaBoundedTelescope(
                            v___x_3062_,
                            v___x_3061_,
                            v___x_3063_,
                            v___y_3047_,
                            v___y_3048_,
                            v___y_3049_,
                            v___y_3050_,
                        );
                        if crate::leanh::lean_obj_tag(v___x_3064_) == 0 {
                            v_a_3065_ = crate::leanh::lean_ctor_get(v___x_3064_, 0);
                            crate::leanh::lean_inc(v_a_3065_);
                            crate::leanh::lean_dec_ref_known(v___x_3064_, 1);
                            v_fst_3066_ = crate::leanh::lean_ctor_get(v_a_3065_, 0);
                            crate::leanh::lean_inc(v_fst_3066_);
                            crate::leanh::lean_dec(v_a_3065_);
                            v___x_3067_ = l_Lean_mkAppN(v___x_3058_, v_fst_3066_);
                            v___x_3068_ = l_Lean_mkAppN(v___x_3067_, v_snd_3036_);
                            crate::leanh::lean_dec(v_snd_3036_);
                            crate::leanh::lean_inc(v_mvarId_3024_);
                            v___x_3069_ = l_Lean_MVarId_assign___at___00Lean_Meta_Grind_casesMatch_spec__1___redArg(v_mvarId_3024_, v___x_3068_, v___y_3048_);
                            crate::leanh::lean_dec_ref(v___x_3069_);
                            v___x_3070_ = l___private_Lean_Meta_Tactic_Grind_CasesMatch_0__Lean_Meta_Grind_casesMatch_updateTags(v_mvarId_3024_, v_fst_3066_, v___y_3047_, v___y_3048_, v___y_3049_, v___y_3050_);
                            crate::leanh::lean_dec(v___y_3050_);
                            crate::leanh::lean_dec_ref(v___y_3049_);
                            crate::leanh::lean_dec(v___y_3048_);
                            crate::leanh::lean_dec_ref(v___y_3047_);
                            if crate::leanh::lean_obj_tag(v___x_3070_) == 0 {
                                v_isSharedCheck_3080_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_3070_)) as u8;
                                if v_isSharedCheck_3080_ == 0 {
                                    v_unused_3081_ = crate::leanh::lean_ctor_get(v___x_3070_, 0);
                                    crate::leanh::lean_dec(v_unused_3081_);
                                    v___x_3072_ = v___x_3070_;
                                    v_isShared_3073_ = v_isSharedCheck_3080_;
                                    state = 2;
                                    continue;
                                } else {
                                    crate::leanh::lean_dec(v___x_3070_);
                                    v___x_3072_ = crate::leanh::lean_box(0);
                                    v_isShared_3073_ = v_isSharedCheck_3080_;
                                    state = 2;
                                    continue;
                                }
                            } else {
                                crate::leanh::lean_dec(v_fst_3066_);
                                v_a_3082_ = crate::leanh::lean_ctor_get(v___x_3070_, 0);
                                v_isSharedCheck_3089_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_3070_)) as u8;
                                if v_isSharedCheck_3089_ == 0 {
                                    v___x_3084_ = v___x_3070_;
                                    v_isShared_3085_ = v_isSharedCheck_3089_;
                                    state = 4;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_a_3082_);
                                    crate::leanh::lean_dec(v___x_3070_);
                                    v___x_3084_ = crate::leanh::lean_box(0);
                                    v_isShared_3085_ = v_isSharedCheck_3089_;
                                    state = 4;
                                    continue;
                                }
                            }
                        } else {
                            crate::leanh::lean_dec_ref(v___x_3058_);
                            crate::leanh::lean_dec(v___y_3050_);
                            crate::leanh::lean_dec_ref(v___y_3049_);
                            crate::leanh::lean_dec(v___y_3048_);
                            crate::leanh::lean_dec_ref(v___y_3047_);
                            crate::leanh::lean_dec(v_snd_3036_);
                            crate::leanh::lean_dec(v_mvarId_3024_);
                            v_a_3090_ = crate::leanh::lean_ctor_get(v___x_3064_, 0);
                            v_isSharedCheck_3097_ =
                                (!crate::leanh::lean_is_exclusive(v___x_3064_)) as u8;
                            if v_isSharedCheck_3097_ == 0 {
                                v___x_3092_ = v___x_3064_;
                                v_isShared_3093_ = v_isSharedCheck_3097_;
                                state = 6;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_3090_);
                                crate::leanh::lean_dec(v___x_3064_);
                                v___x_3092_ = crate::leanh::lean_box(0);
                                v_isShared_3093_ = v_isSharedCheck_3097_;
                                state = 6;
                                continue;
                            }
                        }
                    } else {
                        crate::leanh::lean_dec_ref(v___x_3058_);
                        crate::leanh::lean_dec(v___y_3050_);
                        crate::leanh::lean_dec_ref(v___y_3049_);
                        crate::leanh::lean_dec(v___y_3048_);
                        crate::leanh::lean_dec_ref(v___y_3047_);
                        crate::leanh::lean_dec_ref(v_alts_3044_);
                        crate::leanh::lean_dec(v_snd_3036_);
                        crate::leanh::lean_dec(v_mvarId_3024_);
                        v_a_3098_ = crate::leanh::lean_ctor_get(v___x_3059_, 0);
                        v_isSharedCheck_3105_ =
                            (!crate::leanh::lean_is_exclusive(v___x_3059_)) as u8;
                        if v_isSharedCheck_3105_ == 0 {
                            v___x_3100_ = v___x_3059_;
                            v_isShared_3101_ = v_isSharedCheck_3105_;
                            state = 8;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_3098_);
                            crate::leanh::lean_dec(v___x_3059_);
                            v___x_3100_ = crate::leanh::lean_box(0);
                            v_isShared_3101_ = v_isSharedCheck_3105_;
                            state = 8;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec(v___y_3050_);
                    crate::leanh::lean_dec_ref(v___y_3049_);
                    crate::leanh::lean_dec(v___y_3048_);
                    crate::leanh::lean_dec_ref(v___y_3047_);
                    crate::leanh::lean_dec_ref(v_us_3046_);
                    crate::leanh::lean_dec_ref(v_alts_3044_);
                    crate::leanh::lean_dec_ref(v_discrs_3043_);
                    crate::leanh::lean_dec_ref(v_params_3042_);
                    crate::leanh::lean_dec(v_snd_3036_);
                    crate::leanh::lean_dec(v_fst_3035_);
                    crate::leanh::lean_dec(v_mvarId_3024_);
                    v_a_3106_ = crate::leanh::lean_ctor_get(v___x_3051_, 0);
                    v_isSharedCheck_3113_ = (!crate::leanh::lean_is_exclusive(v___x_3051_)) as u8;
                    if v_isSharedCheck_3113_ == 0 {
                        v___x_3108_ = v___x_3051_;
                        v_isShared_3109_ = v_isSharedCheck_3113_;
                        state = 10;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3106_);
                        crate::leanh::lean_dec(v___x_3051_);
                        v___x_3108_ = crate::leanh::lean_box(0);
                        v_isShared_3109_ = v_isSharedCheck_3113_;
                        state = 10;
                        continue;
                    }
                }
            }
            2 => {
                v___x_3074_ = lean_array_to_list(v_fst_3066_);
                v___x_3075_ = crate::leanh::lean_box(0);
                v___x_3076_ = l_List_mapTR_loop___at___00Lean_Meta_Grind_casesMatch_spec__2(
                    v___x_3074_,
                    v___x_3075_,
                );
                if v_isShared_3073_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3072_, 0, v___x_3076_);
                    v___x_3078_ = v___x_3072_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_3079_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3079_, 0, v___x_3076_);
                    v___x_3078_ = v_reuseFailAlloc_3079_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_3078_;
            }
            4 => {
                if v_isShared_3085_ == 0 {
                    v___x_3087_ = v___x_3084_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_3088_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3088_, 0, v_a_3082_);
                    v___x_3087_ = v_reuseFailAlloc_3088_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_3087_;
            }
            6 => {
                if v_isShared_3093_ == 0 {
                    v___x_3095_ = v___x_3092_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_3096_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3096_, 0, v_a_3090_);
                    v___x_3095_ = v_reuseFailAlloc_3096_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_3095_;
            }
            8 => {
                if v_isShared_3101_ == 0 {
                    v___x_3103_ = v___x_3100_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_3104_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3104_, 0, v_a_3098_);
                    v___x_3103_ = v_reuseFailAlloc_3104_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_3103_;
            }
            10 => {
                if v_isShared_3109_ == 0 {
                    v___x_3111_ = v___x_3108_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_3112_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3112_, 0, v_a_3106_);
                    v___x_3111_ = v_reuseFailAlloc_3112_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                return v___x_3111_;
            }
            12 => {
                if v_isShared_3122_ == 0 {
                    v___x_3124_ = v___x_3121_;
                    state = 13;
                    continue;
                } else {
                    v_reuseFailAlloc_3125_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3125_, 0, v_a_3119_);
                    v___x_3124_ = v_reuseFailAlloc_3125_;
                    state = 13;
                    continue;
                }
            }
            13 => {
                return v___x_3124_;
            }
            14 => {
                if v_isShared_3130_ == 0 {
                    v___x_3132_ = v___x_3129_;
                    state = 15;
                    continue;
                } else {
                    v_reuseFailAlloc_3133_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3133_, 0, v_a_3127_);
                    v___x_3132_ = v_reuseFailAlloc_3133_;
                    state = 15;
                    continue;
                }
            }
            15 => {
                return v___x_3132_;
            }
            16 => {
                if v_isShared_3138_ == 0 {
                    v___x_3140_ = v___x_3137_;
                    state = 17;
                    continue;
                } else {
                    v_reuseFailAlloc_3141_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3141_, 0, v_a_3135_);
                    v___x_3140_ = v_reuseFailAlloc_3141_;
                    state = 17;
                    continue;
                }
            }
            17 => {
                return v___x_3140_;
            }
            18 => {
                if v_isShared_3152_ == 0 {
                    v___x_3154_ = v___x_3151_;
                    state = 19;
                    continue;
                } else {
                    v_reuseFailAlloc_3155_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3155_, 0, v_a_3149_);
                    v___x_3154_ = v_reuseFailAlloc_3155_;
                    state = 19;
                    continue;
                }
            }
            19 => {
                return v___x_3154_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Grind_casesMatch___lam__0___boxed(
    mut v_e_3157_: *mut crate::leanh::LeanObject,
    mut v___x_3158_: *mut crate::leanh::LeanObject,
    mut v_mvarId_3159_: *mut crate::leanh::LeanObject,
    mut v___y_3160_: *mut crate::leanh::LeanObject,
    mut v___y_3161_: *mut crate::leanh::LeanObject,
    mut v___y_3162_: *mut crate::leanh::LeanObject,
    mut v___y_3163_: *mut crate::leanh::LeanObject,
    mut v___y_3164_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_9248__boxed_3165_: u8 = 0;
    let mut v_res_3166_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_9248__boxed_3165_ = (crate::leanh::lean_unbox(v___x_3158_) as u8);
    v_res_3166_ = l_Lean_Meta_Grind_casesMatch___lam__0(
        v_e_3157_,
        v___x_9248__boxed_3165_,
        v_mvarId_3159_,
        v___y_3160_,
        v___y_3161_,
        v___y_3162_,
        v___y_3163_,
    );
    return v_res_3166_;
}
pub unsafe fn l_Lean_Meta_Grind_casesMatch(
    mut v_mvarId_3167_: *mut crate::leanh::LeanObject,
    mut v_e_3168_: *mut crate::leanh::LeanObject,
    mut v_a_3169_: *mut crate::leanh::LeanObject,
    mut v_a_3170_: *mut crate::leanh::LeanObject,
    mut v_a_3171_: *mut crate::leanh::LeanObject,
    mut v_a_3172_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3174_: u8 = 0;
    let mut v___x_3175_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3176_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3177_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3174_ = 0;
    v___x_3175_ = crate::leanh::lean_box((v___x_3174_) as usize);
    crate::leanh::lean_inc(v_mvarId_3167_);
    v___f_3176_ = crate::leanh::lean_alloc_closure(
        l_Lean_Meta_Grind_casesMatch___lam__0___boxed as *mut core::ffi::c_void,
        8,
        3,
    );
    crate::leanh::lean_closure_set(v___f_3176_, 0, v_e_3168_);
    crate::leanh::lean_closure_set(v___f_3176_, 1, v___x_3175_);
    crate::leanh::lean_closure_set(v___f_3176_, 2, v_mvarId_3167_);
    v___x_3177_ = l_Lean_MVarId_withContext___at___00Lean_Meta_Grind_casesMatch_spec__3___redArg(
        v_mvarId_3167_,
        v___f_3176_,
        v_a_3169_,
        v_a_3170_,
        v_a_3171_,
        v_a_3172_,
    );
    return v___x_3177_;
}
pub unsafe fn l_Lean_Meta_Grind_casesMatch___boxed(
    mut v_mvarId_3178_: *mut crate::leanh::LeanObject,
    mut v_e_3179_: *mut crate::leanh::LeanObject,
    mut v_a_3180_: *mut crate::leanh::LeanObject,
    mut v_a_3181_: *mut crate::leanh::LeanObject,
    mut v_a_3182_: *mut crate::leanh::LeanObject,
    mut v_a_3183_: *mut crate::leanh::LeanObject,
    mut v_a_3184_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3185_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3185_ = l_Lean_Meta_Grind_casesMatch(
        v_mvarId_3178_,
        v_e_3179_,
        v_a_3180_,
        v_a_3181_,
        v_a_3182_,
        v_a_3183_,
    );
    crate::leanh::lean_dec(v_a_3183_);
    crate::leanh::lean_dec_ref(v_a_3182_);
    crate::leanh::lean_dec(v_a_3181_);
    crate::leanh::lean_dec_ref(v_a_3180_);
    return v_res_3185_;
}
pub unsafe fn l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Meta_Grind_casesMatch_spec__0_spec__2(
    mut v_declName_3186_: *mut crate::leanh::LeanObject,
    mut v___y_3187_: *mut crate::leanh::LeanObject,
    mut v___y_3188_: *mut crate::leanh::LeanObject,
    mut v___y_3189_: *mut crate::leanh::LeanObject,
    mut v___y_3190_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3192_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3192_ = l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Meta_Grind_casesMatch_spec__0_spec__2___redArg(v_declName_3186_, v___y_3190_);
    return v___x_3192_;
}
pub unsafe fn l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Meta_Grind_casesMatch_spec__0_spec__2___boxed(
    mut v_declName_3193_: *mut crate::leanh::LeanObject,
    mut v___y_3194_: *mut crate::leanh::LeanObject,
    mut v___y_3195_: *mut crate::leanh::LeanObject,
    mut v___y_3196_: *mut crate::leanh::LeanObject,
    mut v___y_3197_: *mut crate::leanh::LeanObject,
    mut v___y_3198_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3199_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3199_ = l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Meta_Grind_casesMatch_spec__0_spec__2(v_declName_3193_, v___y_3194_, v___y_3195_, v___y_3196_, v___y_3197_);
    crate::leanh::lean_dec(v___y_3197_);
    crate::leanh::lean_dec_ref(v___y_3196_);
    crate::leanh::lean_dec(v___y_3195_);
    crate::leanh::lean_dec_ref(v___y_3194_);
    return v_res_3199_;
}
pub unsafe fn l_Lean_MVarId_assign___at___00Lean_Meta_Grind_casesMatch_spec__1(
    mut v_mvarId_3200_: *mut crate::leanh::LeanObject,
    mut v_val_3201_: *mut crate::leanh::LeanObject,
    mut v___y_3202_: *mut crate::leanh::LeanObject,
    mut v___y_3203_: *mut crate::leanh::LeanObject,
    mut v___y_3204_: *mut crate::leanh::LeanObject,
    mut v___y_3205_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3207_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3207_ = l_Lean_MVarId_assign___at___00Lean_Meta_Grind_casesMatch_spec__1___redArg(
        v_mvarId_3200_,
        v_val_3201_,
        v___y_3203_,
    );
    return v___x_3207_;
}
pub unsafe fn l_Lean_MVarId_assign___at___00Lean_Meta_Grind_casesMatch_spec__1___boxed(
    mut v_mvarId_3208_: *mut crate::leanh::LeanObject,
    mut v_val_3209_: *mut crate::leanh::LeanObject,
    mut v___y_3210_: *mut crate::leanh::LeanObject,
    mut v___y_3211_: *mut crate::leanh::LeanObject,
    mut v___y_3212_: *mut crate::leanh::LeanObject,
    mut v___y_3213_: *mut crate::leanh::LeanObject,
    mut v___y_3214_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3215_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3215_ = l_Lean_MVarId_assign___at___00Lean_Meta_Grind_casesMatch_spec__1(
        v_mvarId_3208_,
        v_val_3209_,
        v___y_3210_,
        v___y_3211_,
        v___y_3212_,
        v___y_3213_,
    );
    crate::leanh::lean_dec(v___y_3213_);
    crate::leanh::lean_dec_ref(v___y_3212_);
    crate::leanh::lean_dec(v___y_3211_);
    crate::leanh::lean_dec_ref(v___y_3210_);
    return v_res_3215_;
}
pub unsafe fn l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_casesMatch_spec__1_spec__5(
    mut v_00_u03b2_3216_: *mut crate::leanh::LeanObject,
    mut v_x_3217_: *mut crate::leanh::LeanObject,
    mut v_x_3218_: *mut crate::leanh::LeanObject,
    mut v_x_3219_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3220_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3220_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_casesMatch_spec__1_spec__5___redArg(v_x_3217_, v_x_3218_, v_x_3219_);
    return v___x_3220_;
}
pub unsafe fn l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Meta_Grind_casesMatch_spec__0_spec__0_spec__2(
    mut v_00_u03b1_3221_: *mut crate::leanh::LeanObject,
    mut v_constName_3222_: *mut crate::leanh::LeanObject,
    mut v___y_3223_: *mut crate::leanh::LeanObject,
    mut v___y_3224_: *mut crate::leanh::LeanObject,
    mut v___y_3225_: *mut crate::leanh::LeanObject,
    mut v___y_3226_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3228_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3228_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Meta_Grind_casesMatch_spec__0_spec__0_spec__2___redArg(v_constName_3222_, v___y_3223_, v___y_3224_, v___y_3225_, v___y_3226_);
    return v___x_3228_;
}
pub unsafe fn l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Meta_Grind_casesMatch_spec__0_spec__0_spec__2___boxed(
    mut v_00_u03b1_3229_: *mut crate::leanh::LeanObject,
    mut v_constName_3230_: *mut crate::leanh::LeanObject,
    mut v___y_3231_: *mut crate::leanh::LeanObject,
    mut v___y_3232_: *mut crate::leanh::LeanObject,
    mut v___y_3233_: *mut crate::leanh::LeanObject,
    mut v___y_3234_: *mut crate::leanh::LeanObject,
    mut v___y_3235_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3236_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3236_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Meta_Grind_casesMatch_spec__0_spec__0_spec__2(v_00_u03b1_3229_, v_constName_3230_, v___y_3231_, v___y_3232_, v___y_3233_, v___y_3234_);
    crate::leanh::lean_dec(v___y_3234_);
    crate::leanh::lean_dec_ref(v___y_3233_);
    crate::leanh::lean_dec(v___y_3232_);
    crate::leanh::lean_dec_ref(v___y_3231_);
    return v_res_3236_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_casesMatch_spec__1_spec__5_spec__8(
    mut v_00_u03b2_3237_: *mut crate::leanh::LeanObject,
    mut v_x_3238_: *mut crate::leanh::LeanObject,
    mut v_x_3239_: usize,
    mut v_x_3240_: usize,
    mut v_x_3241_: *mut crate::leanh::LeanObject,
    mut v_x_3242_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3243_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3243_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_casesMatch_spec__1_spec__5_spec__8___redArg(v_x_3238_, v_x_3239_, v_x_3240_, v_x_3241_, v_x_3242_);
    return v___x_3243_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_casesMatch_spec__1_spec__5_spec__8___boxed(
    mut v_00_u03b2_3244_: *mut crate::leanh::LeanObject,
    mut v_x_3245_: *mut crate::leanh::LeanObject,
    mut v_x_3246_: *mut crate::leanh::LeanObject,
    mut v_x_3247_: *mut crate::leanh::LeanObject,
    mut v_x_3248_: *mut crate::leanh::LeanObject,
    mut v_x_3249_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_9585__boxed_3250_: usize = 0;
    let mut v_x_9586__boxed_3251_: usize = 0;
    let mut v_res_3252_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_9585__boxed_3250_ = crate::leanh::lean_unbox_usize(v_x_3246_);
    crate::leanh::lean_dec(v_x_3246_);
    v_x_9586__boxed_3251_ = crate::leanh::lean_unbox_usize(v_x_3247_);
    crate::leanh::lean_dec(v_x_3247_);
    v_res_3252_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_casesMatch_spec__1_spec__5_spec__8(v_00_u03b2_3244_, v_x_3245_, v_x_9585__boxed_3250_, v_x_9586__boxed_3251_, v_x_3248_, v_x_3249_);
    return v_res_3252_;
}
pub unsafe fn l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Meta_Grind_casesMatch_spec__0_spec__0_spec__2_spec__7(
    mut v_00_u03b1_3253_: *mut crate::leanh::LeanObject,
    mut v_ref_3254_: *mut crate::leanh::LeanObject,
    mut v_constName_3255_: *mut crate::leanh::LeanObject,
    mut v___y_3256_: *mut crate::leanh::LeanObject,
    mut v___y_3257_: *mut crate::leanh::LeanObject,
    mut v___y_3258_: *mut crate::leanh::LeanObject,
    mut v___y_3259_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3261_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3261_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Meta_Grind_casesMatch_spec__0_spec__0_spec__2_spec__7___redArg(v_ref_3254_, v_constName_3255_, v___y_3256_, v___y_3257_, v___y_3258_, v___y_3259_);
    return v___x_3261_;
}
pub unsafe fn l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Meta_Grind_casesMatch_spec__0_spec__0_spec__2_spec__7___boxed(
    mut v_00_u03b1_3262_: *mut crate::leanh::LeanObject,
    mut v_ref_3263_: *mut crate::leanh::LeanObject,
    mut v_constName_3264_: *mut crate::leanh::LeanObject,
    mut v___y_3265_: *mut crate::leanh::LeanObject,
    mut v___y_3266_: *mut crate::leanh::LeanObject,
    mut v___y_3267_: *mut crate::leanh::LeanObject,
    mut v___y_3268_: *mut crate::leanh::LeanObject,
    mut v___y_3269_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3270_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3270_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Meta_Grind_casesMatch_spec__0_spec__0_spec__2_spec__7(v_00_u03b1_3262_, v_ref_3263_, v_constName_3264_, v___y_3265_, v___y_3266_, v___y_3267_, v___y_3268_);
    crate::leanh::lean_dec(v___y_3268_);
    crate::leanh::lean_dec_ref(v___y_3267_);
    crate::leanh::lean_dec(v___y_3266_);
    crate::leanh::lean_dec_ref(v___y_3265_);
    crate::leanh::lean_dec(v_ref_3263_);
    return v_res_3270_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_casesMatch_spec__1_spec__5_spec__8_spec__11(
    mut v_00_u03b2_3271_: *mut crate::leanh::LeanObject,
    mut v_n_3272_: *mut crate::leanh::LeanObject,
    mut v_k_3273_: *mut crate::leanh::LeanObject,
    mut v_v_3274_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3275_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3275_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_casesMatch_spec__1_spec__5_spec__8_spec__11___redArg(v_n_3272_, v_k_3273_, v_v_3274_);
    return v___x_3275_;
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_casesMatch_spec__1_spec__5_spec__8_spec__12(
    mut v_00_u03b2_3276_: *mut crate::leanh::LeanObject,
    mut v_depth_3277_: usize,
    mut v_keys_3278_: *mut crate::leanh::LeanObject,
    mut v_vals_3279_: *mut crate::leanh::LeanObject,
    mut v_heq_3280_: *mut crate::leanh::LeanObject,
    mut v_i_3281_: *mut crate::leanh::LeanObject,
    mut v_entries_3282_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3283_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3283_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_casesMatch_spec__1_spec__5_spec__8_spec__12___redArg(v_depth_3277_, v_keys_3278_, v_vals_3279_, v_i_3281_, v_entries_3282_);
    return v___x_3283_;
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_casesMatch_spec__1_spec__5_spec__8_spec__12___boxed(
    mut v_00_u03b2_3284_: *mut crate::leanh::LeanObject,
    mut v_depth_3285_: *mut crate::leanh::LeanObject,
    mut v_keys_3286_: *mut crate::leanh::LeanObject,
    mut v_vals_3287_: *mut crate::leanh::LeanObject,
    mut v_heq_3288_: *mut crate::leanh::LeanObject,
    mut v_i_3289_: *mut crate::leanh::LeanObject,
    mut v_entries_3290_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_depth_boxed_3291_: usize = 0;
    let mut v_res_3292_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_depth_boxed_3291_ = crate::leanh::lean_unbox_usize(v_depth_3285_);
    crate::leanh::lean_dec(v_depth_3285_);
    v_res_3292_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_casesMatch_spec__1_spec__5_spec__8_spec__12(v_00_u03b2_3284_, v_depth_boxed_3291_, v_keys_3286_, v_vals_3287_, v_heq_3288_, v_i_3289_, v_entries_3290_);
    crate::leanh::lean_dec_ref(v_vals_3287_);
    crate::leanh::lean_dec_ref(v_keys_3286_);
    return v_res_3292_;
}
pub unsafe fn l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Meta_Grind_casesMatch_spec__0_spec__0_spec__2_spec__7_spec__10(
    mut v_00_u03b1_3293_: *mut crate::leanh::LeanObject,
    mut v_ref_3294_: *mut crate::leanh::LeanObject,
    mut v_msg_3295_: *mut crate::leanh::LeanObject,
    mut v_declHint_3296_: *mut crate::leanh::LeanObject,
    mut v___y_3297_: *mut crate::leanh::LeanObject,
    mut v___y_3298_: *mut crate::leanh::LeanObject,
    mut v___y_3299_: *mut crate::leanh::LeanObject,
    mut v___y_3300_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3302_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3302_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Meta_Grind_casesMatch_spec__0_spec__0_spec__2_spec__7_spec__10___redArg(v_ref_3294_, v_msg_3295_, v_declHint_3296_, v___y_3297_, v___y_3298_, v___y_3299_, v___y_3300_);
    return v___x_3302_;
}
pub unsafe fn l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Meta_Grind_casesMatch_spec__0_spec__0_spec__2_spec__7_spec__10___boxed(
    mut v_00_u03b1_3303_: *mut crate::leanh::LeanObject,
    mut v_ref_3304_: *mut crate::leanh::LeanObject,
    mut v_msg_3305_: *mut crate::leanh::LeanObject,
    mut v_declHint_3306_: *mut crate::leanh::LeanObject,
    mut v___y_3307_: *mut crate::leanh::LeanObject,
    mut v___y_3308_: *mut crate::leanh::LeanObject,
    mut v___y_3309_: *mut crate::leanh::LeanObject,
    mut v___y_3310_: *mut crate::leanh::LeanObject,
    mut v___y_3311_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3312_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3312_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Meta_Grind_casesMatch_spec__0_spec__0_spec__2_spec__7_spec__10(v_00_u03b1_3303_, v_ref_3304_, v_msg_3305_, v_declHint_3306_, v___y_3307_, v___y_3308_, v___y_3309_, v___y_3310_);
    crate::leanh::lean_dec(v___y_3310_);
    crate::leanh::lean_dec_ref(v___y_3309_);
    crate::leanh::lean_dec(v___y_3308_);
    crate::leanh::lean_dec_ref(v___y_3307_);
    crate::leanh::lean_dec(v_ref_3304_);
    return v_res_3312_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_casesMatch_spec__1_spec__5_spec__8_spec__11_spec__13(
    mut v_00_u03b2_3313_: *mut crate::leanh::LeanObject,
    mut v_x_3314_: *mut crate::leanh::LeanObject,
    mut v_x_3315_: *mut crate::leanh::LeanObject,
    mut v_x_3316_: *mut crate::leanh::LeanObject,
    mut v_x_3317_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3318_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3318_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_casesMatch_spec__1_spec__5_spec__8_spec__11_spec__13___redArg(v_x_3314_, v_x_3315_, v_x_3316_, v_x_3317_);
    return v___x_3318_;
}
pub unsafe fn l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Meta_Grind_casesMatch_spec__0_spec__0_spec__2_spec__7_spec__10_spec__12_spec__15(
    mut v_msg_3319_: *mut crate::leanh::LeanObject,
    mut v_declHint_3320_: *mut crate::leanh::LeanObject,
    mut v___y_3321_: *mut crate::leanh::LeanObject,
    mut v___y_3322_: *mut crate::leanh::LeanObject,
    mut v___y_3323_: *mut crate::leanh::LeanObject,
    mut v___y_3324_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3326_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3326_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Meta_Grind_casesMatch_spec__0_spec__0_spec__2_spec__7_spec__10_spec__12_spec__15___redArg(v_msg_3319_, v_declHint_3320_, v___y_3324_);
    return v___x_3326_;
}
pub unsafe fn l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Meta_Grind_casesMatch_spec__0_spec__0_spec__2_spec__7_spec__10_spec__12_spec__15___boxed(
    mut v_msg_3327_: *mut crate::leanh::LeanObject,
    mut v_declHint_3328_: *mut crate::leanh::LeanObject,
    mut v___y_3329_: *mut crate::leanh::LeanObject,
    mut v___y_3330_: *mut crate::leanh::LeanObject,
    mut v___y_3331_: *mut crate::leanh::LeanObject,
    mut v___y_3332_: *mut crate::leanh::LeanObject,
    mut v___y_3333_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3334_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3334_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Meta_Grind_casesMatch_spec__0_spec__0_spec__2_spec__7_spec__10_spec__12_spec__15(v_msg_3327_, v_declHint_3328_, v___y_3329_, v___y_3330_, v___y_3331_, v___y_3332_);
    crate::leanh::lean_dec(v___y_3332_);
    crate::leanh::lean_dec_ref(v___y_3331_);
    crate::leanh::lean_dec(v___y_3330_);
    crate::leanh::lean_dec_ref(v___y_3329_);
    return v_res_3334_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Meta_Grind_casesMatch_spec__0_spec__0_spec__2_spec__7_spec__10_spec__13(
    mut v_00_u03b1_3335_: *mut crate::leanh::LeanObject,
    mut v_ref_3336_: *mut crate::leanh::LeanObject,
    mut v_msg_3337_: *mut crate::leanh::LeanObject,
    mut v___y_3338_: *mut crate::leanh::LeanObject,
    mut v___y_3339_: *mut crate::leanh::LeanObject,
    mut v___y_3340_: *mut crate::leanh::LeanObject,
    mut v___y_3341_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3343_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3343_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Meta_Grind_casesMatch_spec__0_spec__0_spec__2_spec__7_spec__10_spec__13___redArg(v_ref_3336_, v_msg_3337_, v___y_3338_, v___y_3339_, v___y_3340_, v___y_3341_);
    return v___x_3343_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Meta_Grind_casesMatch_spec__0_spec__0_spec__2_spec__7_spec__10_spec__13___boxed(
    mut v_00_u03b1_3344_: *mut crate::leanh::LeanObject,
    mut v_ref_3345_: *mut crate::leanh::LeanObject,
    mut v_msg_3346_: *mut crate::leanh::LeanObject,
    mut v___y_3347_: *mut crate::leanh::LeanObject,
    mut v___y_3348_: *mut crate::leanh::LeanObject,
    mut v___y_3349_: *mut crate::leanh::LeanObject,
    mut v___y_3350_: *mut crate::leanh::LeanObject,
    mut v___y_3351_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3352_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3352_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Meta_Grind_casesMatch_spec__0_spec__0_spec__2_spec__7_spec__10_spec__13(v_00_u03b1_3344_, v_ref_3345_, v_msg_3346_, v___y_3347_, v___y_3348_, v___y_3349_, v___y_3350_);
    crate::leanh::lean_dec(v___y_3350_);
    crate::leanh::lean_dec_ref(v___y_3349_);
    crate::leanh::lean_dec(v___y_3348_);
    crate::leanh::lean_dec_ref(v___y_3347_);
    crate::leanh::lean_dec(v_ref_3345_);
    return v_res_3352_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Meta_Grind_casesMatch_spec__0_spec__0_spec__2_spec__7_spec__10_spec__13_spec__17(
    mut v_00_u03b1_3353_: *mut crate::leanh::LeanObject,
    mut v_msg_3354_: *mut crate::leanh::LeanObject,
    mut v___y_3355_: *mut crate::leanh::LeanObject,
    mut v___y_3356_: *mut crate::leanh::LeanObject,
    mut v___y_3357_: *mut crate::leanh::LeanObject,
    mut v___y_3358_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3360_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3360_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Meta_Grind_casesMatch_spec__0_spec__0_spec__2_spec__7_spec__10_spec__13_spec__17___redArg(v_msg_3354_, v___y_3355_, v___y_3356_, v___y_3357_, v___y_3358_);
    return v___x_3360_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Meta_Grind_casesMatch_spec__0_spec__0_spec__2_spec__7_spec__10_spec__13_spec__17___boxed(
    mut v_00_u03b1_3361_: *mut crate::leanh::LeanObject,
    mut v_msg_3362_: *mut crate::leanh::LeanObject,
    mut v___y_3363_: *mut crate::leanh::LeanObject,
    mut v___y_3364_: *mut crate::leanh::LeanObject,
    mut v___y_3365_: *mut crate::leanh::LeanObject,
    mut v___y_3366_: *mut crate::leanh::LeanObject,
    mut v___y_3367_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3368_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3368_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Meta_Grind_casesMatch_spec__0_spec__0_spec__2_spec__7_spec__10_spec__13_spec__17(v_00_u03b1_3361_, v_msg_3362_, v___y_3363_, v___y_3364_, v___y_3365_, v___y_3366_);
    crate::leanh::lean_dec(v___y_3366_);
    crate::leanh::lean_dec_ref(v___y_3365_);
    crate::leanh::lean_dec(v___y_3364_);
    crate::leanh::lean_dec_ref(v___y_3363_);
    return v_res_3368_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Meta_Tactic_Grind_CasesMatch(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Meta_Tactic_Util(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Grind_Util(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Match_MatcherApp(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Cases(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Meta_Tactic_Grind_CasesMatch(
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
pub unsafe fn initialize_Lean_Meta_Tactic_Grind_CasesMatch(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Meta_Tactic_Util(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Meta_Tactic_Grind_Util(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Meta_Match_MatcherApp(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Meta_Tactic_Cases(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Grind_CasesMatch(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Meta_Tactic_Grind_CasesMatch(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Lean_Meta_Tactic_Grind_CasesMatch(builtin);
}
