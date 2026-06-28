// Lean compiler output
// Module: Lean.Meta.Tactic.Grind.CasesMatch
// Imports: Lean.Meta.Tactic.Util Lean.Meta.Tactic.Grind.Util Lean.Meta.Match.MatcherApp Lean.Meta.Tactic.Cases
use crate::r#gen::Init::Control::StateRef::l_StateRefT_x27_instMonad___redArg;
use crate::r#gen::Init::Data::Array::Subarray::l_Array_toSubarray___redArg;
use crate::r#gen::Init::Data::List::Basic::l_List_reverse___redArg;
use crate::r#gen::Init::Data::Slice::Array::Iterator::l_Subarray_copy___redArg;
use crate::r#gen::Init::Prelude::{
    l_Array_extract___redArg, l_Lean_Name_mkStr1, l_Lean_Name_mkStr2, l_Lean_Name_num___override,
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
use crate::lean_imports_rs::Init::Data::Array::Basic::{
    lean_array_size, lean_array_uget_borrowed, lean_array_uset, lean_mk_array,
};
use crate::lean_imports_rs::Init::Data::Array::Set::{lean_array_fset, lean_array_set};
use crate::lean_imports_rs::Init::Data::UInt::Basic::{
    lean_uint64_to_usize, lean_usize_land, lean_usize_mul, lean_usize_shift_left,
    lean_usize_shift_right,
};
use crate::lean_imports_rs::Init::Data::UInt::BasicAux::{
    lean_usize_add, lean_usize_dec_le, lean_usize_dec_lt, lean_usize_sub, lean_usize_to_nat,
};
use crate::lean_imports_rs::Init::Prelude::{
    lean_array_fget, lean_array_fget_borrowed, lean_array_get, lean_array_get_borrowed,
    lean_array_get_size, lean_array_mk, lean_array_push, lean_array_to_list,
    lean_mk_empty_array_with_capacity, lean_nat_add, lean_nat_dec_eq, lean_nat_dec_le,
    lean_nat_dec_lt, lean_nat_sub, lean_panic_fn_borrowed, lean_usize_dec_eq,
};
use crate::lean_imports_rs::Init::System::ST::{
    lean_st_ref_get, lean_st_ref_set, lean_st_ref_take,
};
use crate::lean_imports_rs::Init::Util::lean_ptr_addr;
use crate::lean_imports_rs::Lean::Expr::lean_expr_has_loose_bvar;
use crate::lean_imports_rs::Lean::Meta::Basic::lean_infer_type;
use crate::lean_imports_rs::Lean::Meta::Match::MatchEqsExt::lean_get_match_equations_for;
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_alloc_closure, lean_alloc_ctor, lean_apply_5,
    lean_apply_7, lean_box, lean_closure_set, lean_ctor_get, lean_ctor_get_uint8, lean_ctor_set,
    lean_ctor_set_tag, lean_ctor_set_uint8, lean_ctor_set_usize, lean_dec, lean_dec_ref,
    lean_dec_ref_known, lean_del_object, lean_inc, lean_inc_n, lean_inc_ref, lean_inc_ref_n,
    lean_io_result_is_error, lean_io_result_mk_ok, lean_is_exclusive, lean_obj_once, lean_obj_tag,
    lean_unbox, lean_unbox_usize, lean_unsigned_to_nat, lean_usize_once,
};
pub static l___private_Lean_Meta_Tactic_Grind_CasesMatch_0__Lean_Meta_Grind_isMatchCondCandidate_go___closed__0_value: LeanStringObject<3> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [69, 113, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_CasesMatch_0__Lean_Meta_Grind_isMatchCondCandidate_go___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_CasesMatch_0__Lean_Meta_Grind_isMatchCondCandidate_go___closed__0_value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_CasesMatch_0__Lean_Meta_Grind_isMatchCondCandidate_go___closed__1_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_CasesMatch_0__Lean_Meta_Grind_isMatchCondCandidate_go___closed__0_value) as *mut LeanObject,16122875713692181903 as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_CasesMatch_0__Lean_Meta_Grind_isMatchCondCandidate_go___closed__1: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_CasesMatch_0__Lean_Meta_Grind_isMatchCondCandidate_go___closed__1_value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_CasesMatch_0__Lean_Meta_Grind_isMatchCondCandidate_go___closed__2_value: LeanStringObject<4> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [72, 69, 113, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_CasesMatch_0__Lean_Meta_Grind_isMatchCondCandidate_go___closed__2: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_CasesMatch_0__Lean_Meta_Grind_isMatchCondCandidate_go___closed__2_value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_CasesMatch_0__Lean_Meta_Grind_isMatchCondCandidate_go___closed__3_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_CasesMatch_0__Lean_Meta_Grind_isMatchCondCandidate_go___closed__2_value) as *mut LeanObject,13589827700912665667 as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_CasesMatch_0__Lean_Meta_Grind_isMatchCondCandidate_go___closed__3: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_CasesMatch_0__Lean_Meta_Grind_isMatchCondCandidate_go___closed__3_value) as *mut LeanObject;
static mut l___private_Lean_Meta_Tactic_Grind_CasesMatch_0__Lean_Meta_Grind_casesMatch_mkMotiveAndRefls___closed__0_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_CasesMatch_0__Lean_Meta_Grind_casesMatch_mkMotiveAndRefls___closed__0: *mut LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_Tactic_Grind_CasesMatch_0__Lean_Meta_Grind_casesMatch_mkMotiveAndRefls___closed__1_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_CasesMatch_0__Lean_Meta_Grind_casesMatch_mkMotiveAndRefls___closed__1: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Meta_Grind_casesMatch_spec__0_spec__0_spec__2_spec__7_spec__10_spec__12_spec__15___redArg___closed__0_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Meta_Grind_casesMatch_spec__0_spec__0_spec__2_spec__7_spec__10_spec__12_spec__15___redArg___closed__0: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Meta_Grind_casesMatch_spec__0_spec__0_spec__2_spec__7_spec__10_spec__12_spec__15___redArg___closed__1_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Meta_Grind_casesMatch_spec__0_spec__0_spec__2_spec__7_spec__10_spec__12_spec__15___redArg___closed__1: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Meta_Grind_casesMatch_spec__0_spec__0_spec__2_spec__7_spec__10_spec__12_spec__15___redArg___closed__2_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Meta_Grind_casesMatch_spec__0_spec__0_spec__2_spec__7_spec__10_spec__12_spec__15___redArg___closed__2: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Meta_Grind_casesMatch_spec__0_spec__0_spec__2_spec__7_spec__10_spec__12_spec__15___redArg___closed__3_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Meta_Grind_casesMatch_spec__0_spec__0_spec__2_spec__7_spec__10_spec__12_spec__15___redArg___closed__3: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Meta_Grind_casesMatch_spec__0_spec__0_spec__2_spec__7_spec__10_spec__12_spec__15___redArg___closed__4_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Meta_Grind_casesMatch_spec__0_spec__0_spec__2_spec__7_spec__10_spec__12_spec__15___redArg___closed__4: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Meta_Grind_casesMatch_spec__0_spec__0_spec__2_spec__7_spec__10_spec__12_spec__15___redArg___closed__5_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Meta_Grind_casesMatch_spec__0_spec__0_spec__2_spec__7_spec__10_spec__12_spec__15___redArg___closed__5: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Meta_Grind_casesMatch_spec__0_spec__0_spec__2_spec__7_spec__10_spec__12_spec__15___redArg___closed__6_value: LeanStringObject<24> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 24, m_capacity: 24, m_length: 23, m_data: [65, 32, 112, 114, 105, 118, 97, 116, 101, 32, 100, 101, 99, 108, 97, 114, 97, 116, 105, 111, 110, 32, 96, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Meta_Grind_casesMatch_spec__0_spec__0_spec__2_spec__7_spec__10_spec__12_spec__15___redArg___closed__6: *mut LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Meta_Grind_casesMatch_spec__0_spec__0_spec__2_spec__7_spec__10_spec__12_spec__15___redArg___closed__6_value) as *mut LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Meta_Grind_casesMatch_spec__0_spec__0_spec__2_spec__7_spec__10_spec__12_spec__15___redArg___closed__7_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Meta_Grind_casesMatch_spec__0_spec__0_spec__2_spec__7_spec__10_spec__12_spec__15___redArg___closed__7: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Meta_Grind_casesMatch_spec__0_spec__0_spec__2_spec__7_spec__10_spec__12_spec__15___redArg___closed__8_value: LeanStringObject<79> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 79, m_capacity: 79, m_length: 78, m_data: [96, 32, 40, 102, 114, 111, 109, 32, 116, 104, 101, 32, 99, 117, 114, 114, 101, 110, 116, 32, 109, 111, 100, 117, 108, 101, 41, 32, 101, 120, 105, 115, 116, 115, 32, 98, 117, 116, 32, 119, 111, 117, 108, 100, 32, 110, 101, 101, 100, 32, 116, 111, 32, 98, 101, 32, 112, 117, 98, 108, 105, 99, 32, 116, 111, 32, 97, 99, 99, 101, 115, 115, 32, 104, 101, 114, 101, 46, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Meta_Grind_casesMatch_spec__0_spec__0_spec__2_spec__7_spec__10_spec__12_spec__15___redArg___closed__8: *mut LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Meta_Grind_casesMatch_spec__0_spec__0_spec__2_spec__7_spec__10_spec__12_spec__15___redArg___closed__8_value) as *mut LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Meta_Grind_casesMatch_spec__0_spec__0_spec__2_spec__7_spec__10_spec__12_spec__15___redArg___closed__9_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Meta_Grind_casesMatch_spec__0_spec__0_spec__2_spec__7_spec__10_spec__12_spec__15___redArg___closed__9: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Meta_Grind_casesMatch_spec__0_spec__0_spec__2_spec__7_spec__10_spec__12_spec__15___redArg___closed__10_value: LeanStringObject<23> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 23, m_capacity: 23, m_length: 22, m_data: [65, 32, 112, 117, 98, 108, 105, 99, 32, 100, 101, 99, 108, 97, 114, 97, 116, 105, 111, 110, 32, 96, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Meta_Grind_casesMatch_spec__0_spec__0_spec__2_spec__7_spec__10_spec__12_spec__15___redArg___closed__10: *mut LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Meta_Grind_casesMatch_spec__0_spec__0_spec__2_spec__7_spec__10_spec__12_spec__15___redArg___closed__10_value) as *mut LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Meta_Grind_casesMatch_spec__0_spec__0_spec__2_spec__7_spec__10_spec__12_spec__15___redArg___closed__11_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Meta_Grind_casesMatch_spec__0_spec__0_spec__2_spec__7_spec__10_spec__12_spec__15___redArg___closed__11: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Meta_Grind_casesMatch_spec__0_spec__0_spec__2_spec__7_spec__10_spec__12_spec__15___redArg___closed__12_value: LeanStringObject<68> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 68, m_capacity: 68, m_length: 67, m_data: [96, 32, 101, 120, 105, 115, 116, 115, 32, 98, 117, 116, 32, 105, 115, 32, 105, 109, 112, 111, 114, 116, 101, 100, 32, 112, 114, 105, 118, 97, 116, 101, 108, 121, 59, 32, 99, 111, 110, 115, 105, 100, 101, 114, 32, 97, 100, 100, 105, 110, 103, 32, 96, 112, 117, 98, 108, 105, 99, 32, 105, 109, 112, 111, 114, 116, 32, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Meta_Grind_casesMatch_spec__0_spec__0_spec__2_spec__7_spec__10_spec__12_spec__15___redArg___closed__12: *mut LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Meta_Grind_casesMatch_spec__0_spec__0_spec__2_spec__7_spec__10_spec__12_spec__15___redArg___closed__12_value) as *mut LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Meta_Grind_casesMatch_spec__0_spec__0_spec__2_spec__7_spec__10_spec__12_spec__15___redArg___closed__13_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Meta_Grind_casesMatch_spec__0_spec__0_spec__2_spec__7_spec__10_spec__12_spec__15___redArg___closed__13: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Meta_Grind_casesMatch_spec__0_spec__0_spec__2_spec__7_spec__10_spec__12_spec__15___redArg___closed__14_value: LeanStringObject<3> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [96, 46, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Meta_Grind_casesMatch_spec__0_spec__0_spec__2_spec__7_spec__10_spec__12_spec__15___redArg___closed__14: *mut LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Meta_Grind_casesMatch_spec__0_spec__0_spec__2_spec__7_spec__10_spec__12_spec__15___redArg___closed__14_value) as *mut LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Meta_Grind_casesMatch_spec__0_spec__0_spec__2_spec__7_spec__10_spec__12_spec__15___redArg___closed__15_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Meta_Grind_casesMatch_spec__0_spec__0_spec__2_spec__7_spec__10_spec__12_spec__15___redArg___closed__15: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Meta_Grind_casesMatch_spec__0_spec__0_spec__2_spec__7_spec__10_spec__12_spec__15___redArg___closed__16_value: LeanStringObject<10> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [96, 32, 40, 102, 114, 111, 109, 32, 96, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Meta_Grind_casesMatch_spec__0_spec__0_spec__2_spec__7_spec__10_spec__12_spec__15___redArg___closed__16: *mut LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Meta_Grind_casesMatch_spec__0_spec__0_spec__2_spec__7_spec__10_spec__12_spec__15___redArg___closed__16_value) as *mut LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Meta_Grind_casesMatch_spec__0_spec__0_spec__2_spec__7_spec__10_spec__12_spec__15___redArg___closed__17_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Meta_Grind_casesMatch_spec__0_spec__0_spec__2_spec__7_spec__10_spec__12_spec__15___redArg___closed__17: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Meta_Grind_casesMatch_spec__0_spec__0_spec__2_spec__7_spec__10_spec__12_spec__15___redArg___closed__18_value: LeanStringObject<54> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 54, m_capacity: 54, m_length: 53, m_data: [96, 41, 32, 101, 120, 105, 115, 116, 115, 32, 98, 117, 116, 32, 119, 111, 117, 108, 100, 32, 110, 101, 101, 100, 32, 116, 111, 32, 98, 101, 32, 112, 117, 98, 108, 105, 99, 32, 116, 111, 32, 97, 99, 99, 101, 115, 115, 32, 104, 101, 114, 101, 46, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Meta_Grind_casesMatch_spec__0_spec__0_spec__2_spec__7_spec__10_spec__12_spec__15___redArg___closed__18: *mut LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Meta_Grind_casesMatch_spec__0_spec__0_spec__2_spec__7_spec__10_spec__12_spec__15___redArg___closed__18_value) as *mut LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Meta_Grind_casesMatch_spec__0_spec__0_spec__2_spec__7_spec__10_spec__12_spec__15___redArg___closed__19_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Meta_Grind_casesMatch_spec__0_spec__0_spec__2_spec__7_spec__10_spec__12_spec__15___redArg___closed__19: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Meta_Grind_casesMatch_spec__0_spec__0_spec__2_spec__7___redArg___closed__0_value: LeanStringObject<19> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 19, m_capacity: 19, m_length: 18, m_data: [85, 110, 107, 110, 111, 119, 110, 32, 99, 111, 110, 115, 116, 97, 110, 116, 32, 96, 0]};
static mut l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Meta_Grind_casesMatch_spec__0_spec__0_spec__2_spec__7___redArg___closed__0: *mut LeanObject = core::ptr::addr_of!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Meta_Grind_casesMatch_spec__0_spec__0_spec__2_spec__7___redArg___closed__0_value) as *mut LeanObject;
static mut l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Meta_Grind_casesMatch_spec__0_spec__0_spec__2_spec__7___redArg___closed__1_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Meta_Grind_casesMatch_spec__0_spec__0_spec__2_spec__7___redArg___closed__1: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Meta_Grind_casesMatch_spec__0_spec__0_spec__2_spec__7___redArg___closed__2_value: LeanStringObject<2> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [96, 0]};
static mut l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Meta_Grind_casesMatch_spec__0_spec__0_spec__2_spec__7___redArg___closed__2: *mut LeanObject = core::ptr::addr_of!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Meta_Grind_casesMatch_spec__0_spec__0_spec__2_spec__7___redArg___closed__2_value) as *mut LeanObject;
static mut l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Meta_Grind_casesMatch_spec__0_spec__0_spec__2_spec__7___redArg___closed__3_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Meta_Grind_casesMatch_spec__0_spec__0_spec__2_spec__7___redArg___closed__3: *mut LeanObject = core::ptr::null_mut();
static mut l_panic___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Meta_Grind_casesMatch_spec__0_spec__1___closed__0_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_panic___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Meta_Grind_casesMatch_spec__0_spec__1___closed__0: *mut LeanObject = core::ptr::null_mut();
pub static l_panic___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Meta_Grind_casesMatch_spec__0_spec__1___closed__1_value: LeanClosureObject<0> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Core_instMonadCoreM___lam__0___boxed as *const core::ffi::c_void, m_arity: 5, m_num_fixed: 0, m_objs: [] };
static mut l_panic___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Meta_Grind_casesMatch_spec__0_spec__1___closed__1: *mut LeanObject = core::ptr::addr_of!(l_panic___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Meta_Grind_casesMatch_spec__0_spec__1___closed__1_value) as *mut LeanObject;
pub static l_panic___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Meta_Grind_casesMatch_spec__0_spec__1___closed__2_value: LeanClosureObject<0> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Core_instMonadCoreM___lam__1___boxed as *const core::ffi::c_void, m_arity: 7, m_num_fixed: 0, m_objs: [] };
static mut l_panic___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Meta_Grind_casesMatch_spec__0_spec__1___closed__2: *mut LeanObject = core::ptr::addr_of!(l_panic___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Meta_Grind_casesMatch_spec__0_spec__1___closed__2_value) as *mut LeanObject;
pub static l_panic___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Meta_Grind_casesMatch_spec__0_spec__1___closed__3_value: LeanClosureObject<0> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Meta_instMonadMetaM___lam__0___boxed as *const core::ffi::c_void, m_arity: 7, m_num_fixed: 0, m_objs: [] };
static mut l_panic___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Meta_Grind_casesMatch_spec__0_spec__1___closed__3: *mut LeanObject = core::ptr::addr_of!(l_panic___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Meta_Grind_casesMatch_spec__0_spec__1___closed__3_value) as *mut LeanObject;
pub static l_panic___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Meta_Grind_casesMatch_spec__0_spec__1___closed__4_value: LeanClosureObject<0> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Meta_instMonadMetaM___lam__1___boxed as *const core::ffi::c_void, m_arity: 9, m_num_fixed: 0, m_objs: [] };
static mut l_panic___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Meta_Grind_casesMatch_spec__0_spec__1___closed__4: *mut LeanObject = core::ptr::addr_of!(l_panic___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Meta_Grind_casesMatch_spec__0_spec__1___closed__4_value) as *mut LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Meta_Grind_casesMatch_spec__0_spec__3___closed__0_value: LeanStringObject<33> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 33, m_capacity: 33, m_length: 32, m_data: [76, 101, 97, 110, 46, 77, 101, 116, 97, 46, 77, 97, 116, 99, 104, 46, 77, 97, 116, 99, 104, 101, 114, 65, 112, 112, 46, 66, 97, 115, 105, 99, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Meta_Grind_casesMatch_spec__0_spec__3___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Meta_Grind_casesMatch_spec__0_spec__3___closed__0_value) as *mut LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Meta_Grind_casesMatch_spec__0_spec__3___closed__1_value: LeanStringObject<27> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 27, m_capacity: 27, m_length: 26, m_data: [76, 101, 97, 110, 46, 77, 101, 116, 97, 46, 109, 97, 116, 99, 104, 77, 97, 116, 99, 104, 101, 114, 65, 112, 112, 63, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Meta_Grind_casesMatch_spec__0_spec__3___closed__1: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Meta_Grind_casesMatch_spec__0_spec__3___closed__1_value) as *mut LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Meta_Grind_casesMatch_spec__0_spec__3___closed__2_value: LeanStringObject<21> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 21, m_capacity: 21, m_length: 20, m_data: [101, 120, 112, 101, 99, 116, 101, 100, 32, 99, 111, 110, 115, 116, 114, 117, 99, 116, 111, 114, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Meta_Grind_casesMatch_spec__0_spec__3___closed__2: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Meta_Grind_casesMatch_spec__0_spec__3___closed__2_value) as *mut LeanObject;
static mut l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Meta_Grind_casesMatch_spec__0_spec__3___closed__3_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Meta_Grind_casesMatch_spec__0_spec__3___closed__3: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Meta_matchMatcherApp_x3f___at___00Lean_Meta_Grind_casesMatch_spec__0___closed__0_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Meta_matchMatcherApp_x3f___at___00Lean_Meta_Grind_casesMatch_spec__0___closed__0: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Meta_matchMatcherApp_x3f___at___00Lean_Meta_Grind_casesMatch_spec__0___closed__1_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Meta_matchMatcherApp_x3f___at___00Lean_Meta_Grind_casesMatch_spec__0___closed__1: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Meta_matchMatcherApp_x3f___at___00Lean_Meta_Grind_casesMatch_spec__0___closed__2_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Meta_matchMatcherApp_x3f___at___00Lean_Meta_Grind_casesMatch_spec__0___closed__2: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Meta_matchMatcherApp_x3f___at___00Lean_Meta_Grind_casesMatch_spec__0___closed__3_value: LeanCtorObject<1> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*1 + 0) as u16, other: 1, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject] };
static mut l_Lean_Meta_matchMatcherApp_x3f___at___00Lean_Meta_Grind_casesMatch_spec__0___closed__3: *mut LeanObject = core::ptr::addr_of!(l_Lean_Meta_matchMatcherApp_x3f___at___00Lean_Meta_Grind_casesMatch_spec__0___closed__3_value) as *mut LeanObject;
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_casesMatch_spec__1_spec__5_spec__8___redArg___closed__0_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_casesMatch_spec__1_spec__5_spec__8___redArg___closed__0: usize = 0;
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_casesMatch_spec__1_spec__5_spec__8___redArg___closed__1_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_casesMatch_spec__1_spec__5_spec__8___redArg___closed__1: usize = 0;
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_casesMatch_spec__1_spec__5_spec__8___redArg___closed__2_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_casesMatch_spec__1_spec__5_spec__8___redArg___closed__2: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Meta_Grind_casesMatch___lam__0___closed__0_value: LeanStringObject<6> =
    LeanStringObject {
        m_header: LeanObject {
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
static mut l_Lean_Meta_Grind_casesMatch___lam__0___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_casesMatch___lam__0___closed__0_value) as *mut LeanObject;
pub static l_Lean_Meta_Grind_casesMatch___lam__0___closed__1_value: LeanStringObject<11> =
    LeanStringObject {
        m_header: LeanObject {
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
static mut l_Lean_Meta_Grind_casesMatch___lam__0___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_casesMatch___lam__0___closed__1_value) as *mut LeanObject;
static l_Lean_Meta_Grind_casesMatch___lam__0___closed__2_value_aux_0: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_Grind_casesMatch___lam__0___closed__0_value)
                as *mut LeanObject,
            15947788021050471391 as *mut LeanObject,
        ],
    };
pub static l_Lean_Meta_Grind_casesMatch___lam__0___closed__2_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_Grind_casesMatch___lam__0___closed__2_value_aux_0)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Grind_casesMatch___lam__0___closed__1_value)
                as *mut LeanObject,
            10880498660615990170 as *mut LeanObject,
        ],
    };
static mut l_Lean_Meta_Grind_casesMatch___lam__0___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_casesMatch___lam__0___closed__2_value) as *mut LeanObject;
pub static l_Lean_Meta_Grind_casesMatch___lam__0___closed__3_value: LeanStringObject<28> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 28,
        m_capacity: 28,
        m_length: 27,
        m_data: [
            96, 109, 97, 116, 99, 104, 96, 45, 101, 120, 112, 114, 101, 115, 115, 105, 111, 110,
            32, 101, 120, 112, 101, 99, 116, 101, 100, 0,
        ],
    };
static mut l_Lean_Meta_Grind_casesMatch___lam__0___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_casesMatch___lam__0___closed__3_value) as *mut LeanObject;
static mut l_Lean_Meta_Grind_casesMatch___lam__0___closed__4_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Grind_casesMatch___lam__0___closed__4: *mut LeanObject =
    core::ptr::null_mut();
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_CasesMatch_0__Lean_Meta_Grind_isMatchCondCandidate_go(
    mut v_e_1691_: *mut LeanObject,
) -> u8 {
    let mut v_binderType_1692_: *mut LeanObject = core::ptr::null_mut();
    let mut v_body_1693_: *mut LeanObject = core::ptr::null_mut();
    let mut v_lhs_1695_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1696_: u8 = 0;
    let mut v___x_1698_: u8 = 0;
    let mut v___x_1700_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1701_: u8 = 0;
    let mut v___x_1703_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1704_: u8 = 0;
    let mut v___x_1705_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1706_: u8 = 0;
    let mut v_arg_1707_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1708_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1709_: u8 = 0;
    let mut v_arg_1710_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1711_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1712_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1713_: u8 = 0;
    let mut v___x_1714_: u8 = 0;
    let mut v___x_1715_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1716_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1717_: u8 = 0;
    let mut v___x_1718_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_e_1691_) == 7 {
                    v_binderType_1692_ = lean_ctor_get(v_e_1691_, 1);
                    lean_inc_ref(v_binderType_1692_);
                    v_body_1693_ = lean_ctor_get(v_e_1691_, 2);
                    lean_inc_ref(v_body_1693_);
                    lean_dec_ref_known(v_e_1691_, 3);
                    v___x_1703_ = l_Lean_Expr_cleanupAnnotations(v_binderType_1692_);
                    v___x_1704_ = l_Lean_Expr_isApp(v___x_1703_);
                    if v___x_1704_ == 0 {
                        lean_dec_ref(v___x_1703_);
                        state = 2;
                        continue;
                    } else {
                        v___x_1705_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1703_);
                        v___x_1706_ = l_Lean_Expr_isApp(v___x_1705_);
                        if v___x_1706_ == 0 {
                            lean_dec_ref(v___x_1705_);
                            state = 2;
                            continue;
                        } else {
                            v_arg_1707_ = lean_ctor_get(v___x_1705_, 1);
                            lean_inc_ref(v_arg_1707_);
                            v___x_1708_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1705_);
                            v___x_1709_ = l_Lean_Expr_isApp(v___x_1708_);
                            if v___x_1709_ == 0 {
                                lean_dec_ref(v___x_1708_);
                                lean_dec_ref(v_arg_1707_);
                                state = 2;
                                continue;
                            } else {
                                v_arg_1710_ = lean_ctor_get(v___x_1708_, 1);
                                lean_inc_ref(v_arg_1710_);
                                v___x_1711_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1708_);
                                v___x_1712_ = l___private_Lean_Meta_Tactic_Grind_CasesMatch_0__Lean_Meta_Grind_isMatchCondCandidate_go___closed__1;
                                v___x_1713_ = l_Lean_Expr_isConstOf(v___x_1711_, v___x_1712_);
                                if v___x_1713_ == 0 {
                                    lean_dec_ref(v_arg_1707_);
                                    v___x_1714_ = l_Lean_Expr_isApp(v___x_1711_);
                                    if v___x_1714_ == 0 {
                                        lean_dec_ref(v___x_1711_);
                                        lean_dec_ref(v_arg_1710_);
                                        state = 2;
                                        continue;
                                    } else {
                                        v___x_1715_ =
                                            l_Lean_Expr_appFnCleanup___redArg(v___x_1711_);
                                        v___x_1716_ = l___private_Lean_Meta_Tactic_Grind_CasesMatch_0__Lean_Meta_Grind_isMatchCondCandidate_go___closed__3;
                                        v___x_1717_ =
                                            l_Lean_Expr_isConstOf(v___x_1715_, v___x_1716_);
                                        lean_dec_ref(v___x_1715_);
                                        if v___x_1717_ == 0 {
                                            lean_dec_ref(v_arg_1710_);
                                            state = 2;
                                            continue;
                                        } else {
                                            v_lhs_1695_ = v_arg_1710_;
                                            state = 1;
                                            continue;
                                        }
                                    }
                                } else {
                                    lean_dec_ref(v___x_1711_);
                                    lean_dec_ref(v_arg_1710_);
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
                lean_dec_ref(v_lhs_1695_);
                if v___x_1696_ == 0 {
                    v_e_1691_ = v_body_1693_;
                    state = 0;
                    continue;
                } else {
                    lean_dec_ref(v_body_1693_);
                    v___x_1698_ = 0;
                    return v___x_1698_;
                }
            }
            2 => {
                v___x_1700_ = lean_unsigned_to_nat(0);
                v___x_1701_ = lean_expr_has_loose_bvar(v_body_1693_, v___x_1700_);
                if v___x_1701_ == 0 {
                    lean_dec_ref(v_body_1693_);
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
    mut v_e_1719_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1720_: u8 = 0;
    let mut v_r_1721_: *mut LeanObject = core::ptr::null_mut();
    v_res_1720_ =
        l___private_Lean_Meta_Tactic_Grind_CasesMatch_0__Lean_Meta_Grind_isMatchCondCandidate_go(
            v_e_1719_,
        );
    v_r_1721_ = lean_box((v_res_1720_) as usize);
    return v_r_1721_;
}
pub unsafe fn l_Lean_Meta_Grind_isMatchCondCandidate(mut v_e_1722_: *mut LeanObject) -> u8 {
    let mut v___x_1723_: u8 = 0;
    v___x_1723_ = l_Lean_Expr_isForall(v_e_1722_);
    if v___x_1723_ == 0 {
        lean_dec_ref(v_e_1722_);
        return v___x_1723_;
    } else {
        let mut v___x_1724_: u8 = 0;
        v___x_1724_ = l___private_Lean_Meta_Tactic_Grind_CasesMatch_0__Lean_Meta_Grind_isMatchCondCandidate_go(v_e_1722_);
        return v___x_1724_;
    }
}
pub unsafe fn l_Lean_Meta_Grind_isMatchCondCandidate___boxed(
    mut v_e_1725_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1726_: u8 = 0;
    let mut v_r_1727_: *mut LeanObject = core::ptr::null_mut();
    v_res_1726_ = l_Lean_Meta_Grind_isMatchCondCandidate(v_e_1725_);
    v_r_1727_ = lean_box((v_res_1726_) as usize);
    return v_r_1727_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_CasesMatch_0__Lean_Meta_Grind_addMatchCondsToAlt(
    mut v_alt_1728_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_binderName_1729_: *mut LeanObject = core::ptr::null_mut();
    let mut v_binderType_1730_: *mut LeanObject = core::ptr::null_mut();
    let mut v_body_1731_: *mut LeanObject = core::ptr::null_mut();
    let mut v_binderInfo_1732_: u8 = 0;
    let mut v___y_1734_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1735_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1736_: u8 = 0;
    let mut v___x_1737_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1738_: u8 = 0;
    let mut v___x_1739_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1741_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1742_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1743_: usize = 0;
    let mut v___x_1744_: usize = 0;
    let mut v___x_1745_: u8 = 0;
    let mut v___x_1746_: usize = 0;
    let mut v___x_1747_: usize = 0;
    let mut v___x_1748_: u8 = 0;
    let mut v___x_1749_: u8 = 0;
    let mut v___x_1750_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_alt_1728_) == 7 {
                    v_binderName_1729_ = lean_ctor_get(v_alt_1728_, 0);
                    v_binderType_1730_ = lean_ctor_get(v_alt_1728_, 1);
                    v_body_1731_ = lean_ctor_get(v_alt_1728_, 2);
                    v_binderInfo_1732_ = lean_ctor_get_uint8(
                        v_alt_1728_,
                        (core::mem::size_of::<*mut LeanObject>() * 3 + 8) as u32,
                    );
                    lean_inc_ref(v_binderType_1730_);
                    v___x_1749_ = l_Lean_Meta_Grind_isMatchCondCandidate(v_binderType_1730_);
                    if v___x_1749_ == 0 {
                        lean_inc_ref(v_binderType_1730_);
                        v___y_1741_ = v_binderType_1730_;
                        state = 2;
                        continue;
                    } else {
                        lean_inc_ref(v_binderType_1730_);
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
                    lean_inc(v_binderName_1729_);
                    lean_dec_ref_known(v_alt_1728_, 3);
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
                        lean_inc(v_binderName_1729_);
                        lean_dec_ref_known(v_alt_1728_, 3);
                        v___x_1739_ = l_Lean_Expr_forallE___override(
                            v_binderName_1729_,
                            v___y_1735_,
                            v___y_1734_,
                            v_binderInfo_1732_,
                        );
                        return v___x_1739_;
                    } else {
                        lean_dec_ref(v___y_1735_);
                        lean_dec_ref(v___y_1734_);
                        return v_alt_1728_;
                    }
                }
            }
            2 => {
                lean_inc_ref(v_body_1731_);
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
    mut v_splitterType_1751_: *mut LeanObject,
    mut v_numAlts_1752_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1753_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1754_: u8 = 0;
    let mut v_binderName_1755_: *mut LeanObject = core::ptr::null_mut();
    let mut v_binderType_1756_: *mut LeanObject = core::ptr::null_mut();
    let mut v_body_1757_: *mut LeanObject = core::ptr::null_mut();
    let mut v_binderInfo_1758_: u8 = 0;
    let mut v___x_1759_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1760_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1761_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1762_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1764_: u8 = 0;
    let mut v___x_1765_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1766_: u8 = 0;
    let mut v___x_1767_: *mut LeanObject = core::ptr::null_mut();
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
                v___x_1753_ = lean_unsigned_to_nat(0);
                v___x_1754_ = lean_nat_dec_eq(v_numAlts_1752_, v___x_1753_);
                if v___x_1754_ == 0 {
                    if lean_obj_tag(v_splitterType_1751_) == 7 {
                        v_binderName_1755_ = lean_ctor_get(v_splitterType_1751_, 0);
                        v_binderType_1756_ = lean_ctor_get(v_splitterType_1751_, 1);
                        v_body_1757_ = lean_ctor_get(v_splitterType_1751_, 2);
                        v_binderInfo_1758_ = lean_ctor_get_uint8(
                            v_splitterType_1751_,
                            (core::mem::size_of::<*mut LeanObject>() * 3 + 8) as u32,
                        );
                        lean_inc_ref(v_binderType_1756_);
                        v___x_1759_ = l___private_Lean_Meta_Tactic_Grind_CasesMatch_0__Lean_Meta_Grind_addMatchCondsToAlt(v_binderType_1756_);
                        v___x_1760_ = lean_unsigned_to_nat(1);
                        v___x_1761_ = lean_nat_sub(v_numAlts_1752_, v___x_1760_);
                        lean_inc_ref(v_body_1757_);
                        v___x_1762_ = l___private_Lean_Meta_Tactic_Grind_CasesMatch_0__Lean_Meta_Grind_addMatchCondsToSplitter(v_body_1757_, v___x_1761_);
                        lean_dec(v___x_1761_);
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
                    lean_inc(v_binderName_1755_);
                    lean_dec_ref_known(v_splitterType_1751_, 3);
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
                        lean_inc(v_binderName_1755_);
                        lean_dec_ref_known(v_splitterType_1751_, 3);
                        v___x_1767_ = l_Lean_Expr_forallE___override(
                            v_binderName_1755_,
                            v___x_1759_,
                            v___x_1762_,
                            v_binderInfo_1758_,
                        );
                        return v___x_1767_;
                    } else {
                        lean_dec_ref(v___x_1762_);
                        lean_dec_ref(v___x_1759_);
                        return v_splitterType_1751_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_CasesMatch_0__Lean_Meta_Grind_addMatchCondsToSplitter___boxed(
    mut v_splitterType_1774_: *mut LeanObject,
    mut v_numAlts_1775_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1776_: *mut LeanObject = core::ptr::null_mut();
    v_res_1776_ =
        l___private_Lean_Meta_Tactic_Grind_CasesMatch_0__Lean_Meta_Grind_addMatchCondsToSplitter(
            v_splitterType_1774_,
            v_numAlts_1775_,
        );
    lean_dec(v_numAlts_1775_);
    return v_res_1776_;
}
pub unsafe fn l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_Tactic_Grind_CasesMatch_0__Lean_Meta_Grind_casesMatch_mkMotiveAndRefls_spec__0___redArg___lam__0(
    mut v_k_1777_: *mut LeanObject,
    mut v_b_1778_: *mut LeanObject,
    mut v_c_1779_: *mut LeanObject,
    mut v___y_1780_: *mut LeanObject,
    mut v___y_1781_: *mut LeanObject,
    mut v___y_1782_: *mut LeanObject,
    mut v___y_1783_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1785_: *mut LeanObject = core::ptr::null_mut();
    lean_inc(v___y_1783_);
    lean_inc_ref(v___y_1782_);
    lean_inc(v___y_1781_);
    lean_inc_ref(v___y_1780_);
    v___x_1785_ = lean_apply_7(
        v_k_1777_,
        v_b_1778_,
        v_c_1779_,
        v___y_1780_,
        v___y_1781_,
        v___y_1782_,
        v___y_1783_,
        lean_box(0),
    );
    return v___x_1785_;
}
pub unsafe fn l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_Tactic_Grind_CasesMatch_0__Lean_Meta_Grind_casesMatch_mkMotiveAndRefls_spec__0___redArg___lam__0___boxed(
    mut v_k_1786_: *mut LeanObject,
    mut v_b_1787_: *mut LeanObject,
    mut v_c_1788_: *mut LeanObject,
    mut v___y_1789_: *mut LeanObject,
    mut v___y_1790_: *mut LeanObject,
    mut v___y_1791_: *mut LeanObject,
    mut v___y_1792_: *mut LeanObject,
    mut v___y_1793_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1794_: *mut LeanObject = core::ptr::null_mut();
    v_res_1794_ = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_Tactic_Grind_CasesMatch_0__Lean_Meta_Grind_casesMatch_mkMotiveAndRefls_spec__0___redArg___lam__0(v_k_1786_, v_b_1787_, v_c_1788_, v___y_1789_, v___y_1790_, v___y_1791_, v___y_1792_);
    lean_dec(v___y_1792_);
    lean_dec_ref(v___y_1791_);
    lean_dec(v___y_1790_);
    lean_dec_ref(v___y_1789_);
    return v_res_1794_;
}
pub unsafe fn l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_Tactic_Grind_CasesMatch_0__Lean_Meta_Grind_casesMatch_mkMotiveAndRefls_spec__0___redArg(
    mut v_type_1795_: *mut LeanObject,
    mut v_maxFVars_x3f_1796_: *mut LeanObject,
    mut v_k_1797_: *mut LeanObject,
    mut v_cleanupAnnotations_1798_: u8,
    mut v_whnfType_1799_: u8,
    mut v___y_1800_: *mut LeanObject,
    mut v___y_1801_: *mut LeanObject,
    mut v___y_1802_: *mut LeanObject,
    mut v___y_1803_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_1805_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1806_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1807_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1809_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1810_: u8 = 0;
    let mut v___x_1812_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1813_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1814_: u8 = 0;
    let mut v_a_1815_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1817_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1818_: u8 = 0;
    let mut v___x_1820_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1821_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1822_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___f_1805_ = lean_alloc_closure(l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_Tactic_Grind_CasesMatch_0__Lean_Meta_Grind_casesMatch_mkMotiveAndRefls_spec__0___redArg___lam__0___boxed as *mut core::ffi::c_void, 8, 1);
                lean_closure_set(v___f_1805_, 0, v_k_1797_);
                v___x_1806_ = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAux(
                    lean_box(0),
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
                if lean_obj_tag(v___x_1806_) == 0 {
                    v_a_1807_ = lean_ctor_get(v___x_1806_, 0);
                    v_isSharedCheck_1814_ = (!lean_is_exclusive(v___x_1806_)) as u8;
                    if v_isSharedCheck_1814_ == 0 {
                        v___x_1809_ = v___x_1806_;
                        v_isShared_1810_ = v_isSharedCheck_1814_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_1807_);
                        lean_dec(v___x_1806_);
                        v___x_1809_ = lean_box(0);
                        v_isShared_1810_ = v_isSharedCheck_1814_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_1815_ = lean_ctor_get(v___x_1806_, 0);
                    v_isSharedCheck_1822_ = (!lean_is_exclusive(v___x_1806_)) as u8;
                    if v_isSharedCheck_1822_ == 0 {
                        v___x_1817_ = v___x_1806_;
                        v_isShared_1818_ = v_isSharedCheck_1822_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_1815_);
                        lean_dec(v___x_1806_);
                        v___x_1817_ = lean_box(0);
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
                    v_reuseFailAlloc_1813_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1813_, 0, v_a_1807_);
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
                    v_reuseFailAlloc_1821_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1821_, 0, v_a_1815_);
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
    mut v_type_1823_: *mut LeanObject,
    mut v_maxFVars_x3f_1824_: *mut LeanObject,
    mut v_k_1825_: *mut LeanObject,
    mut v_cleanupAnnotations_1826_: *mut LeanObject,
    mut v_whnfType_1827_: *mut LeanObject,
    mut v___y_1828_: *mut LeanObject,
    mut v___y_1829_: *mut LeanObject,
    mut v___y_1830_: *mut LeanObject,
    mut v___y_1831_: *mut LeanObject,
    mut v___y_1832_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_cleanupAnnotations_boxed_1833_: u8 = 0;
    let mut v_whnfType_boxed_1834_: u8 = 0;
    let mut v_res_1835_: *mut LeanObject = core::ptr::null_mut();
    v_cleanupAnnotations_boxed_1833_ = (lean_unbox(v_cleanupAnnotations_1826_) as u8);
    v_whnfType_boxed_1834_ = (lean_unbox(v_whnfType_1827_) as u8);
    v_res_1835_ = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_Tactic_Grind_CasesMatch_0__Lean_Meta_Grind_casesMatch_mkMotiveAndRefls_spec__0___redArg(v_type_1823_, v_maxFVars_x3f_1824_, v_k_1825_, v_cleanupAnnotations_boxed_1833_, v_whnfType_boxed_1834_, v___y_1828_, v___y_1829_, v___y_1830_, v___y_1831_);
    lean_dec(v___y_1831_);
    lean_dec_ref(v___y_1830_);
    lean_dec(v___y_1829_);
    lean_dec_ref(v___y_1828_);
    return v_res_1835_;
}
pub unsafe fn l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_Tactic_Grind_CasesMatch_0__Lean_Meta_Grind_casesMatch_mkMotiveAndRefls_spec__0(
    mut v_00_u03b1_1836_: *mut LeanObject,
    mut v_type_1837_: *mut LeanObject,
    mut v_maxFVars_x3f_1838_: *mut LeanObject,
    mut v_k_1839_: *mut LeanObject,
    mut v_cleanupAnnotations_1840_: u8,
    mut v_whnfType_1841_: u8,
    mut v___y_1842_: *mut LeanObject,
    mut v___y_1843_: *mut LeanObject,
    mut v___y_1844_: *mut LeanObject,
    mut v___y_1845_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1847_: *mut LeanObject = core::ptr::null_mut();
    v___x_1847_ = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_Tactic_Grind_CasesMatch_0__Lean_Meta_Grind_casesMatch_mkMotiveAndRefls_spec__0___redArg(v_type_1837_, v_maxFVars_x3f_1838_, v_k_1839_, v_cleanupAnnotations_1840_, v_whnfType_1841_, v___y_1842_, v___y_1843_, v___y_1844_, v___y_1845_);
    return v___x_1847_;
}
pub unsafe fn l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_Tactic_Grind_CasesMatch_0__Lean_Meta_Grind_casesMatch_mkMotiveAndRefls_spec__0___boxed(
    mut v_00_u03b1_1848_: *mut LeanObject,
    mut v_type_1849_: *mut LeanObject,
    mut v_maxFVars_x3f_1850_: *mut LeanObject,
    mut v_k_1851_: *mut LeanObject,
    mut v_cleanupAnnotations_1852_: *mut LeanObject,
    mut v_whnfType_1853_: *mut LeanObject,
    mut v___y_1854_: *mut LeanObject,
    mut v___y_1855_: *mut LeanObject,
    mut v___y_1856_: *mut LeanObject,
    mut v___y_1857_: *mut LeanObject,
    mut v___y_1858_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_cleanupAnnotations_boxed_1859_: u8 = 0;
    let mut v_whnfType_boxed_1860_: u8 = 0;
    let mut v_res_1861_: *mut LeanObject = core::ptr::null_mut();
    v_cleanupAnnotations_boxed_1859_ = (lean_unbox(v_cleanupAnnotations_1852_) as u8);
    v_whnfType_boxed_1860_ = (lean_unbox(v_whnfType_1853_) as u8);
    v_res_1861_ = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_Tactic_Grind_CasesMatch_0__Lean_Meta_Grind_casesMatch_mkMotiveAndRefls_spec__0(v_00_u03b1_1848_, v_type_1849_, v_maxFVars_x3f_1850_, v_k_1851_, v_cleanupAnnotations_boxed_1859_, v_whnfType_boxed_1860_, v___y_1854_, v___y_1855_, v___y_1856_, v___y_1857_);
    lean_dec(v___y_1857_);
    lean_dec_ref(v___y_1856_);
    lean_dec(v___y_1855_);
    lean_dec_ref(v___y_1854_);
    return v_res_1861_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_CasesMatch_0__Lean_Meta_Grind_casesMatch_mkMotiveAndRefls___lam__0(
    mut v_mvarId_1862_: *mut LeanObject,
    mut v_xs_1863_: *mut LeanObject,
    mut v_eqs_1864_: *mut LeanObject,
    mut v_eqRefls_1865_: *mut LeanObject,
    mut v___y_1866_: *mut LeanObject,
    mut v___y_1867_: *mut LeanObject,
    mut v___y_1868_: *mut LeanObject,
    mut v___y_1869_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1871_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1872_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1873_: u8 = 0;
    let mut v___x_1874_: u8 = 0;
    let mut v___x_1875_: u8 = 0;
    let mut v___x_1876_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1877_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1878_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1879_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1881_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1882_: u8 = 0;
    let mut v___x_1883_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1885_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1886_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1887_: u8 = 0;
    let mut v_a_1888_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1890_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1891_: u8 = 0;
    let mut v___x_1893_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1894_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1895_: u8 = 0;
    let mut v_a_1896_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1898_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1899_: u8 = 0;
    let mut v___x_1901_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1902_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1903_: u8 = 0;
    let mut v_a_1904_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1906_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1907_: u8 = 0;
    let mut v___x_1909_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1910_: *mut LeanObject = core::ptr::null_mut();
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
                if lean_obj_tag(v___x_1871_) == 0 {
                    v_a_1872_ = lean_ctor_get(v___x_1871_, 0);
                    lean_inc(v_a_1872_);
                    lean_dec_ref_known(v___x_1871_, 1);
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
                    if lean_obj_tag(v___x_1876_) == 0 {
                        v_a_1877_ = lean_ctor_get(v___x_1876_, 0);
                        lean_inc(v_a_1877_);
                        lean_dec_ref_known(v___x_1876_, 1);
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
                        if lean_obj_tag(v___x_1878_) == 0 {
                            v_a_1879_ = lean_ctor_get(v___x_1878_, 0);
                            v_isSharedCheck_1887_ = (!lean_is_exclusive(v___x_1878_)) as u8;
                            if v_isSharedCheck_1887_ == 0 {
                                v___x_1881_ = v___x_1878_;
                                v_isShared_1882_ = v_isSharedCheck_1887_;
                                state = 1;
                                continue;
                            } else {
                                lean_inc(v_a_1879_);
                                lean_dec(v___x_1878_);
                                v___x_1881_ = lean_box(0);
                                v_isShared_1882_ = v_isSharedCheck_1887_;
                                state = 1;
                                continue;
                            }
                        } else {
                            lean_dec_ref(v_eqRefls_1865_);
                            v_a_1888_ = lean_ctor_get(v___x_1878_, 0);
                            v_isSharedCheck_1895_ = (!lean_is_exclusive(v___x_1878_)) as u8;
                            if v_isSharedCheck_1895_ == 0 {
                                v___x_1890_ = v___x_1878_;
                                v_isShared_1891_ = v_isSharedCheck_1895_;
                                state = 3;
                                continue;
                            } else {
                                lean_inc(v_a_1888_);
                                lean_dec(v___x_1878_);
                                v___x_1890_ = lean_box(0);
                                v_isShared_1891_ = v_isSharedCheck_1895_;
                                state = 3;
                                continue;
                            }
                        }
                    } else {
                        lean_dec_ref(v_eqRefls_1865_);
                        v_a_1896_ = lean_ctor_get(v___x_1876_, 0);
                        v_isSharedCheck_1903_ = (!lean_is_exclusive(v___x_1876_)) as u8;
                        if v_isSharedCheck_1903_ == 0 {
                            v___x_1898_ = v___x_1876_;
                            v_isShared_1899_ = v_isSharedCheck_1903_;
                            state = 5;
                            continue;
                        } else {
                            lean_inc(v_a_1896_);
                            lean_dec(v___x_1876_);
                            v___x_1898_ = lean_box(0);
                            v_isShared_1899_ = v_isSharedCheck_1903_;
                            state = 5;
                            continue;
                        }
                    }
                } else {
                    lean_dec_ref(v_eqRefls_1865_);
                    v_a_1904_ = lean_ctor_get(v___x_1871_, 0);
                    v_isSharedCheck_1911_ = (!lean_is_exclusive(v___x_1871_)) as u8;
                    if v_isSharedCheck_1911_ == 0 {
                        v___x_1906_ = v___x_1871_;
                        v_isShared_1907_ = v_isSharedCheck_1911_;
                        state = 7;
                        continue;
                    } else {
                        lean_inc(v_a_1904_);
                        lean_dec(v___x_1871_);
                        v___x_1906_ = lean_box(0);
                        v_isShared_1907_ = v_isSharedCheck_1911_;
                        state = 7;
                        continue;
                    }
                }
            }
            1 => {
                v___x_1883_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_1883_, 0, v_a_1879_);
                lean_ctor_set(v___x_1883_, 1, v_eqRefls_1865_);
                if v_isShared_1882_ == 0 {
                    lean_ctor_set(v___x_1881_, 0, v___x_1883_);
                    v___x_1885_ = v___x_1881_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1886_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1886_, 0, v___x_1883_);
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
                    v_reuseFailAlloc_1894_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1894_, 0, v_a_1888_);
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
                    v_reuseFailAlloc_1902_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1902_, 0, v_a_1896_);
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
                    v_reuseFailAlloc_1910_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1910_, 0, v_a_1904_);
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
    mut v_mvarId_1912_: *mut LeanObject,
    mut v_xs_1913_: *mut LeanObject,
    mut v_eqs_1914_: *mut LeanObject,
    mut v_eqRefls_1915_: *mut LeanObject,
    mut v___y_1916_: *mut LeanObject,
    mut v___y_1917_: *mut LeanObject,
    mut v___y_1918_: *mut LeanObject,
    mut v___y_1919_: *mut LeanObject,
    mut v___y_1920_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1921_: *mut LeanObject = core::ptr::null_mut();
    v_res_1921_ = l___private_Lean_Meta_Tactic_Grind_CasesMatch_0__Lean_Meta_Grind_casesMatch_mkMotiveAndRefls___lam__0(v_mvarId_1912_, v_xs_1913_, v_eqs_1914_, v_eqRefls_1915_, v___y_1916_, v___y_1917_, v___y_1918_, v___y_1919_);
    lean_dec(v___y_1919_);
    lean_dec_ref(v___y_1918_);
    lean_dec(v___y_1917_);
    lean_dec_ref(v___y_1916_);
    lean_dec_ref(v_eqs_1914_);
    lean_dec_ref(v_xs_1913_);
    return v_res_1921_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_CasesMatch_0__Lean_Meta_Grind_casesMatch_mkMotiveAndRefls___lam__1(
    mut v_mvarId_1922_: *mut LeanObject,
    mut v_discrs_1923_: *mut LeanObject,
    mut v_xs_1924_: *mut LeanObject,
    mut v_x_1925_: *mut LeanObject,
    mut v___y_1926_: *mut LeanObject,
    mut v___y_1927_: *mut LeanObject,
    mut v___y_1928_: *mut LeanObject,
    mut v___y_1929_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_1931_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1932_: *mut LeanObject = core::ptr::null_mut();
    lean_inc_ref(v_xs_1924_);
    v___f_1931_ = lean_alloc_closure(l___private_Lean_Meta_Tactic_Grind_CasesMatch_0__Lean_Meta_Grind_casesMatch_mkMotiveAndRefls___lam__0___boxed as *mut core::ffi::c_void, 9, 2);
    lean_closure_set(v___f_1931_, 0, v_mvarId_1922_);
    lean_closure_set(v___f_1931_, 1, v_xs_1924_);
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
    mut v_mvarId_1933_: *mut LeanObject,
    mut v_discrs_1934_: *mut LeanObject,
    mut v_xs_1935_: *mut LeanObject,
    mut v_x_1936_: *mut LeanObject,
    mut v___y_1937_: *mut LeanObject,
    mut v___y_1938_: *mut LeanObject,
    mut v___y_1939_: *mut LeanObject,
    mut v___y_1940_: *mut LeanObject,
    mut v___y_1941_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1942_: *mut LeanObject = core::ptr::null_mut();
    v_res_1942_ = l___private_Lean_Meta_Tactic_Grind_CasesMatch_0__Lean_Meta_Grind_casesMatch_mkMotiveAndRefls___lam__1(v_mvarId_1933_, v_discrs_1934_, v_xs_1935_, v_x_1936_, v___y_1937_, v___y_1938_, v___y_1939_, v___y_1940_);
    lean_dec(v___y_1940_);
    lean_dec_ref(v___y_1939_);
    lean_dec(v___y_1938_);
    lean_dec_ref(v___y_1937_);
    lean_dec_ref(v_x_1936_);
    return v_res_1942_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_CasesMatch_0__Lean_Meta_Grind_casesMatch_mkMotiveAndRefls___closed__0()
-> *mut LeanObject {
    let mut v___x_1943_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1944_: *mut LeanObject = core::ptr::null_mut();
    v___x_1943_ = lean_unsigned_to_nat(0);
    v___x_1944_ = l_Lean_Level_ofNat(v___x_1943_);
    return v___x_1944_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_CasesMatch_0__Lean_Meta_Grind_casesMatch_mkMotiveAndRefls___closed__1()
-> *mut LeanObject {
    let mut v___x_1945_: *mut LeanObject = core::ptr::null_mut();
    let mut v_dummy_1946_: *mut LeanObject = core::ptr::null_mut();
    v___x_1945_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_CasesMatch_0__Lean_Meta_Grind_casesMatch_mkMotiveAndRefls___closed__0), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_CasesMatch_0__Lean_Meta_Grind_casesMatch_mkMotiveAndRefls___closed__0_once), _init_l___private_Lean_Meta_Tactic_Grind_CasesMatch_0__Lean_Meta_Grind_casesMatch_mkMotiveAndRefls___closed__0);
    v_dummy_1946_ = l_Lean_mkSort(v___x_1945_);
    return v_dummy_1946_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_CasesMatch_0__Lean_Meta_Grind_casesMatch_mkMotiveAndRefls(
    mut v_mvarId_1947_: *mut LeanObject,
    mut v_e_1948_: *mut LeanObject,
    mut v_app_1949_: *mut LeanObject,
    mut v_a_1950_: *mut LeanObject,
    mut v_a_1951_: *mut LeanObject,
    mut v_a_1952_: *mut LeanObject,
    mut v_a_1953_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_params_1955_: *mut LeanObject = core::ptr::null_mut();
    let mut v_discrs_1956_: *mut LeanObject = core::ptr::null_mut();
    let mut v_dummy_1957_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1958_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1959_: *mut LeanObject = core::ptr::null_mut();
    let mut v_aux_1960_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1961_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1962_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1963_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1964_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1965_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1966_: u8 = 0;
    let mut v___x_1967_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1968_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1970_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1971_: u8 = 0;
    let mut v___x_1973_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1974_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1975_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_params_1955_ = lean_ctor_get(v_app_1949_, 3);
                lean_inc_ref(v_params_1955_);
                v_discrs_1956_ = lean_ctor_get(v_app_1949_, 5);
                lean_inc_ref(v_discrs_1956_);
                lean_dec_ref(v_app_1949_);
                v_dummy_1957_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_CasesMatch_0__Lean_Meta_Grind_casesMatch_mkMotiveAndRefls___closed__1), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_CasesMatch_0__Lean_Meta_Grind_casesMatch_mkMotiveAndRefls___closed__1_once), _init_l___private_Lean_Meta_Tactic_Grind_CasesMatch_0__Lean_Meta_Grind_casesMatch_mkMotiveAndRefls___closed__1);
                v___x_1958_ = l_Lean_Expr_getAppFn(v_e_1948_);
                v___x_1959_ = l_Lean_mkAppN(v___x_1958_, v_params_1955_);
                lean_dec_ref(v_params_1955_);
                v_aux_1960_ = l_Lean_Expr_app___override(v___x_1959_, v_dummy_1957_);
                lean_inc(v_a_1953_);
                lean_inc_ref(v_a_1952_);
                lean_inc(v_a_1951_);
                lean_inc_ref(v_a_1950_);
                v___x_1961_ =
                    lean_infer_type(v_aux_1960_, v_a_1950_, v_a_1951_, v_a_1952_, v_a_1953_);
                if lean_obj_tag(v___x_1961_) == 0 {
                    v_a_1962_ = lean_ctor_get(v___x_1961_, 0);
                    lean_inc(v_a_1962_);
                    lean_dec_ref_known(v___x_1961_, 1);
                    lean_inc_ref(v_discrs_1956_);
                    v___f_1963_ = lean_alloc_closure(l___private_Lean_Meta_Tactic_Grind_CasesMatch_0__Lean_Meta_Grind_casesMatch_mkMotiveAndRefls___lam__1___boxed as *mut core::ffi::c_void, 9, 2);
                    lean_closure_set(v___f_1963_, 0, v_mvarId_1947_);
                    lean_closure_set(v___f_1963_, 1, v_discrs_1956_);
                    v___x_1964_ = lean_array_get_size(v_discrs_1956_);
                    lean_dec_ref(v_discrs_1956_);
                    v___x_1965_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v___x_1965_, 0, v___x_1964_);
                    v___x_1966_ = 0;
                    v___x_1967_ = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Meta_Tactic_Grind_CasesMatch_0__Lean_Meta_Grind_casesMatch_mkMotiveAndRefls_spec__0___redArg(v_a_1962_, v___x_1965_, v___f_1963_, v___x_1966_, v___x_1966_, v_a_1950_, v_a_1951_, v_a_1952_, v_a_1953_);
                    return v___x_1967_;
                } else {
                    lean_dec_ref(v_discrs_1956_);
                    lean_dec(v_mvarId_1947_);
                    v_a_1968_ = lean_ctor_get(v___x_1961_, 0);
                    v_isSharedCheck_1975_ = (!lean_is_exclusive(v___x_1961_)) as u8;
                    if v_isSharedCheck_1975_ == 0 {
                        v___x_1970_ = v___x_1961_;
                        v_isShared_1971_ = v_isSharedCheck_1975_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_1968_);
                        lean_dec(v___x_1961_);
                        v___x_1970_ = lean_box(0);
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
                    v_reuseFailAlloc_1974_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1974_, 0, v_a_1968_);
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
    mut v_mvarId_1976_: *mut LeanObject,
    mut v_e_1977_: *mut LeanObject,
    mut v_app_1978_: *mut LeanObject,
    mut v_a_1979_: *mut LeanObject,
    mut v_a_1980_: *mut LeanObject,
    mut v_a_1981_: *mut LeanObject,
    mut v_a_1982_: *mut LeanObject,
    mut v_a_1983_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1984_: *mut LeanObject = core::ptr::null_mut();
    v_res_1984_ = l___private_Lean_Meta_Tactic_Grind_CasesMatch_0__Lean_Meta_Grind_casesMatch_mkMotiveAndRefls(v_mvarId_1976_, v_e_1977_, v_app_1978_, v_a_1979_, v_a_1980_, v_a_1981_, v_a_1982_);
    lean_dec(v_a_1982_);
    lean_dec_ref(v_a_1981_);
    lean_dec(v_a_1980_);
    lean_dec_ref(v_a_1979_);
    lean_dec_ref(v_e_1977_);
    return v_res_1984_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_CasesMatch_0__Lean_Meta_Grind_casesMatch_updateTags_spec__0___redArg(
    mut v_a_1985_: *mut LeanObject,
    mut v_as_1986_: *mut LeanObject,
    mut v_sz_1987_: usize,
    mut v_i_1988_: usize,
    mut v_b_1989_: *mut LeanObject,
    mut v___y_1990_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1992_: u8 = 0;
    let mut v___x_1993_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1994_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1995_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1996_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1997_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1998_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1999_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2000_: usize = 0;
    let mut v___x_2001_: usize = 0;
    let mut v_a_2003_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2005_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2006_: u8 = 0;
    let mut v___x_2008_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2009_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2010_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1992_ = lean_usize_dec_lt(v_i_1988_, v_sz_1987_);
                if v___x_1992_ == 0 {
                    lean_dec(v_a_1985_);
                    v___x_1993_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_1993_, 0, v_b_1989_);
                    return v___x_1993_;
                } else {
                    v_a_1994_ = lean_array_uget_borrowed(v_as_1986_, v_i_1988_);
                    v___x_1995_ = l_Lean_Expr_mvarId_x21(v_a_1994_);
                    lean_inc(v_b_1989_);
                    lean_inc(v_a_1985_);
                    v___x_1996_ = l_Lean_Name_num___override(v_a_1985_, v_b_1989_);
                    v___x_1997_ =
                        l_Lean_MVarId_setTag___redArg(v___x_1995_, v___x_1996_, v___y_1990_);
                    if lean_obj_tag(v___x_1997_) == 0 {
                        lean_dec_ref_known(v___x_1997_, 1);
                        v___x_1998_ = lean_unsigned_to_nat(1);
                        v___x_1999_ = lean_nat_add(v_b_1989_, v___x_1998_);
                        lean_dec(v_b_1989_);
                        v___x_2000_ = 1usize;
                        v___x_2001_ = lean_usize_add(v_i_1988_, v___x_2000_);
                        v_i_1988_ = v___x_2001_;
                        v_b_1989_ = v___x_1999_;
                        state = 0;
                        continue;
                    } else {
                        lean_dec(v_b_1989_);
                        lean_dec(v_a_1985_);
                        v_a_2003_ = lean_ctor_get(v___x_1997_, 0);
                        v_isSharedCheck_2010_ = (!lean_is_exclusive(v___x_1997_)) as u8;
                        if v_isSharedCheck_2010_ == 0 {
                            v___x_2005_ = v___x_1997_;
                            v_isShared_2006_ = v_isSharedCheck_2010_;
                            state = 1;
                            continue;
                        } else {
                            lean_inc(v_a_2003_);
                            lean_dec(v___x_1997_);
                            v___x_2005_ = lean_box(0);
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
                    v_reuseFailAlloc_2009_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2009_, 0, v_a_2003_);
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
    mut v_a_2011_: *mut LeanObject,
    mut v_as_2012_: *mut LeanObject,
    mut v_sz_2013_: *mut LeanObject,
    mut v_i_2014_: *mut LeanObject,
    mut v_b_2015_: *mut LeanObject,
    mut v___y_2016_: *mut LeanObject,
    mut v___y_2017_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_boxed_2018_: usize = 0;
    let mut v_i_boxed_2019_: usize = 0;
    let mut v_res_2020_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_2018_ = lean_unbox_usize(v_sz_2013_);
    lean_dec(v_sz_2013_);
    v_i_boxed_2019_ = lean_unbox_usize(v_i_2014_);
    lean_dec(v_i_2014_);
    v_res_2020_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_CasesMatch_0__Lean_Meta_Grind_casesMatch_updateTags_spec__0___redArg(v_a_2011_, v_as_2012_, v_sz_boxed_2018_, v_i_boxed_2019_, v_b_2015_, v___y_2016_);
    lean_dec(v___y_2016_);
    lean_dec_ref(v_as_2012_);
    return v_res_2020_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_CasesMatch_0__Lean_Meta_Grind_casesMatch_updateTags(
    mut v_mvarId_2021_: *mut LeanObject,
    mut v_mvars_2022_: *mut LeanObject,
    mut v_a_2023_: *mut LeanObject,
    mut v_a_2024_: *mut LeanObject,
    mut v_a_2025_: *mut LeanObject,
    mut v_a_2026_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2028_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2029_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2030_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2031_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2032_: u8 = 0;
    let mut v_sz_2033_: usize = 0;
    let mut v___x_2034_: usize = 0;
    let mut v___x_2035_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2037_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2038_: u8 = 0;
    let mut v___x_2039_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2041_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2042_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2043_: u8 = 0;
    let mut v_unused_2044_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2045_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2047_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2048_: u8 = 0;
    let mut v___x_2050_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2051_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2052_: u8 = 0;
    let mut v___x_2053_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2054_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2055_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2056_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2057_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2058_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2060_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2061_: u8 = 0;
    let mut v___x_2063_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2064_: *mut LeanObject = core::ptr::null_mut();
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
                if lean_obj_tag(v___x_2028_) == 0 {
                    v_a_2029_ = lean_ctor_get(v___x_2028_, 0);
                    lean_inc(v_a_2029_);
                    lean_dec_ref_known(v___x_2028_, 1);
                    v___x_2030_ = lean_array_get_size(v_mvars_2022_);
                    v___x_2031_ = lean_unsigned_to_nat(1);
                    v___x_2032_ = lean_nat_dec_eq(v___x_2030_, v___x_2031_);
                    if v___x_2032_ == 0 {
                        v_sz_2033_ = lean_array_size(v_mvars_2022_);
                        v___x_2034_ = 0usize;
                        v___x_2035_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_CasesMatch_0__Lean_Meta_Grind_casesMatch_updateTags_spec__0___redArg(v_a_2029_, v_mvars_2022_, v_sz_2033_, v___x_2034_, v___x_2031_, v_a_2024_);
                        if lean_obj_tag(v___x_2035_) == 0 {
                            v_isSharedCheck_2043_ = (!lean_is_exclusive(v___x_2035_)) as u8;
                            if v_isSharedCheck_2043_ == 0 {
                                v_unused_2044_ = lean_ctor_get(v___x_2035_, 0);
                                lean_dec(v_unused_2044_);
                                v___x_2037_ = v___x_2035_;
                                v_isShared_2038_ = v_isSharedCheck_2043_;
                                state = 1;
                                continue;
                            } else {
                                lean_dec(v___x_2035_);
                                v___x_2037_ = lean_box(0);
                                v_isShared_2038_ = v_isSharedCheck_2043_;
                                state = 1;
                                continue;
                            }
                        } else {
                            v_a_2045_ = lean_ctor_get(v___x_2035_, 0);
                            v_isSharedCheck_2052_ = (!lean_is_exclusive(v___x_2035_)) as u8;
                            if v_isSharedCheck_2052_ == 0 {
                                v___x_2047_ = v___x_2035_;
                                v_isShared_2048_ = v_isSharedCheck_2052_;
                                state = 3;
                                continue;
                            } else {
                                lean_inc(v_a_2045_);
                                lean_dec(v___x_2035_);
                                v___x_2047_ = lean_box(0);
                                v_isShared_2048_ = v_isSharedCheck_2052_;
                                state = 3;
                                continue;
                            }
                        }
                    } else {
                        v___x_2053_ = l_Lean_instInhabitedExpr;
                        v___x_2054_ = lean_unsigned_to_nat(0);
                        v___x_2055_ =
                            lean_array_get_borrowed(v___x_2053_, v_mvars_2022_, v___x_2054_);
                        v___x_2056_ = l_Lean_Expr_mvarId_x21(v___x_2055_);
                        v___x_2057_ =
                            l_Lean_MVarId_setTag___redArg(v___x_2056_, v_a_2029_, v_a_2024_);
                        return v___x_2057_;
                    }
                } else {
                    v_a_2058_ = lean_ctor_get(v___x_2028_, 0);
                    v_isSharedCheck_2065_ = (!lean_is_exclusive(v___x_2028_)) as u8;
                    if v_isSharedCheck_2065_ == 0 {
                        v___x_2060_ = v___x_2028_;
                        v_isShared_2061_ = v_isSharedCheck_2065_;
                        state = 5;
                        continue;
                    } else {
                        lean_inc(v_a_2058_);
                        lean_dec(v___x_2028_);
                        v___x_2060_ = lean_box(0);
                        v_isShared_2061_ = v_isSharedCheck_2065_;
                        state = 5;
                        continue;
                    }
                }
            }
            1 => {
                v___x_2039_ = lean_box(0);
                if v_isShared_2038_ == 0 {
                    lean_ctor_set(v___x_2037_, 0, v___x_2039_);
                    v___x_2041_ = v___x_2037_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2042_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2042_, 0, v___x_2039_);
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
                    v_reuseFailAlloc_2051_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2051_, 0, v_a_2045_);
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
                    v_reuseFailAlloc_2064_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2064_, 0, v_a_2058_);
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
    mut v_mvarId_2066_: *mut LeanObject,
    mut v_mvars_2067_: *mut LeanObject,
    mut v_a_2068_: *mut LeanObject,
    mut v_a_2069_: *mut LeanObject,
    mut v_a_2070_: *mut LeanObject,
    mut v_a_2071_: *mut LeanObject,
    mut v_a_2072_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2073_: *mut LeanObject = core::ptr::null_mut();
    v_res_2073_ =
        l___private_Lean_Meta_Tactic_Grind_CasesMatch_0__Lean_Meta_Grind_casesMatch_updateTags(
            v_mvarId_2066_,
            v_mvars_2067_,
            v_a_2068_,
            v_a_2069_,
            v_a_2070_,
            v_a_2071_,
        );
    lean_dec(v_a_2071_);
    lean_dec_ref(v_a_2070_);
    lean_dec(v_a_2069_);
    lean_dec_ref(v_a_2068_);
    lean_dec_ref(v_mvars_2067_);
    return v_res_2073_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_CasesMatch_0__Lean_Meta_Grind_casesMatch_updateTags_spec__0(
    mut v_a_2074_: *mut LeanObject,
    mut v_as_2075_: *mut LeanObject,
    mut v_sz_2076_: usize,
    mut v_i_2077_: usize,
    mut v_b_2078_: *mut LeanObject,
    mut v___y_2079_: *mut LeanObject,
    mut v___y_2080_: *mut LeanObject,
    mut v___y_2081_: *mut LeanObject,
    mut v___y_2082_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2084_: *mut LeanObject = core::ptr::null_mut();
    v___x_2084_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_CasesMatch_0__Lean_Meta_Grind_casesMatch_updateTags_spec__0___redArg(v_a_2074_, v_as_2075_, v_sz_2076_, v_i_2077_, v_b_2078_, v___y_2080_);
    return v___x_2084_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_CasesMatch_0__Lean_Meta_Grind_casesMatch_updateTags_spec__0___boxed(
    mut v_a_2085_: *mut LeanObject,
    mut v_as_2086_: *mut LeanObject,
    mut v_sz_2087_: *mut LeanObject,
    mut v_i_2088_: *mut LeanObject,
    mut v_b_2089_: *mut LeanObject,
    mut v___y_2090_: *mut LeanObject,
    mut v___y_2091_: *mut LeanObject,
    mut v___y_2092_: *mut LeanObject,
    mut v___y_2093_: *mut LeanObject,
    mut v___y_2094_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_boxed_2095_: usize = 0;
    let mut v_i_boxed_2096_: usize = 0;
    let mut v_res_2097_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_2095_ = lean_unbox_usize(v_sz_2087_);
    lean_dec(v_sz_2087_);
    v_i_boxed_2096_ = lean_unbox_usize(v_i_2088_);
    lean_dec(v_i_2088_);
    v_res_2097_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_CasesMatch_0__Lean_Meta_Grind_casesMatch_updateTags_spec__0(v_a_2085_, v_as_2086_, v_sz_boxed_2095_, v_i_boxed_2096_, v_b_2089_, v___y_2090_, v___y_2091_, v___y_2092_, v___y_2093_);
    lean_dec(v___y_2093_);
    lean_dec_ref(v___y_2092_);
    lean_dec(v___y_2091_);
    lean_dec_ref(v___y_2090_);
    lean_dec_ref(v_as_2086_);
    return v_res_2097_;
}
pub unsafe fn l_Lean_MVarId_withContext___at___00Lean_Meta_Grind_casesMatch_spec__3___redArg(
    mut v_mvarId_2098_: *mut LeanObject,
    mut v_x_2099_: *mut LeanObject,
    mut v___y_2100_: *mut LeanObject,
    mut v___y_2101_: *mut LeanObject,
    mut v___y_2102_: *mut LeanObject,
    mut v___y_2103_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2105_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2106_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2108_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2109_: u8 = 0;
    let mut v___x_2111_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2112_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2113_: u8 = 0;
    let mut v_a_2114_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2116_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2117_: u8 = 0;
    let mut v___x_2119_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2120_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2121_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2105_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(
                    lean_box(0),
                    v_mvarId_2098_,
                    v_x_2099_,
                    v___y_2100_,
                    v___y_2101_,
                    v___y_2102_,
                    v___y_2103_,
                );
                if lean_obj_tag(v___x_2105_) == 0 {
                    v_a_2106_ = lean_ctor_get(v___x_2105_, 0);
                    v_isSharedCheck_2113_ = (!lean_is_exclusive(v___x_2105_)) as u8;
                    if v_isSharedCheck_2113_ == 0 {
                        v___x_2108_ = v___x_2105_;
                        v_isShared_2109_ = v_isSharedCheck_2113_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_2106_);
                        lean_dec(v___x_2105_);
                        v___x_2108_ = lean_box(0);
                        v_isShared_2109_ = v_isSharedCheck_2113_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_2114_ = lean_ctor_get(v___x_2105_, 0);
                    v_isSharedCheck_2121_ = (!lean_is_exclusive(v___x_2105_)) as u8;
                    if v_isSharedCheck_2121_ == 0 {
                        v___x_2116_ = v___x_2105_;
                        v_isShared_2117_ = v_isSharedCheck_2121_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_2114_);
                        lean_dec(v___x_2105_);
                        v___x_2116_ = lean_box(0);
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
                    v_reuseFailAlloc_2112_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2112_, 0, v_a_2106_);
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
                    v_reuseFailAlloc_2120_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2120_, 0, v_a_2114_);
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
    mut v_mvarId_2122_: *mut LeanObject,
    mut v_x_2123_: *mut LeanObject,
    mut v___y_2124_: *mut LeanObject,
    mut v___y_2125_: *mut LeanObject,
    mut v___y_2126_: *mut LeanObject,
    mut v___y_2127_: *mut LeanObject,
    mut v___y_2128_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2129_: *mut LeanObject = core::ptr::null_mut();
    v_res_2129_ = l_Lean_MVarId_withContext___at___00Lean_Meta_Grind_casesMatch_spec__3___redArg(
        v_mvarId_2122_,
        v_x_2123_,
        v___y_2124_,
        v___y_2125_,
        v___y_2126_,
        v___y_2127_,
    );
    lean_dec(v___y_2127_);
    lean_dec_ref(v___y_2126_);
    lean_dec(v___y_2125_);
    lean_dec_ref(v___y_2124_);
    return v_res_2129_;
}
pub unsafe fn l_Lean_MVarId_withContext___at___00Lean_Meta_Grind_casesMatch_spec__3(
    mut v_00_u03b1_2130_: *mut LeanObject,
    mut v_mvarId_2131_: *mut LeanObject,
    mut v_x_2132_: *mut LeanObject,
    mut v___y_2133_: *mut LeanObject,
    mut v___y_2134_: *mut LeanObject,
    mut v___y_2135_: *mut LeanObject,
    mut v___y_2136_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2138_: *mut LeanObject = core::ptr::null_mut();
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
    mut v_00_u03b1_2139_: *mut LeanObject,
    mut v_mvarId_2140_: *mut LeanObject,
    mut v_x_2141_: *mut LeanObject,
    mut v___y_2142_: *mut LeanObject,
    mut v___y_2143_: *mut LeanObject,
    mut v___y_2144_: *mut LeanObject,
    mut v___y_2145_: *mut LeanObject,
    mut v___y_2146_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2147_: *mut LeanObject = core::ptr::null_mut();
    v_res_2147_ = l_Lean_MVarId_withContext___at___00Lean_Meta_Grind_casesMatch_spec__3(
        v_00_u03b1_2139_,
        v_mvarId_2140_,
        v_x_2141_,
        v___y_2142_,
        v___y_2143_,
        v___y_2144_,
        v___y_2145_,
    );
    lean_dec(v___y_2145_);
    lean_dec_ref(v___y_2144_);
    lean_dec(v___y_2143_);
    lean_dec_ref(v___y_2142_);
    return v_res_2147_;
}
pub unsafe fn l_List_mapTR_loop___at___00Lean_Meta_Grind_casesMatch_spec__2(
    mut v_a_2148_: *mut LeanObject,
    mut v_a_2149_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2150_: *mut LeanObject = core::ptr::null_mut();
    let mut v_head_2151_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_2152_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2154_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2155_: u8 = 0;
    let mut v___x_2156_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2158_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2160_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2161_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_a_2148_) == 0 {
                    v___x_2150_ = l_List_reverse___redArg(v_a_2149_);
                    return v___x_2150_;
                } else {
                    v_head_2151_ = lean_ctor_get(v_a_2148_, 0);
                    v_tail_2152_ = lean_ctor_get(v_a_2148_, 1);
                    v_isSharedCheck_2161_ = (!lean_is_exclusive(v_a_2148_)) as u8;
                    if v_isSharedCheck_2161_ == 0 {
                        v___x_2154_ = v_a_2148_;
                        v_isShared_2155_ = v_isSharedCheck_2161_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_tail_2152_);
                        lean_inc(v_head_2151_);
                        lean_dec(v_a_2148_);
                        v___x_2154_ = lean_box(0);
                        v_isShared_2155_ = v_isSharedCheck_2161_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_2156_ = l_Lean_Expr_mvarId_x21(v_head_2151_);
                lean_dec(v_head_2151_);
                if v_isShared_2155_ == 0 {
                    lean_ctor_set(v___x_2154_, 1, v_a_2149_);
                    lean_ctor_set(v___x_2154_, 0, v___x_2156_);
                    v___x_2158_ = v___x_2154_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2160_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2160_, 0, v___x_2156_);
                    lean_ctor_set(v_reuseFailAlloc_2160_, 1, v_a_2149_);
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
-> *mut LeanObject {
    let mut v___x_2162_: *mut LeanObject = core::ptr::null_mut();
    v___x_2162_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
    return v___x_2162_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Meta_Grind_casesMatch_spec__0_spec__0_spec__2_spec__7_spec__10_spec__12_spec__15___redArg___closed__1()
-> *mut LeanObject {
    let mut v___x_2163_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2164_: *mut LeanObject = core::ptr::null_mut();
    v___x_2163_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Meta_Grind_casesMatch_spec__0_spec__0_spec__2_spec__7_spec__10_spec__12_spec__15___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Meta_Grind_casesMatch_spec__0_spec__0_spec__2_spec__7_spec__10_spec__12_spec__15___redArg___closed__0_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Meta_Grind_casesMatch_spec__0_spec__0_spec__2_spec__7_spec__10_spec__12_spec__15___redArg___closed__0);
    v___x_2164_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_2164_, 0, v___x_2163_);
    return v___x_2164_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Meta_Grind_casesMatch_spec__0_spec__0_spec__2_spec__7_spec__10_spec__12_spec__15___redArg___closed__2()
-> *mut LeanObject {
    let mut v___x_2165_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2166_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2167_: *mut LeanObject = core::ptr::null_mut();
    v___x_2165_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Meta_Grind_casesMatch_spec__0_spec__0_spec__2_spec__7_spec__10_spec__12_spec__15___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Meta_Grind_casesMatch_spec__0_spec__0_spec__2_spec__7_spec__10_spec__12_spec__15___redArg___closed__1_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Meta_Grind_casesMatch_spec__0_spec__0_spec__2_spec__7_spec__10_spec__12_spec__15___redArg___closed__1);
    v___x_2166_ = lean_unsigned_to_nat(0);
    v___x_2167_ = lean_alloc_ctor(0, 10, (0) as u32);
    lean_ctor_set(v___x_2167_, 0, v___x_2166_);
    lean_ctor_set(v___x_2167_, 1, v___x_2166_);
    lean_ctor_set(v___x_2167_, 2, v___x_2166_);
    lean_ctor_set(v___x_2167_, 3, v___x_2166_);
    lean_ctor_set(v___x_2167_, 4, v___x_2165_);
    lean_ctor_set(v___x_2167_, 5, v___x_2165_);
    lean_ctor_set(v___x_2167_, 6, v___x_2165_);
    lean_ctor_set(v___x_2167_, 7, v___x_2165_);
    lean_ctor_set(v___x_2167_, 8, v___x_2165_);
    lean_ctor_set(v___x_2167_, 9, v___x_2165_);
    return v___x_2167_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Meta_Grind_casesMatch_spec__0_spec__0_spec__2_spec__7_spec__10_spec__12_spec__15___redArg___closed__3()
-> *mut LeanObject {
    let mut v___x_2168_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2169_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2170_: *mut LeanObject = core::ptr::null_mut();
    v___x_2168_ = lean_unsigned_to_nat(32);
    v___x_2169_ = lean_mk_empty_array_with_capacity(v___x_2168_);
    v___x_2170_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_2170_, 0, v___x_2169_);
    return v___x_2170_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Meta_Grind_casesMatch_spec__0_spec__0_spec__2_spec__7_spec__10_spec__12_spec__15___redArg___closed__4()
-> *mut LeanObject {
    let mut v___x_2171_: usize = 0;
    let mut v___x_2172_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2173_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2174_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2175_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2176_: *mut LeanObject = core::ptr::null_mut();
    v___x_2171_ = 5usize;
    v___x_2172_ = lean_unsigned_to_nat(0);
    v___x_2173_ = lean_unsigned_to_nat(32);
    v___x_2174_ = lean_mk_empty_array_with_capacity(v___x_2173_);
    v___x_2175_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Meta_Grind_casesMatch_spec__0_spec__0_spec__2_spec__7_spec__10_spec__12_spec__15___redArg___closed__3), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Meta_Grind_casesMatch_spec__0_spec__0_spec__2_spec__7_spec__10_spec__12_spec__15___redArg___closed__3_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Meta_Grind_casesMatch_spec__0_spec__0_spec__2_spec__7_spec__10_spec__12_spec__15___redArg___closed__3);
    v___x_2176_ = lean_alloc_ctor(0, 4, (core::mem::size_of::<usize>() * 1) as u32);
    lean_ctor_set(v___x_2176_, 0, v___x_2175_);
    lean_ctor_set(v___x_2176_, 1, v___x_2174_);
    lean_ctor_set(v___x_2176_, 2, v___x_2172_);
    lean_ctor_set(v___x_2176_, 3, v___x_2172_);
    lean_ctor_set_usize(v___x_2176_, 4, v___x_2171_);
    return v___x_2176_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Meta_Grind_casesMatch_spec__0_spec__0_spec__2_spec__7_spec__10_spec__12_spec__15___redArg___closed__5()
-> *mut LeanObject {
    let mut v___x_2177_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2178_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2179_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2180_: *mut LeanObject = core::ptr::null_mut();
    v___x_2177_ = lean_box(1);
    v___x_2178_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Meta_Grind_casesMatch_spec__0_spec__0_spec__2_spec__7_spec__10_spec__12_spec__15___redArg___closed__4), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Meta_Grind_casesMatch_spec__0_spec__0_spec__2_spec__7_spec__10_spec__12_spec__15___redArg___closed__4_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Meta_Grind_casesMatch_spec__0_spec__0_spec__2_spec__7_spec__10_spec__12_spec__15___redArg___closed__4);
    v___x_2179_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Meta_Grind_casesMatch_spec__0_spec__0_spec__2_spec__7_spec__10_spec__12_spec__15___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Meta_Grind_casesMatch_spec__0_spec__0_spec__2_spec__7_spec__10_spec__12_spec__15___redArg___closed__1_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Meta_Grind_casesMatch_spec__0_spec__0_spec__2_spec__7_spec__10_spec__12_spec__15___redArg___closed__1);
    v___x_2180_ = lean_alloc_ctor(0, 3, (0) as u32);
    lean_ctor_set(v___x_2180_, 0, v___x_2179_);
    lean_ctor_set(v___x_2180_, 1, v___x_2178_);
    lean_ctor_set(v___x_2180_, 2, v___x_2177_);
    return v___x_2180_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Meta_Grind_casesMatch_spec__0_spec__0_spec__2_spec__7_spec__10_spec__12_spec__15___redArg___closed__7()
-> *mut LeanObject {
    let mut v___x_2182_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2183_: *mut LeanObject = core::ptr::null_mut();
    v___x_2182_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Meta_Grind_casesMatch_spec__0_spec__0_spec__2_spec__7_spec__10_spec__12_spec__15___redArg___closed__6;
    v___x_2183_ = l_Lean_stringToMessageData(v___x_2182_);
    return v___x_2183_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Meta_Grind_casesMatch_spec__0_spec__0_spec__2_spec__7_spec__10_spec__12_spec__15___redArg___closed__9()
-> *mut LeanObject {
    let mut v___x_2185_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2186_: *mut LeanObject = core::ptr::null_mut();
    v___x_2185_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Meta_Grind_casesMatch_spec__0_spec__0_spec__2_spec__7_spec__10_spec__12_spec__15___redArg___closed__8;
    v___x_2186_ = l_Lean_stringToMessageData(v___x_2185_);
    return v___x_2186_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Meta_Grind_casesMatch_spec__0_spec__0_spec__2_spec__7_spec__10_spec__12_spec__15___redArg___closed__11()
-> *mut LeanObject {
    let mut v___x_2188_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2189_: *mut LeanObject = core::ptr::null_mut();
    v___x_2188_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Meta_Grind_casesMatch_spec__0_spec__0_spec__2_spec__7_spec__10_spec__12_spec__15___redArg___closed__10;
    v___x_2189_ = l_Lean_stringToMessageData(v___x_2188_);
    return v___x_2189_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Meta_Grind_casesMatch_spec__0_spec__0_spec__2_spec__7_spec__10_spec__12_spec__15___redArg___closed__13()
-> *mut LeanObject {
    let mut v___x_2191_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2192_: *mut LeanObject = core::ptr::null_mut();
    v___x_2191_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Meta_Grind_casesMatch_spec__0_spec__0_spec__2_spec__7_spec__10_spec__12_spec__15___redArg___closed__12;
    v___x_2192_ = l_Lean_stringToMessageData(v___x_2191_);
    return v___x_2192_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Meta_Grind_casesMatch_spec__0_spec__0_spec__2_spec__7_spec__10_spec__12_spec__15___redArg___closed__15()
-> *mut LeanObject {
    let mut v___x_2194_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2195_: *mut LeanObject = core::ptr::null_mut();
    v___x_2194_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Meta_Grind_casesMatch_spec__0_spec__0_spec__2_spec__7_spec__10_spec__12_spec__15___redArg___closed__14;
    v___x_2195_ = l_Lean_stringToMessageData(v___x_2194_);
    return v___x_2195_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Meta_Grind_casesMatch_spec__0_spec__0_spec__2_spec__7_spec__10_spec__12_spec__15___redArg___closed__17()
-> *mut LeanObject {
    let mut v___x_2197_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2198_: *mut LeanObject = core::ptr::null_mut();
    v___x_2197_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Meta_Grind_casesMatch_spec__0_spec__0_spec__2_spec__7_spec__10_spec__12_spec__15___redArg___closed__16;
    v___x_2198_ = l_Lean_stringToMessageData(v___x_2197_);
    return v___x_2198_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Meta_Grind_casesMatch_spec__0_spec__0_spec__2_spec__7_spec__10_spec__12_spec__15___redArg___closed__19()
-> *mut LeanObject {
    let mut v___x_2200_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2201_: *mut LeanObject = core::ptr::null_mut();
    v___x_2200_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Meta_Grind_casesMatch_spec__0_spec__0_spec__2_spec__7_spec__10_spec__12_spec__15___redArg___closed__18;
    v___x_2201_ = l_Lean_stringToMessageData(v___x_2200_);
    return v___x_2201_;
}
pub unsafe fn l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Meta_Grind_casesMatch_spec__0_spec__0_spec__2_spec__7_spec__10_spec__12_spec__15___redArg(
    mut v_msg_2202_: *mut LeanObject,
    mut v_declHint_2203_: *mut LeanObject,
    mut v___y_2204_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2206_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_2207_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2208_: u8 = 0;
    let mut v_isExporting_2209_: u8 = 0;
    let mut v___x_2210_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2211_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2212_: u8 = 0;
    let mut v___x_2213_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2214_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2215_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2216_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2217_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2218_: *mut LeanObject = core::ptr::null_mut();
    let mut v_c_2219_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2220_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2221_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2222_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2223_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2224_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2225_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2226_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2227_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_2228_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2230_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2231_: u8 = 0;
    let mut v___x_2232_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2233_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2234_: *mut LeanObject = core::ptr::null_mut();
    let mut v_mod_2235_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2236_: u8 = 0;
    let mut v___x_2237_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2238_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2239_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2240_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2241_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2242_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2243_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2244_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2245_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2246_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2248_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2249_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2250_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2251_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2252_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2253_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2254_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2255_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2256_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2257_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2258_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2259_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2261_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2262_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2263_: u8 = 0;
    let mut v___x_2264_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2206_ = lean_st_ref_get(v___y_2204_);
                v_env_2207_ = lean_ctor_get(v___x_2206_, 0);
                lean_inc_ref(v_env_2207_);
                lean_dec(v___x_2206_);
                v___x_2208_ = l_Lean_Name_isAnonymous(v_declHint_2203_);
                if v___x_2208_ == 0 {
                    v_isExporting_2209_ = lean_ctor_get_uint8(
                        v_env_2207_,
                        (core::mem::size_of::<*mut LeanObject>() * 8) as u32,
                    );
                    if v_isExporting_2209_ == 0 {
                        lean_dec_ref(v_env_2207_);
                        lean_dec(v_declHint_2203_);
                        v___x_2210_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v___x_2210_, 0, v_msg_2202_);
                        return v___x_2210_;
                    } else {
                        lean_inc_ref(v_env_2207_);
                        v___x_2211_ = l_Lean_Environment_setExporting(v_env_2207_, v___x_2208_);
                        lean_inc(v_declHint_2203_);
                        lean_inc_ref(v___x_2211_);
                        v___x_2212_ = l_Lean_Environment_contains(
                            v___x_2211_,
                            v_declHint_2203_,
                            v_isExporting_2209_,
                        );
                        if v___x_2212_ == 0 {
                            lean_dec_ref(v___x_2211_);
                            lean_dec_ref(v_env_2207_);
                            lean_dec(v_declHint_2203_);
                            v___x_2213_ = lean_alloc_ctor(0, 1, (0) as u32);
                            lean_ctor_set(v___x_2213_, 0, v_msg_2202_);
                            return v___x_2213_;
                        } else {
                            v___x_2214_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Meta_Grind_casesMatch_spec__0_spec__0_spec__2_spec__7_spec__10_spec__12_spec__15___redArg___closed__2), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Meta_Grind_casesMatch_spec__0_spec__0_spec__2_spec__7_spec__10_spec__12_spec__15___redArg___closed__2_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Meta_Grind_casesMatch_spec__0_spec__0_spec__2_spec__7_spec__10_spec__12_spec__15___redArg___closed__2);
                            v___x_2215_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Meta_Grind_casesMatch_spec__0_spec__0_spec__2_spec__7_spec__10_spec__12_spec__15___redArg___closed__5), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Meta_Grind_casesMatch_spec__0_spec__0_spec__2_spec__7_spec__10_spec__12_spec__15___redArg___closed__5_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Meta_Grind_casesMatch_spec__0_spec__0_spec__2_spec__7_spec__10_spec__12_spec__15___redArg___closed__5);
                            v___x_2216_ = l_Lean_Options_empty;
                            v___x_2217_ = lean_alloc_ctor(0, 4, (0) as u32);
                            lean_ctor_set(v___x_2217_, 0, v___x_2211_);
                            lean_ctor_set(v___x_2217_, 1, v___x_2214_);
                            lean_ctor_set(v___x_2217_, 2, v___x_2215_);
                            lean_ctor_set(v___x_2217_, 3, v___x_2216_);
                            lean_inc(v_declHint_2203_);
                            v___x_2218_ =
                                l_Lean_MessageData_ofConstName(v_declHint_2203_, v___x_2208_);
                            v_c_2219_ = lean_alloc_ctor(3, 2, (0) as u32);
                            lean_ctor_set(v_c_2219_, 0, v___x_2217_);
                            lean_ctor_set(v_c_2219_, 1, v___x_2218_);
                            v___x_2220_ = l_Lean_Environment_getModuleIdxFor_x3f(
                                v_env_2207_,
                                v_declHint_2203_,
                            );
                            if lean_obj_tag(v___x_2220_) == 0 {
                                lean_dec_ref(v_env_2207_);
                                lean_dec(v_declHint_2203_);
                                v___x_2221_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Meta_Grind_casesMatch_spec__0_spec__0_spec__2_spec__7_spec__10_spec__12_spec__15___redArg___closed__7), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Meta_Grind_casesMatch_spec__0_spec__0_spec__2_spec__7_spec__10_spec__12_spec__15___redArg___closed__7_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Meta_Grind_casesMatch_spec__0_spec__0_spec__2_spec__7_spec__10_spec__12_spec__15___redArg___closed__7);
                                v___x_2222_ = lean_alloc_ctor(7, 2, (0) as u32);
                                lean_ctor_set(v___x_2222_, 0, v___x_2221_);
                                lean_ctor_set(v___x_2222_, 1, v_c_2219_);
                                v___x_2223_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Meta_Grind_casesMatch_spec__0_spec__0_spec__2_spec__7_spec__10_spec__12_spec__15___redArg___closed__9), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Meta_Grind_casesMatch_spec__0_spec__0_spec__2_spec__7_spec__10_spec__12_spec__15___redArg___closed__9_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Meta_Grind_casesMatch_spec__0_spec__0_spec__2_spec__7_spec__10_spec__12_spec__15___redArg___closed__9);
                                v___x_2224_ = lean_alloc_ctor(7, 2, (0) as u32);
                                lean_ctor_set(v___x_2224_, 0, v___x_2222_);
                                lean_ctor_set(v___x_2224_, 1, v___x_2223_);
                                v___x_2225_ = l_Lean_MessageData_note(v___x_2224_);
                                v___x_2226_ = lean_alloc_ctor(7, 2, (0) as u32);
                                lean_ctor_set(v___x_2226_, 0, v_msg_2202_);
                                lean_ctor_set(v___x_2226_, 1, v___x_2225_);
                                v___x_2227_ = lean_alloc_ctor(0, 1, (0) as u32);
                                lean_ctor_set(v___x_2227_, 0, v___x_2226_);
                                return v___x_2227_;
                            } else {
                                v_val_2228_ = lean_ctor_get(v___x_2220_, 0);
                                v_isSharedCheck_2263_ = (!lean_is_exclusive(v___x_2220_)) as u8;
                                if v_isSharedCheck_2263_ == 0 {
                                    v___x_2230_ = v___x_2220_;
                                    v_isShared_2231_ = v_isSharedCheck_2263_;
                                    state = 1;
                                    continue;
                                } else {
                                    lean_inc(v_val_2228_);
                                    lean_dec(v___x_2220_);
                                    v___x_2230_ = lean_box(0);
                                    v_isShared_2231_ = v_isSharedCheck_2263_;
                                    state = 1;
                                    continue;
                                }
                            }
                        }
                    }
                } else {
                    lean_dec_ref(v_env_2207_);
                    lean_dec(v_declHint_2203_);
                    v___x_2264_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_2264_, 0, v_msg_2202_);
                    return v___x_2264_;
                }
            }
            1 => {
                v___x_2232_ = lean_box(0);
                v___x_2233_ = l_Lean_Environment_header(v_env_2207_);
                lean_dec_ref(v_env_2207_);
                v___x_2234_ = l_Lean_EnvironmentHeader_moduleNames(v___x_2233_);
                v_mod_2235_ = lean_array_get(v___x_2232_, v___x_2234_, v_val_2228_);
                lean_dec(v_val_2228_);
                lean_dec_ref(v___x_2234_);
                v___x_2236_ = l_Lean_isPrivateName(v_declHint_2203_);
                lean_dec(v_declHint_2203_);
                if v___x_2236_ == 0 {
                    v___x_2237_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Meta_Grind_casesMatch_spec__0_spec__0_spec__2_spec__7_spec__10_spec__12_spec__15___redArg___closed__11), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Meta_Grind_casesMatch_spec__0_spec__0_spec__2_spec__7_spec__10_spec__12_spec__15___redArg___closed__11_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Meta_Grind_casesMatch_spec__0_spec__0_spec__2_spec__7_spec__10_spec__12_spec__15___redArg___closed__11);
                    v___x_2238_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_2238_, 0, v___x_2237_);
                    lean_ctor_set(v___x_2238_, 1, v_c_2219_);
                    v___x_2239_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Meta_Grind_casesMatch_spec__0_spec__0_spec__2_spec__7_spec__10_spec__12_spec__15___redArg___closed__13), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Meta_Grind_casesMatch_spec__0_spec__0_spec__2_spec__7_spec__10_spec__12_spec__15___redArg___closed__13_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Meta_Grind_casesMatch_spec__0_spec__0_spec__2_spec__7_spec__10_spec__12_spec__15___redArg___closed__13);
                    v___x_2240_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_2240_, 0, v___x_2238_);
                    lean_ctor_set(v___x_2240_, 1, v___x_2239_);
                    v___x_2241_ = l_Lean_MessageData_ofName(v_mod_2235_);
                    v___x_2242_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_2242_, 0, v___x_2240_);
                    lean_ctor_set(v___x_2242_, 1, v___x_2241_);
                    v___x_2243_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Meta_Grind_casesMatch_spec__0_spec__0_spec__2_spec__7_spec__10_spec__12_spec__15___redArg___closed__15), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Meta_Grind_casesMatch_spec__0_spec__0_spec__2_spec__7_spec__10_spec__12_spec__15___redArg___closed__15_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Meta_Grind_casesMatch_spec__0_spec__0_spec__2_spec__7_spec__10_spec__12_spec__15___redArg___closed__15);
                    v___x_2244_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_2244_, 0, v___x_2242_);
                    lean_ctor_set(v___x_2244_, 1, v___x_2243_);
                    v___x_2245_ = l_Lean_MessageData_note(v___x_2244_);
                    v___x_2246_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_2246_, 0, v_msg_2202_);
                    lean_ctor_set(v___x_2246_, 1, v___x_2245_);
                    if v_isShared_2231_ == 0 {
                        lean_ctor_set_tag(v___x_2230_, 0);
                        lean_ctor_set(v___x_2230_, 0, v___x_2246_);
                        v___x_2248_ = v___x_2230_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_2249_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_2249_, 0, v___x_2246_);
                        v___x_2248_ = v_reuseFailAlloc_2249_;
                        state = 2;
                        continue;
                    }
                } else {
                    v___x_2250_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Meta_Grind_casesMatch_spec__0_spec__0_spec__2_spec__7_spec__10_spec__12_spec__15___redArg___closed__7), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Meta_Grind_casesMatch_spec__0_spec__0_spec__2_spec__7_spec__10_spec__12_spec__15___redArg___closed__7_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Meta_Grind_casesMatch_spec__0_spec__0_spec__2_spec__7_spec__10_spec__12_spec__15___redArg___closed__7);
                    v___x_2251_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_2251_, 0, v___x_2250_);
                    lean_ctor_set(v___x_2251_, 1, v_c_2219_);
                    v___x_2252_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Meta_Grind_casesMatch_spec__0_spec__0_spec__2_spec__7_spec__10_spec__12_spec__15___redArg___closed__17), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Meta_Grind_casesMatch_spec__0_spec__0_spec__2_spec__7_spec__10_spec__12_spec__15___redArg___closed__17_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Meta_Grind_casesMatch_spec__0_spec__0_spec__2_spec__7_spec__10_spec__12_spec__15___redArg___closed__17);
                    v___x_2253_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_2253_, 0, v___x_2251_);
                    lean_ctor_set(v___x_2253_, 1, v___x_2252_);
                    v___x_2254_ = l_Lean_MessageData_ofName(v_mod_2235_);
                    v___x_2255_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_2255_, 0, v___x_2253_);
                    lean_ctor_set(v___x_2255_, 1, v___x_2254_);
                    v___x_2256_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Meta_Grind_casesMatch_spec__0_spec__0_spec__2_spec__7_spec__10_spec__12_spec__15___redArg___closed__19), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Meta_Grind_casesMatch_spec__0_spec__0_spec__2_spec__7_spec__10_spec__12_spec__15___redArg___closed__19_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Meta_Grind_casesMatch_spec__0_spec__0_spec__2_spec__7_spec__10_spec__12_spec__15___redArg___closed__19);
                    v___x_2257_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_2257_, 0, v___x_2255_);
                    lean_ctor_set(v___x_2257_, 1, v___x_2256_);
                    v___x_2258_ = l_Lean_MessageData_note(v___x_2257_);
                    v___x_2259_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_2259_, 0, v_msg_2202_);
                    lean_ctor_set(v___x_2259_, 1, v___x_2258_);
                    if v_isShared_2231_ == 0 {
                        lean_ctor_set_tag(v___x_2230_, 0);
                        lean_ctor_set(v___x_2230_, 0, v___x_2259_);
                        v___x_2261_ = v___x_2230_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_2262_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_2262_, 0, v___x_2259_);
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
    mut v_msg_2265_: *mut LeanObject,
    mut v_declHint_2266_: *mut LeanObject,
    mut v___y_2267_: *mut LeanObject,
    mut v___y_2268_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2269_: *mut LeanObject = core::ptr::null_mut();
    v_res_2269_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Meta_Grind_casesMatch_spec__0_spec__0_spec__2_spec__7_spec__10_spec__12_spec__15___redArg(v_msg_2265_, v_declHint_2266_, v___y_2267_);
    lean_dec(v___y_2267_);
    return v_res_2269_;
}
pub unsafe fn l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Meta_Grind_casesMatch_spec__0_spec__0_spec__2_spec__7_spec__10_spec__12(
    mut v_msg_2270_: *mut LeanObject,
    mut v_declHint_2271_: *mut LeanObject,
    mut v___y_2272_: *mut LeanObject,
    mut v___y_2273_: *mut LeanObject,
    mut v___y_2274_: *mut LeanObject,
    mut v___y_2275_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2277_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2278_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2280_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2281_: u8 = 0;
    let mut v___x_2282_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2283_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2285_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2286_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2287_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2277_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Meta_Grind_casesMatch_spec__0_spec__0_spec__2_spec__7_spec__10_spec__12_spec__15___redArg(v_msg_2270_, v_declHint_2271_, v___y_2275_);
                v_a_2278_ = lean_ctor_get(v___x_2277_, 0);
                v_isSharedCheck_2287_ = (!lean_is_exclusive(v___x_2277_)) as u8;
                if v_isSharedCheck_2287_ == 0 {
                    v___x_2280_ = v___x_2277_;
                    v_isShared_2281_ = v_isSharedCheck_2287_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_a_2278_);
                    lean_dec(v___x_2277_);
                    v___x_2280_ = lean_box(0);
                    v_isShared_2281_ = v_isSharedCheck_2287_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_2282_ = l_Lean_unknownIdentifierMessageTag;
                v___x_2283_ = lean_alloc_ctor(8, 2, (0) as u32);
                lean_ctor_set(v___x_2283_, 0, v___x_2282_);
                lean_ctor_set(v___x_2283_, 1, v_a_2278_);
                if v_isShared_2281_ == 0 {
                    lean_ctor_set(v___x_2280_, 0, v___x_2283_);
                    v___x_2285_ = v___x_2280_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2286_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2286_, 0, v___x_2283_);
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
    mut v_msg_2288_: *mut LeanObject,
    mut v_declHint_2289_: *mut LeanObject,
    mut v___y_2290_: *mut LeanObject,
    mut v___y_2291_: *mut LeanObject,
    mut v___y_2292_: *mut LeanObject,
    mut v___y_2293_: *mut LeanObject,
    mut v___y_2294_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2295_: *mut LeanObject = core::ptr::null_mut();
    v_res_2295_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Meta_Grind_casesMatch_spec__0_spec__0_spec__2_spec__7_spec__10_spec__12(v_msg_2288_, v_declHint_2289_, v___y_2290_, v___y_2291_, v___y_2292_, v___y_2293_);
    lean_dec(v___y_2293_);
    lean_dec_ref(v___y_2292_);
    lean_dec(v___y_2291_);
    lean_dec_ref(v___y_2290_);
    return v_res_2295_;
}
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Meta_Grind_casesMatch_spec__0_spec__0_spec__2_spec__7_spec__10_spec__13_spec__17_spec__19(
    mut v_msgData_2296_: *mut LeanObject,
    mut v___y_2297_: *mut LeanObject,
    mut v___y_2298_: *mut LeanObject,
    mut v___y_2299_: *mut LeanObject,
    mut v___y_2300_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2302_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_2303_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2304_: *mut LeanObject = core::ptr::null_mut();
    let mut v_mctx_2305_: *mut LeanObject = core::ptr::null_mut();
    let mut v_lctx_2306_: *mut LeanObject = core::ptr::null_mut();
    let mut v_options_2307_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2308_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2309_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2310_: *mut LeanObject = core::ptr::null_mut();
    v___x_2302_ = lean_st_ref_get(v___y_2300_);
    v_env_2303_ = lean_ctor_get(v___x_2302_, 0);
    lean_inc_ref(v_env_2303_);
    lean_dec(v___x_2302_);
    v___x_2304_ = lean_st_ref_get(v___y_2298_);
    v_mctx_2305_ = lean_ctor_get(v___x_2304_, 0);
    lean_inc_ref(v_mctx_2305_);
    lean_dec(v___x_2304_);
    v_lctx_2306_ = lean_ctor_get(v___y_2297_, 2);
    v_options_2307_ = lean_ctor_get(v___y_2299_, 2);
    lean_inc_ref(v_options_2307_);
    lean_inc_ref(v_lctx_2306_);
    v___x_2308_ = lean_alloc_ctor(0, 4, (0) as u32);
    lean_ctor_set(v___x_2308_, 0, v_env_2303_);
    lean_ctor_set(v___x_2308_, 1, v_mctx_2305_);
    lean_ctor_set(v___x_2308_, 2, v_lctx_2306_);
    lean_ctor_set(v___x_2308_, 3, v_options_2307_);
    v___x_2309_ = lean_alloc_ctor(3, 2, (0) as u32);
    lean_ctor_set(v___x_2309_, 0, v___x_2308_);
    lean_ctor_set(v___x_2309_, 1, v_msgData_2296_);
    v___x_2310_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_2310_, 0, v___x_2309_);
    return v___x_2310_;
}
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Meta_Grind_casesMatch_spec__0_spec__0_spec__2_spec__7_spec__10_spec__13_spec__17_spec__19___boxed(
    mut v_msgData_2311_: *mut LeanObject,
    mut v___y_2312_: *mut LeanObject,
    mut v___y_2313_: *mut LeanObject,
    mut v___y_2314_: *mut LeanObject,
    mut v___y_2315_: *mut LeanObject,
    mut v___y_2316_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2317_: *mut LeanObject = core::ptr::null_mut();
    v_res_2317_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Meta_Grind_casesMatch_spec__0_spec__0_spec__2_spec__7_spec__10_spec__13_spec__17_spec__19(v_msgData_2311_, v___y_2312_, v___y_2313_, v___y_2314_, v___y_2315_);
    lean_dec(v___y_2315_);
    lean_dec_ref(v___y_2314_);
    lean_dec(v___y_2313_);
    lean_dec_ref(v___y_2312_);
    return v_res_2317_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Meta_Grind_casesMatch_spec__0_spec__0_spec__2_spec__7_spec__10_spec__13_spec__17___redArg(
    mut v_msg_2318_: *mut LeanObject,
    mut v___y_2319_: *mut LeanObject,
    mut v___y_2320_: *mut LeanObject,
    mut v___y_2321_: *mut LeanObject,
    mut v___y_2322_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_ref_2324_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2325_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2326_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2328_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2329_: u8 = 0;
    let mut v___x_2330_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2332_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2333_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2334_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ref_2324_ = lean_ctor_get(v___y_2321_, 5);
                v___x_2325_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Meta_Grind_casesMatch_spec__0_spec__0_spec__2_spec__7_spec__10_spec__13_spec__17_spec__19(v_msg_2318_, v___y_2319_, v___y_2320_, v___y_2321_, v___y_2322_);
                v_a_2326_ = lean_ctor_get(v___x_2325_, 0);
                v_isSharedCheck_2334_ = (!lean_is_exclusive(v___x_2325_)) as u8;
                if v_isSharedCheck_2334_ == 0 {
                    v___x_2328_ = v___x_2325_;
                    v_isShared_2329_ = v_isSharedCheck_2334_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_a_2326_);
                    lean_dec(v___x_2325_);
                    v___x_2328_ = lean_box(0);
                    v_isShared_2329_ = v_isSharedCheck_2334_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                lean_inc(v_ref_2324_);
                v___x_2330_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_2330_, 0, v_ref_2324_);
                lean_ctor_set(v___x_2330_, 1, v_a_2326_);
                if v_isShared_2329_ == 0 {
                    lean_ctor_set_tag(v___x_2328_, 1);
                    lean_ctor_set(v___x_2328_, 0, v___x_2330_);
                    v___x_2332_ = v___x_2328_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2333_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2333_, 0, v___x_2330_);
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
    mut v_msg_2335_: *mut LeanObject,
    mut v___y_2336_: *mut LeanObject,
    mut v___y_2337_: *mut LeanObject,
    mut v___y_2338_: *mut LeanObject,
    mut v___y_2339_: *mut LeanObject,
    mut v___y_2340_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2341_: *mut LeanObject = core::ptr::null_mut();
    v_res_2341_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Meta_Grind_casesMatch_spec__0_spec__0_spec__2_spec__7_spec__10_spec__13_spec__17___redArg(v_msg_2335_, v___y_2336_, v___y_2337_, v___y_2338_, v___y_2339_);
    lean_dec(v___y_2339_);
    lean_dec_ref(v___y_2338_);
    lean_dec(v___y_2337_);
    lean_dec_ref(v___y_2336_);
    return v_res_2341_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Meta_Grind_casesMatch_spec__0_spec__0_spec__2_spec__7_spec__10_spec__13___redArg(
    mut v_ref_2342_: *mut LeanObject,
    mut v_msg_2343_: *mut LeanObject,
    mut v___y_2344_: *mut LeanObject,
    mut v___y_2345_: *mut LeanObject,
    mut v___y_2346_: *mut LeanObject,
    mut v___y_2347_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_fileName_2349_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fileMap_2350_: *mut LeanObject = core::ptr::null_mut();
    let mut v_options_2351_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currRecDepth_2352_: *mut LeanObject = core::ptr::null_mut();
    let mut v_maxRecDepth_2353_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ref_2354_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currNamespace_2355_: *mut LeanObject = core::ptr::null_mut();
    let mut v_openDecls_2356_: *mut LeanObject = core::ptr::null_mut();
    let mut v_initHeartbeats_2357_: *mut LeanObject = core::ptr::null_mut();
    let mut v_maxHeartbeats_2358_: *mut LeanObject = core::ptr::null_mut();
    let mut v_quotContext_2359_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currMacroScope_2360_: *mut LeanObject = core::ptr::null_mut();
    let mut v_diag_2361_: u8 = 0;
    let mut v_cancelTk_x3f_2362_: *mut LeanObject = core::ptr::null_mut();
    let mut v_suppressElabErrors_2363_: u8 = 0;
    let mut v_inheritedTraceOptions_2364_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ref_2365_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2366_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2367_: *mut LeanObject = core::ptr::null_mut();
    v_fileName_2349_ = lean_ctor_get(v___y_2346_, 0);
    v_fileMap_2350_ = lean_ctor_get(v___y_2346_, 1);
    v_options_2351_ = lean_ctor_get(v___y_2346_, 2);
    v_currRecDepth_2352_ = lean_ctor_get(v___y_2346_, 3);
    v_maxRecDepth_2353_ = lean_ctor_get(v___y_2346_, 4);
    v_ref_2354_ = lean_ctor_get(v___y_2346_, 5);
    v_currNamespace_2355_ = lean_ctor_get(v___y_2346_, 6);
    v_openDecls_2356_ = lean_ctor_get(v___y_2346_, 7);
    v_initHeartbeats_2357_ = lean_ctor_get(v___y_2346_, 8);
    v_maxHeartbeats_2358_ = lean_ctor_get(v___y_2346_, 9);
    v_quotContext_2359_ = lean_ctor_get(v___y_2346_, 10);
    v_currMacroScope_2360_ = lean_ctor_get(v___y_2346_, 11);
    v_diag_2361_ = lean_ctor_get_uint8(
        v___y_2346_,
        (core::mem::size_of::<*mut LeanObject>() * 14) as u32,
    );
    v_cancelTk_x3f_2362_ = lean_ctor_get(v___y_2346_, 12);
    v_suppressElabErrors_2363_ = lean_ctor_get_uint8(
        v___y_2346_,
        (core::mem::size_of::<*mut LeanObject>() * 14 + 1) as u32,
    );
    v_inheritedTraceOptions_2364_ = lean_ctor_get(v___y_2346_, 13);
    v_ref_2365_ = l_Lean_replaceRef(v_ref_2342_, v_ref_2354_);
    lean_inc_ref(v_inheritedTraceOptions_2364_);
    lean_inc(v_cancelTk_x3f_2362_);
    lean_inc(v_currMacroScope_2360_);
    lean_inc(v_quotContext_2359_);
    lean_inc(v_maxHeartbeats_2358_);
    lean_inc(v_initHeartbeats_2357_);
    lean_inc(v_openDecls_2356_);
    lean_inc(v_currNamespace_2355_);
    lean_inc(v_maxRecDepth_2353_);
    lean_inc(v_currRecDepth_2352_);
    lean_inc_ref(v_options_2351_);
    lean_inc_ref(v_fileMap_2350_);
    lean_inc_ref(v_fileName_2349_);
    v___x_2366_ = lean_alloc_ctor(0, 14, (2) as u32);
    lean_ctor_set(v___x_2366_, 0, v_fileName_2349_);
    lean_ctor_set(v___x_2366_, 1, v_fileMap_2350_);
    lean_ctor_set(v___x_2366_, 2, v_options_2351_);
    lean_ctor_set(v___x_2366_, 3, v_currRecDepth_2352_);
    lean_ctor_set(v___x_2366_, 4, v_maxRecDepth_2353_);
    lean_ctor_set(v___x_2366_, 5, v_ref_2365_);
    lean_ctor_set(v___x_2366_, 6, v_currNamespace_2355_);
    lean_ctor_set(v___x_2366_, 7, v_openDecls_2356_);
    lean_ctor_set(v___x_2366_, 8, v_initHeartbeats_2357_);
    lean_ctor_set(v___x_2366_, 9, v_maxHeartbeats_2358_);
    lean_ctor_set(v___x_2366_, 10, v_quotContext_2359_);
    lean_ctor_set(v___x_2366_, 11, v_currMacroScope_2360_);
    lean_ctor_set(v___x_2366_, 12, v_cancelTk_x3f_2362_);
    lean_ctor_set(v___x_2366_, 13, v_inheritedTraceOptions_2364_);
    lean_ctor_set_uint8(
        v___x_2366_,
        (core::mem::size_of::<*mut LeanObject>() * 14) as u32,
        v_diag_2361_,
    );
    lean_ctor_set_uint8(
        v___x_2366_,
        (core::mem::size_of::<*mut LeanObject>() * 14 + 1) as u32,
        v_suppressElabErrors_2363_,
    );
    v___x_2367_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Meta_Grind_casesMatch_spec__0_spec__0_spec__2_spec__7_spec__10_spec__13_spec__17___redArg(v_msg_2343_, v___y_2344_, v___y_2345_, v___x_2366_, v___y_2347_);
    lean_dec_ref_known(v___x_2366_, 14);
    return v___x_2367_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Meta_Grind_casesMatch_spec__0_spec__0_spec__2_spec__7_spec__10_spec__13___redArg___boxed(
    mut v_ref_2368_: *mut LeanObject,
    mut v_msg_2369_: *mut LeanObject,
    mut v___y_2370_: *mut LeanObject,
    mut v___y_2371_: *mut LeanObject,
    mut v___y_2372_: *mut LeanObject,
    mut v___y_2373_: *mut LeanObject,
    mut v___y_2374_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2375_: *mut LeanObject = core::ptr::null_mut();
    v_res_2375_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Meta_Grind_casesMatch_spec__0_spec__0_spec__2_spec__7_spec__10_spec__13___redArg(v_ref_2368_, v_msg_2369_, v___y_2370_, v___y_2371_, v___y_2372_, v___y_2373_);
    lean_dec(v___y_2373_);
    lean_dec_ref(v___y_2372_);
    lean_dec(v___y_2371_);
    lean_dec_ref(v___y_2370_);
    lean_dec(v_ref_2368_);
    return v_res_2375_;
}
pub unsafe fn l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Meta_Grind_casesMatch_spec__0_spec__0_spec__2_spec__7_spec__10___redArg(
    mut v_ref_2376_: *mut LeanObject,
    mut v_msg_2377_: *mut LeanObject,
    mut v_declHint_2378_: *mut LeanObject,
    mut v___y_2379_: *mut LeanObject,
    mut v___y_2380_: *mut LeanObject,
    mut v___y_2381_: *mut LeanObject,
    mut v___y_2382_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2384_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2385_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2386_: *mut LeanObject = core::ptr::null_mut();
    v___x_2384_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Meta_Grind_casesMatch_spec__0_spec__0_spec__2_spec__7_spec__10_spec__12(v_msg_2377_, v_declHint_2378_, v___y_2379_, v___y_2380_, v___y_2381_, v___y_2382_);
    v_a_2385_ = lean_ctor_get(v___x_2384_, 0);
    lean_inc(v_a_2385_);
    lean_dec_ref(v___x_2384_);
    v___x_2386_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Meta_Grind_casesMatch_spec__0_spec__0_spec__2_spec__7_spec__10_spec__13___redArg(v_ref_2376_, v_a_2385_, v___y_2379_, v___y_2380_, v___y_2381_, v___y_2382_);
    return v___x_2386_;
}
pub unsafe fn l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Meta_Grind_casesMatch_spec__0_spec__0_spec__2_spec__7_spec__10___redArg___boxed(
    mut v_ref_2387_: *mut LeanObject,
    mut v_msg_2388_: *mut LeanObject,
    mut v_declHint_2389_: *mut LeanObject,
    mut v___y_2390_: *mut LeanObject,
    mut v___y_2391_: *mut LeanObject,
    mut v___y_2392_: *mut LeanObject,
    mut v___y_2393_: *mut LeanObject,
    mut v___y_2394_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2395_: *mut LeanObject = core::ptr::null_mut();
    v_res_2395_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Meta_Grind_casesMatch_spec__0_spec__0_spec__2_spec__7_spec__10___redArg(v_ref_2387_, v_msg_2388_, v_declHint_2389_, v___y_2390_, v___y_2391_, v___y_2392_, v___y_2393_);
    lean_dec(v___y_2393_);
    lean_dec_ref(v___y_2392_);
    lean_dec(v___y_2391_);
    lean_dec_ref(v___y_2390_);
    lean_dec(v_ref_2387_);
    return v_res_2395_;
}
pub unsafe fn _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Meta_Grind_casesMatch_spec__0_spec__0_spec__2_spec__7___redArg___closed__1()
-> *mut LeanObject {
    let mut v___x_2397_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2398_: *mut LeanObject = core::ptr::null_mut();
    v___x_2397_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Meta_Grind_casesMatch_spec__0_spec__0_spec__2_spec__7___redArg___closed__0;
    v___x_2398_ = l_Lean_stringToMessageData(v___x_2397_);
    return v___x_2398_;
}
pub unsafe fn _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Meta_Grind_casesMatch_spec__0_spec__0_spec__2_spec__7___redArg___closed__3()
-> *mut LeanObject {
    let mut v___x_2400_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2401_: *mut LeanObject = core::ptr::null_mut();
    v___x_2400_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Meta_Grind_casesMatch_spec__0_spec__0_spec__2_spec__7___redArg___closed__2;
    v___x_2401_ = l_Lean_stringToMessageData(v___x_2400_);
    return v___x_2401_;
}
pub unsafe fn l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Meta_Grind_casesMatch_spec__0_spec__0_spec__2_spec__7___redArg(
    mut v_ref_2402_: *mut LeanObject,
    mut v_constName_2403_: *mut LeanObject,
    mut v___y_2404_: *mut LeanObject,
    mut v___y_2405_: *mut LeanObject,
    mut v___y_2406_: *mut LeanObject,
    mut v___y_2407_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2409_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2410_: u8 = 0;
    let mut v___x_2411_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2412_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2413_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2414_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2415_: *mut LeanObject = core::ptr::null_mut();
    v___x_2409_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Meta_Grind_casesMatch_spec__0_spec__0_spec__2_spec__7___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Meta_Grind_casesMatch_spec__0_spec__0_spec__2_spec__7___redArg___closed__1_once), _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Meta_Grind_casesMatch_spec__0_spec__0_spec__2_spec__7___redArg___closed__1);
    v___x_2410_ = 0;
    lean_inc(v_constName_2403_);
    v___x_2411_ = l_Lean_MessageData_ofConstName(v_constName_2403_, v___x_2410_);
    v___x_2412_ = lean_alloc_ctor(7, 2, (0) as u32);
    lean_ctor_set(v___x_2412_, 0, v___x_2409_);
    lean_ctor_set(v___x_2412_, 1, v___x_2411_);
    v___x_2413_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Meta_Grind_casesMatch_spec__0_spec__0_spec__2_spec__7___redArg___closed__3), core::ptr::addr_of_mut!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Meta_Grind_casesMatch_spec__0_spec__0_spec__2_spec__7___redArg___closed__3_once), _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Meta_Grind_casesMatch_spec__0_spec__0_spec__2_spec__7___redArg___closed__3);
    v___x_2414_ = lean_alloc_ctor(7, 2, (0) as u32);
    lean_ctor_set(v___x_2414_, 0, v___x_2412_);
    lean_ctor_set(v___x_2414_, 1, v___x_2413_);
    v___x_2415_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Meta_Grind_casesMatch_spec__0_spec__0_spec__2_spec__7_spec__10___redArg(v_ref_2402_, v___x_2414_, v_constName_2403_, v___y_2404_, v___y_2405_, v___y_2406_, v___y_2407_);
    return v___x_2415_;
}
pub unsafe fn l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Meta_Grind_casesMatch_spec__0_spec__0_spec__2_spec__7___redArg___boxed(
    mut v_ref_2416_: *mut LeanObject,
    mut v_constName_2417_: *mut LeanObject,
    mut v___y_2418_: *mut LeanObject,
    mut v___y_2419_: *mut LeanObject,
    mut v___y_2420_: *mut LeanObject,
    mut v___y_2421_: *mut LeanObject,
    mut v___y_2422_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2423_: *mut LeanObject = core::ptr::null_mut();
    v_res_2423_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Meta_Grind_casesMatch_spec__0_spec__0_spec__2_spec__7___redArg(v_ref_2416_, v_constName_2417_, v___y_2418_, v___y_2419_, v___y_2420_, v___y_2421_);
    lean_dec(v___y_2421_);
    lean_dec_ref(v___y_2420_);
    lean_dec(v___y_2419_);
    lean_dec_ref(v___y_2418_);
    lean_dec(v_ref_2416_);
    return v_res_2423_;
}
pub unsafe fn l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Meta_Grind_casesMatch_spec__0_spec__0_spec__2___redArg(
    mut v_constName_2424_: *mut LeanObject,
    mut v___y_2425_: *mut LeanObject,
    mut v___y_2426_: *mut LeanObject,
    mut v___y_2427_: *mut LeanObject,
    mut v___y_2428_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_ref_2430_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2431_: *mut LeanObject = core::ptr::null_mut();
    v_ref_2430_ = lean_ctor_get(v___y_2427_, 5);
    v___x_2431_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Meta_Grind_casesMatch_spec__0_spec__0_spec__2_spec__7___redArg(v_ref_2430_, v_constName_2424_, v___y_2425_, v___y_2426_, v___y_2427_, v___y_2428_);
    return v___x_2431_;
}
pub unsafe fn l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Meta_Grind_casesMatch_spec__0_spec__0_spec__2___redArg___boxed(
    mut v_constName_2432_: *mut LeanObject,
    mut v___y_2433_: *mut LeanObject,
    mut v___y_2434_: *mut LeanObject,
    mut v___y_2435_: *mut LeanObject,
    mut v___y_2436_: *mut LeanObject,
    mut v___y_2437_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2438_: *mut LeanObject = core::ptr::null_mut();
    v_res_2438_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Meta_Grind_casesMatch_spec__0_spec__0_spec__2___redArg(v_constName_2432_, v___y_2433_, v___y_2434_, v___y_2435_, v___y_2436_);
    lean_dec(v___y_2436_);
    lean_dec_ref(v___y_2435_);
    lean_dec(v___y_2434_);
    lean_dec_ref(v___y_2433_);
    return v_res_2438_;
}
pub unsafe fn l_Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Meta_Grind_casesMatch_spec__0_spec__0(
    mut v_constName_2439_: *mut LeanObject,
    mut v___y_2440_: *mut LeanObject,
    mut v___y_2441_: *mut LeanObject,
    mut v___y_2442_: *mut LeanObject,
    mut v___y_2443_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2445_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_2446_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2447_: u8 = 0;
    let mut v___x_2448_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2449_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_2450_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2452_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2453_: u8 = 0;
    let mut v___x_2455_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2456_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2457_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2445_ = lean_st_ref_get(v___y_2443_);
                v_env_2446_ = lean_ctor_get(v___x_2445_, 0);
                lean_inc_ref(v_env_2446_);
                lean_dec(v___x_2445_);
                v___x_2447_ = 0;
                lean_inc(v_constName_2439_);
                v___x_2448_ =
                    l_Lean_Environment_find_x3f(v_env_2446_, v_constName_2439_, v___x_2447_);
                if lean_obj_tag(v___x_2448_) == 0 {
                    v___x_2449_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Meta_Grind_casesMatch_spec__0_spec__0_spec__2___redArg(v_constName_2439_, v___y_2440_, v___y_2441_, v___y_2442_, v___y_2443_);
                    return v___x_2449_;
                } else {
                    lean_dec(v_constName_2439_);
                    v_val_2450_ = lean_ctor_get(v___x_2448_, 0);
                    v_isSharedCheck_2457_ = (!lean_is_exclusive(v___x_2448_)) as u8;
                    if v_isSharedCheck_2457_ == 0 {
                        v___x_2452_ = v___x_2448_;
                        v_isShared_2453_ = v_isSharedCheck_2457_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_val_2450_);
                        lean_dec(v___x_2448_);
                        v___x_2452_ = lean_box(0);
                        v_isShared_2453_ = v_isSharedCheck_2457_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_2453_ == 0 {
                    lean_ctor_set_tag(v___x_2452_, 0);
                    v___x_2455_ = v___x_2452_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2456_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2456_, 0, v_val_2450_);
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
    mut v_constName_2458_: *mut LeanObject,
    mut v___y_2459_: *mut LeanObject,
    mut v___y_2460_: *mut LeanObject,
    mut v___y_2461_: *mut LeanObject,
    mut v___y_2462_: *mut LeanObject,
    mut v___y_2463_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2464_: *mut LeanObject = core::ptr::null_mut();
    v_res_2464_ = l_Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Meta_Grind_casesMatch_spec__0_spec__0(v_constName_2458_, v___y_2459_, v___y_2460_, v___y_2461_, v___y_2462_);
    lean_dec(v___y_2462_);
    lean_dec_ref(v___y_2461_);
    lean_dec(v___y_2460_);
    lean_dec_ref(v___y_2459_);
    return v_res_2464_;
}
pub unsafe fn l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Meta_Grind_casesMatch_spec__0_spec__2___redArg(
    mut v_declName_2465_: *mut LeanObject,
    mut v___y_2466_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2468_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_2469_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2470_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2471_: *mut LeanObject = core::ptr::null_mut();
    v___x_2468_ = lean_st_ref_get(v___y_2466_);
    v_env_2469_ = lean_ctor_get(v___x_2468_, 0);
    lean_inc_ref(v_env_2469_);
    lean_dec(v___x_2468_);
    v___x_2470_ = l_Lean_Meta_Match_Extension_getMatcherInfo_x3f(v_env_2469_, v_declName_2465_);
    v___x_2471_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_2471_, 0, v___x_2470_);
    return v___x_2471_;
}
pub unsafe fn l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Meta_Grind_casesMatch_spec__0_spec__2___redArg___boxed(
    mut v_declName_2472_: *mut LeanObject,
    mut v___y_2473_: *mut LeanObject,
    mut v___y_2474_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2475_: *mut LeanObject = core::ptr::null_mut();
    v_res_2475_ = l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Meta_Grind_casesMatch_spec__0_spec__2___redArg(v_declName_2472_, v___y_2473_);
    lean_dec(v___y_2473_);
    return v_res_2475_;
}
pub unsafe fn _init_l_panic___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Meta_Grind_casesMatch_spec__0_spec__1___closed__0()
-> *mut LeanObject {
    let mut v___x_2476_: *mut LeanObject = core::ptr::null_mut();
    v___x_2476_ = l_instMonadEIO(lean_box(0));
    return v___x_2476_;
}
pub unsafe fn l_panic___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Meta_Grind_casesMatch_spec__0_spec__1(
    mut v_msg_2481_: *mut LeanObject,
    mut v___y_2482_: *mut LeanObject,
    mut v___y_2483_: *mut LeanObject,
    mut v___y_2484_: *mut LeanObject,
    mut v___y_2485_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2487_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2488_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toApplicative_2489_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2491_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2492_: u8 = 0;
    let mut v_toFunctor_2493_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toSeq_2494_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toSeqLeft_2495_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toSeqRight_2496_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2498_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2499_: u8 = 0;
    let mut v___f_2500_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2501_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2502_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2503_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2504_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2505_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2506_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2507_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2509_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2511_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2512_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toApplicative_2513_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2515_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2516_: u8 = 0;
    let mut v_toFunctor_2517_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toSeq_2518_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toSeqLeft_2519_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toSeqRight_2520_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2522_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2523_: u8 = 0;
    let mut v___f_2524_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2525_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2526_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2527_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2528_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2529_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2530_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2531_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2533_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2535_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2536_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2537_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4013__overap_2538_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2539_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2540_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2541_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2542_: u8 = 0;
    let mut v_unused_2543_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2544_: u8 = 0;
    let mut v_unused_2545_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2546_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2547_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2548_: u8 = 0;
    let mut v_unused_2549_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2550_: u8 = 0;
    let mut v_unused_2551_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2487_ = lean_obj_once(core::ptr::addr_of_mut!(l_panic___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Meta_Grind_casesMatch_spec__0_spec__1___closed__0), core::ptr::addr_of_mut!(l_panic___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Meta_Grind_casesMatch_spec__0_spec__1___closed__0_once), _init_l_panic___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Meta_Grind_casesMatch_spec__0_spec__1___closed__0);
                v___x_2488_ = l_StateRefT_x27_instMonad___redArg(v___x_2487_);
                v_toApplicative_2489_ = lean_ctor_get(v___x_2488_, 0);
                v_isSharedCheck_2550_ = (!lean_is_exclusive(v___x_2488_)) as u8;
                if v_isSharedCheck_2550_ == 0 {
                    v_unused_2551_ = lean_ctor_get(v___x_2488_, 1);
                    lean_dec(v_unused_2551_);
                    v___x_2491_ = v___x_2488_;
                    v_isShared_2492_ = v_isSharedCheck_2550_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_toApplicative_2489_);
                    lean_dec(v___x_2488_);
                    v___x_2491_ = lean_box(0);
                    v_isShared_2492_ = v_isSharedCheck_2550_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_toFunctor_2493_ = lean_ctor_get(v_toApplicative_2489_, 0);
                v_toSeq_2494_ = lean_ctor_get(v_toApplicative_2489_, 2);
                v_toSeqLeft_2495_ = lean_ctor_get(v_toApplicative_2489_, 3);
                v_toSeqRight_2496_ = lean_ctor_get(v_toApplicative_2489_, 4);
                v_isSharedCheck_2548_ = (!lean_is_exclusive(v_toApplicative_2489_)) as u8;
                if v_isSharedCheck_2548_ == 0 {
                    v_unused_2549_ = lean_ctor_get(v_toApplicative_2489_, 1);
                    lean_dec(v_unused_2549_);
                    v___x_2498_ = v_toApplicative_2489_;
                    v_isShared_2499_ = v_isSharedCheck_2548_;
                    state = 2;
                    continue;
                } else {
                    lean_inc(v_toSeqRight_2496_);
                    lean_inc(v_toSeqLeft_2495_);
                    lean_inc(v_toSeq_2494_);
                    lean_inc(v_toFunctor_2493_);
                    lean_dec(v_toApplicative_2489_);
                    v___x_2498_ = lean_box(0);
                    v_isShared_2499_ = v_isSharedCheck_2548_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___f_2500_ = l_panic___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Meta_Grind_casesMatch_spec__0_spec__1___closed__1;
                v___f_2501_ = l_panic___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Meta_Grind_casesMatch_spec__0_spec__1___closed__2;
                lean_inc_ref(v_toFunctor_2493_);
                v___f_2502_ = lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__0 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                lean_closure_set(v___f_2502_, 0, v_toFunctor_2493_);
                v___f_2503_ = lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                lean_closure_set(v___f_2503_, 0, v_toFunctor_2493_);
                v___x_2504_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_2504_, 0, v___f_2502_);
                lean_ctor_set(v___x_2504_, 1, v___f_2503_);
                v___f_2505_ = lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                lean_closure_set(v___f_2505_, 0, v_toSeqRight_2496_);
                v___f_2506_ = lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__3 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                lean_closure_set(v___f_2506_, 0, v_toSeqLeft_2495_);
                v___f_2507_ = lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__4 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                lean_closure_set(v___f_2507_, 0, v_toSeq_2494_);
                if v_isShared_2499_ == 0 {
                    lean_ctor_set(v___x_2498_, 4, v___f_2505_);
                    lean_ctor_set(v___x_2498_, 3, v___f_2506_);
                    lean_ctor_set(v___x_2498_, 2, v___f_2507_);
                    lean_ctor_set(v___x_2498_, 1, v___f_2500_);
                    lean_ctor_set(v___x_2498_, 0, v___x_2504_);
                    v___x_2509_ = v___x_2498_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2547_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2547_, 0, v___x_2504_);
                    lean_ctor_set(v_reuseFailAlloc_2547_, 1, v___f_2500_);
                    lean_ctor_set(v_reuseFailAlloc_2547_, 2, v___f_2507_);
                    lean_ctor_set(v_reuseFailAlloc_2547_, 3, v___f_2506_);
                    lean_ctor_set(v_reuseFailAlloc_2547_, 4, v___f_2505_);
                    v___x_2509_ = v_reuseFailAlloc_2547_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_2492_ == 0 {
                    lean_ctor_set(v___x_2491_, 1, v___f_2501_);
                    lean_ctor_set(v___x_2491_, 0, v___x_2509_);
                    v___x_2511_ = v___x_2491_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2546_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2546_, 0, v___x_2509_);
                    lean_ctor_set(v_reuseFailAlloc_2546_, 1, v___f_2501_);
                    v___x_2511_ = v_reuseFailAlloc_2546_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_2512_ = l_StateRefT_x27_instMonad___redArg(v___x_2511_);
                v_toApplicative_2513_ = lean_ctor_get(v___x_2512_, 0);
                v_isSharedCheck_2544_ = (!lean_is_exclusive(v___x_2512_)) as u8;
                if v_isSharedCheck_2544_ == 0 {
                    v_unused_2545_ = lean_ctor_get(v___x_2512_, 1);
                    lean_dec(v_unused_2545_);
                    v___x_2515_ = v___x_2512_;
                    v_isShared_2516_ = v_isSharedCheck_2544_;
                    state = 5;
                    continue;
                } else {
                    lean_inc(v_toApplicative_2513_);
                    lean_dec(v___x_2512_);
                    v___x_2515_ = lean_box(0);
                    v_isShared_2516_ = v_isSharedCheck_2544_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v_toFunctor_2517_ = lean_ctor_get(v_toApplicative_2513_, 0);
                v_toSeq_2518_ = lean_ctor_get(v_toApplicative_2513_, 2);
                v_toSeqLeft_2519_ = lean_ctor_get(v_toApplicative_2513_, 3);
                v_toSeqRight_2520_ = lean_ctor_get(v_toApplicative_2513_, 4);
                v_isSharedCheck_2542_ = (!lean_is_exclusive(v_toApplicative_2513_)) as u8;
                if v_isSharedCheck_2542_ == 0 {
                    v_unused_2543_ = lean_ctor_get(v_toApplicative_2513_, 1);
                    lean_dec(v_unused_2543_);
                    v___x_2522_ = v_toApplicative_2513_;
                    v_isShared_2523_ = v_isSharedCheck_2542_;
                    state = 6;
                    continue;
                } else {
                    lean_inc(v_toSeqRight_2520_);
                    lean_inc(v_toSeqLeft_2519_);
                    lean_inc(v_toSeq_2518_);
                    lean_inc(v_toFunctor_2517_);
                    lean_dec(v_toApplicative_2513_);
                    v___x_2522_ = lean_box(0);
                    v_isShared_2523_ = v_isSharedCheck_2542_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                v___f_2524_ = l_panic___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Meta_Grind_casesMatch_spec__0_spec__1___closed__3;
                v___f_2525_ = l_panic___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Meta_Grind_casesMatch_spec__0_spec__1___closed__4;
                lean_inc_ref(v_toFunctor_2517_);
                v___f_2526_ = lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__0 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                lean_closure_set(v___f_2526_, 0, v_toFunctor_2517_);
                v___f_2527_ = lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                lean_closure_set(v___f_2527_, 0, v_toFunctor_2517_);
                v___x_2528_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_2528_, 0, v___f_2526_);
                lean_ctor_set(v___x_2528_, 1, v___f_2527_);
                v___f_2529_ = lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                lean_closure_set(v___f_2529_, 0, v_toSeqRight_2520_);
                v___f_2530_ = lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__3 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                lean_closure_set(v___f_2530_, 0, v_toSeqLeft_2519_);
                v___f_2531_ = lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__4 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                lean_closure_set(v___f_2531_, 0, v_toSeq_2518_);
                if v_isShared_2523_ == 0 {
                    lean_ctor_set(v___x_2522_, 4, v___f_2529_);
                    lean_ctor_set(v___x_2522_, 3, v___f_2530_);
                    lean_ctor_set(v___x_2522_, 2, v___f_2531_);
                    lean_ctor_set(v___x_2522_, 1, v___f_2524_);
                    lean_ctor_set(v___x_2522_, 0, v___x_2528_);
                    v___x_2533_ = v___x_2522_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_2541_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2541_, 0, v___x_2528_);
                    lean_ctor_set(v_reuseFailAlloc_2541_, 1, v___f_2524_);
                    lean_ctor_set(v_reuseFailAlloc_2541_, 2, v___f_2531_);
                    lean_ctor_set(v_reuseFailAlloc_2541_, 3, v___f_2530_);
                    lean_ctor_set(v_reuseFailAlloc_2541_, 4, v___f_2529_);
                    v___x_2533_ = v_reuseFailAlloc_2541_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                if v_isShared_2516_ == 0 {
                    lean_ctor_set(v___x_2515_, 1, v___f_2525_);
                    lean_ctor_set(v___x_2515_, 0, v___x_2533_);
                    v___x_2535_ = v___x_2515_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_2540_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2540_, 0, v___x_2533_);
                    lean_ctor_set(v_reuseFailAlloc_2540_, 1, v___f_2525_);
                    v___x_2535_ = v_reuseFailAlloc_2540_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                v___x_2536_ = l_Lean_Meta_Match_instInhabitedAltParamInfo_default;
                v___x_2537_ = l_instInhabitedOfMonad___redArg(v___x_2535_, v___x_2536_);
                v___x_4013__overap_2538_ = lean_panic_fn_borrowed(v___x_2537_, v_msg_2481_);
                lean_dec(v___x_2537_);
                lean_inc(v___y_2485_);
                lean_inc_ref(v___y_2484_);
                lean_inc(v___y_2483_);
                lean_inc_ref(v___y_2482_);
                v___x_2539_ = lean_apply_5(
                    v___x_4013__overap_2538_,
                    v___y_2482_,
                    v___y_2483_,
                    v___y_2484_,
                    v___y_2485_,
                    lean_box(0),
                );
                return v___x_2539_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_panic___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Meta_Grind_casesMatch_spec__0_spec__1___boxed(
    mut v_msg_2552_: *mut LeanObject,
    mut v___y_2553_: *mut LeanObject,
    mut v___y_2554_: *mut LeanObject,
    mut v___y_2555_: *mut LeanObject,
    mut v___y_2556_: *mut LeanObject,
    mut v___y_2557_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2558_: *mut LeanObject = core::ptr::null_mut();
    v_res_2558_ = l_panic___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Meta_Grind_casesMatch_spec__0_spec__1(v_msg_2552_, v___y_2553_, v___y_2554_, v___y_2555_, v___y_2556_);
    lean_dec(v___y_2556_);
    lean_dec_ref(v___y_2555_);
    lean_dec(v___y_2554_);
    lean_dec_ref(v___y_2553_);
    return v_res_2558_;
}
pub unsafe fn _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Meta_Grind_casesMatch_spec__0_spec__3___closed__3()
-> *mut LeanObject {
    let mut v___x_2562_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2563_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2564_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2565_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2566_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2567_: *mut LeanObject = core::ptr::null_mut();
    v___x_2562_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Meta_Grind_casesMatch_spec__0_spec__3___closed__2;
    v___x_2563_ = lean_unsigned_to_nat(53);
    v___x_2564_ = lean_unsigned_to_nat(62);
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
    mut v_bs_2570_: *mut LeanObject,
    mut v___y_2571_: *mut LeanObject,
    mut v___y_2572_: *mut LeanObject,
    mut v___y_2573_: *mut LeanObject,
    mut v___y_2574_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2576_: u8 = 0;
    let mut v___x_2577_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_2578_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2579_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2580_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2581_: *mut LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_2582_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2584_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2585_: usize = 0;
    let mut v___x_2586_: usize = 0;
    let mut v___x_2587_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_2589_: *mut LeanObject = core::ptr::null_mut();
    let mut v_numFields_2590_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2591_: u8 = 0;
    let mut v___x_2592_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2593_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2594_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2595_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2596_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2598_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2599_: u8 = 0;
    let mut v___x_2601_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2602_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2603_: u8 = 0;
    let mut v_a_2604_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2606_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2607_: u8 = 0;
    let mut v___x_2609_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2610_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2611_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2576_ = lean_usize_dec_lt(v_i_2569_, v_sz_2568_);
                if v___x_2576_ == 0 {
                    v___x_2577_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_2577_, 0, v_bs_2570_);
                    return v___x_2577_;
                } else {
                    v_v_2578_ = lean_array_uget_borrowed(v_bs_2570_, v_i_2569_);
                    lean_inc(v_v_2578_);
                    v___x_2579_ = l_Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Meta_Grind_casesMatch_spec__0_spec__0(v_v_2578_, v___y_2571_, v___y_2572_, v___y_2573_, v___y_2574_);
                    if lean_obj_tag(v___x_2579_) == 0 {
                        v_a_2580_ = lean_ctor_get(v___x_2579_, 0);
                        lean_inc(v_a_2580_);
                        lean_dec_ref_known(v___x_2579_, 1);
                        v___x_2581_ = lean_unsigned_to_nat(0);
                        v_bs_x27_2582_ = lean_array_uset(v_bs_2570_, v_i_2569_, v___x_2581_);
                        if lean_obj_tag(v_a_2580_) == 6 {
                            v_val_2589_ = lean_ctor_get(v_a_2580_, 0);
                            lean_inc_ref(v_val_2589_);
                            lean_dec_ref_known(v_a_2580_, 1);
                            v_numFields_2590_ = lean_ctor_get(v_val_2589_, 4);
                            lean_inc(v_numFields_2590_);
                            lean_dec_ref(v_val_2589_);
                            v___x_2591_ = 0;
                            v___x_2592_ = lean_alloc_ctor(0, 2, (1) as u32);
                            lean_ctor_set(v___x_2592_, 0, v_numFields_2590_);
                            lean_ctor_set(v___x_2592_, 1, v___x_2581_);
                            lean_ctor_set_uint8(
                                v___x_2592_,
                                (core::mem::size_of::<*mut LeanObject>() * 2) as u32,
                                v___x_2591_,
                            );
                            v_a_2584_ = v___x_2592_;
                            state = 1;
                            continue;
                        } else {
                            lean_dec(v_a_2580_);
                            v___x_2593_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Meta_Grind_casesMatch_spec__0_spec__3___closed__3), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Meta_Grind_casesMatch_spec__0_spec__3___closed__3_once), _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Meta_Grind_casesMatch_spec__0_spec__3___closed__3);
                            v___x_2594_ = l_panic___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Meta_Grind_casesMatch_spec__0_spec__1(v___x_2593_, v___y_2571_, v___y_2572_, v___y_2573_, v___y_2574_);
                            if lean_obj_tag(v___x_2594_) == 0 {
                                v_a_2595_ = lean_ctor_get(v___x_2594_, 0);
                                lean_inc(v_a_2595_);
                                lean_dec_ref_known(v___x_2594_, 1);
                                v_a_2584_ = v_a_2595_;
                                state = 1;
                                continue;
                            } else {
                                lean_dec_ref(v_bs_x27_2582_);
                                v_a_2596_ = lean_ctor_get(v___x_2594_, 0);
                                v_isSharedCheck_2603_ = (!lean_is_exclusive(v___x_2594_)) as u8;
                                if v_isSharedCheck_2603_ == 0 {
                                    v___x_2598_ = v___x_2594_;
                                    v_isShared_2599_ = v_isSharedCheck_2603_;
                                    state = 2;
                                    continue;
                                } else {
                                    lean_inc(v_a_2596_);
                                    lean_dec(v___x_2594_);
                                    v___x_2598_ = lean_box(0);
                                    v_isShared_2599_ = v_isSharedCheck_2603_;
                                    state = 2;
                                    continue;
                                }
                            }
                        }
                    } else {
                        lean_dec_ref(v_bs_2570_);
                        v_a_2604_ = lean_ctor_get(v___x_2579_, 0);
                        v_isSharedCheck_2611_ = (!lean_is_exclusive(v___x_2579_)) as u8;
                        if v_isSharedCheck_2611_ == 0 {
                            v___x_2606_ = v___x_2579_;
                            v_isShared_2607_ = v_isSharedCheck_2611_;
                            state = 4;
                            continue;
                        } else {
                            lean_inc(v_a_2604_);
                            lean_dec(v___x_2579_);
                            v___x_2606_ = lean_box(0);
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
                    v_reuseFailAlloc_2602_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2602_, 0, v_a_2596_);
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
                    v_reuseFailAlloc_2610_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2610_, 0, v_a_2604_);
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
    mut v_sz_2612_: *mut LeanObject,
    mut v_i_2613_: *mut LeanObject,
    mut v_bs_2614_: *mut LeanObject,
    mut v___y_2615_: *mut LeanObject,
    mut v___y_2616_: *mut LeanObject,
    mut v___y_2617_: *mut LeanObject,
    mut v___y_2618_: *mut LeanObject,
    mut v___y_2619_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_boxed_2620_: usize = 0;
    let mut v_i_boxed_2621_: usize = 0;
    let mut v_res_2622_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_2620_ = lean_unbox_usize(v_sz_2612_);
    lean_dec(v_sz_2612_);
    v_i_boxed_2621_ = lean_unbox_usize(v_i_2613_);
    lean_dec(v_i_2613_);
    v_res_2622_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Meta_Grind_casesMatch_spec__0_spec__3(v_sz_boxed_2620_, v_i_boxed_2621_, v_bs_2614_, v___y_2615_, v___y_2616_, v___y_2617_, v___y_2618_);
    lean_dec(v___y_2618_);
    lean_dec_ref(v___y_2617_);
    lean_dec(v___y_2616_);
    lean_dec_ref(v___y_2615_);
    return v_res_2622_;
}
pub unsafe fn _init_l_Lean_Meta_matchMatcherApp_x3f___at___00Lean_Meta_Grind_casesMatch_spec__0___closed__0()
-> *mut LeanObject {
    let mut v___x_2623_: *mut LeanObject = core::ptr::null_mut();
    let mut v_dummy_2624_: *mut LeanObject = core::ptr::null_mut();
    v___x_2623_ = lean_box(0);
    v_dummy_2624_ = l_Lean_Expr_sort___override(v___x_2623_);
    return v_dummy_2624_;
}
pub unsafe fn _init_l_Lean_Meta_matchMatcherApp_x3f___at___00Lean_Meta_Grind_casesMatch_spec__0___closed__1()
-> *mut LeanObject {
    let mut v___x_2625_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2626_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2627_: *mut LeanObject = core::ptr::null_mut();
    v___x_2625_ = lean_box(0);
    v___x_2626_ = lean_unsigned_to_nat(16);
    v___x_2627_ = lean_mk_array(v___x_2626_, v___x_2625_);
    return v___x_2627_;
}
pub unsafe fn _init_l_Lean_Meta_matchMatcherApp_x3f___at___00Lean_Meta_Grind_casesMatch_spec__0___closed__2()
-> *mut LeanObject {
    let mut v___x_2628_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2629_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2630_: *mut LeanObject = core::ptr::null_mut();
    v___x_2628_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Meta_matchMatcherApp_x3f___at___00Lean_Meta_Grind_casesMatch_spec__0___closed__1), core::ptr::addr_of_mut!(l_Lean_Meta_matchMatcherApp_x3f___at___00Lean_Meta_Grind_casesMatch_spec__0___closed__1_once), _init_l_Lean_Meta_matchMatcherApp_x3f___at___00Lean_Meta_Grind_casesMatch_spec__0___closed__1);
    v___x_2629_ = lean_unsigned_to_nat(0);
    v___x_2630_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_2630_, 0, v___x_2629_);
    lean_ctor_set(v___x_2630_, 1, v___x_2628_);
    return v___x_2630_;
}
pub unsafe fn l_Lean_Meta_matchMatcherApp_x3f___at___00Lean_Meta_Grind_casesMatch_spec__0(
    mut v_e_2633_: *mut LeanObject,
    mut v_alsoCasesOn_2634_: u8,
    mut v___y_2635_: *mut LeanObject,
    mut v___y_2636_: *mut LeanObject,
    mut v___y_2637_: *mut LeanObject,
    mut v___y_2638_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2641_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2642_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2643_: u8 = 0;
    let mut v___x_2644_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2645_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2646_: *mut LeanObject = core::ptr::null_mut();
    let mut v_declName_2647_: *mut LeanObject = core::ptr::null_mut();
    let mut v_us_2648_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2649_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2650_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2652_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2653_: u8 = 0;
    let mut v_val_2654_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2656_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2657_: u8 = 0;
    let mut v_dummy_2658_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nargs_2659_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2660_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2661_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2662_: *mut LeanObject = core::ptr::null_mut();
    let mut v_args_2663_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2664_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2665_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2666_: u8 = 0;
    let mut v_numParams_2667_: *mut LeanObject = core::ptr::null_mut();
    let mut v_numDiscrs_2668_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2669_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2670_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2671_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2672_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2673_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2674_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2675_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2676_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2677_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2678_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2679_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2680_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2681_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2682_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2683_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2684_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2685_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2687_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2689_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2690_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2691_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2692_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2694_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2695_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2696_: u8 = 0;
    let mut v___x_2697_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_2698_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2699_: u8 = 0;
    let mut v_indName_2700_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2701_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2702_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2704_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2705_: u8 = 0;
    let mut v_val_2706_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2708_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2709_: u8 = 0;
    let mut v_toConstantVal_2710_: *mut LeanObject = core::ptr::null_mut();
    let mut v_numParams_2711_: *mut LeanObject = core::ptr::null_mut();
    let mut v_numIndices_2712_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ctors_2713_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nargs_2714_: *mut LeanObject = core::ptr::null_mut();
    let mut v_dummy_2715_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2716_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2717_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2718_: *mut LeanObject = core::ptr::null_mut();
    let mut v_args_2719_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2720_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2721_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2722_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2723_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2724_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2725_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2726_: u8 = 0;
    let mut v___x_2727_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2729_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2730_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2731_: *mut LeanObject = core::ptr::null_mut();
    let mut v_params_2732_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2733_: *mut LeanObject = core::ptr::null_mut();
    let mut v_motive_2734_: *mut LeanObject = core::ptr::null_mut();
    let mut v_discrs_2735_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2736_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2737_: *mut LeanObject = core::ptr::null_mut();
    let mut v_discrInfos_2738_: *mut LeanObject = core::ptr::null_mut();
    let mut v_alts_2739_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2741_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2742_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2743_: *mut LeanObject = core::ptr::null_mut();
    let mut v_sz_2744_: usize = 0;
    let mut v___x_2745_: usize = 0;
    let mut v___x_2746_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2747_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2749_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2750_: u8 = 0;
    let mut v_start_2751_: *mut LeanObject = core::ptr::null_mut();
    let mut v_stop_2752_: *mut LeanObject = core::ptr::null_mut();
    let mut v_start_2753_: *mut LeanObject = core::ptr::null_mut();
    let mut v_stop_2754_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2755_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2756_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2757_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2758_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2759_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2760_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2761_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2762_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2763_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2764_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2766_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2768_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2769_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2770_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2771_: u8 = 0;
    let mut v_a_2772_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2774_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2775_: u8 = 0;
    let mut v___x_2777_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2778_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2779_: u8 = 0;
    let mut v_lower_2781_: *mut LeanObject = core::ptr::null_mut();
    let mut v_upper_2782_: *mut LeanObject = core::ptr::null_mut();
    let mut v_levelParams_2783_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2784_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2785_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2786_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2787_: u8 = 0;
    let mut v___x_2788_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2789_: u8 = 0;
    let mut v_isSharedCheck_2790_: u8 = 0;
    let mut v___x_2791_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2793_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2794_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2795_: u8 = 0;
    let mut v_a_2796_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2798_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2799_: u8 = 0;
    let mut v___x_2801_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2802_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2803_: u8 = 0;
    let mut v_isSharedCheck_2804_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2643_ = l_Lean_Expr_isApp(v_e_2633_);
                if v___x_2643_ == 0 {
                    lean_dec_ref(v_e_2633_);
                    v___x_2644_ = lean_box(0);
                    v___x_2645_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_2645_, 0, v___x_2644_);
                    return v___x_2645_;
                } else {
                    v___x_2646_ = l_Lean_Expr_getAppFn(v_e_2633_);
                    if lean_obj_tag(v___x_2646_) == 4 {
                        v_declName_2647_ = lean_ctor_get(v___x_2646_, 0);
                        lean_inc_n(v_declName_2647_, 2);
                        v_us_2648_ = lean_ctor_get(v___x_2646_, 1);
                        lean_inc(v_us_2648_);
                        lean_dec_ref_known(v___x_2646_, 2);
                        v___x_2649_ = l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Meta_Grind_casesMatch_spec__0_spec__2___redArg(v_declName_2647_, v___y_2638_);
                        v_a_2650_ = lean_ctor_get(v___x_2649_, 0);
                        v_isSharedCheck_2804_ = (!lean_is_exclusive(v___x_2649_)) as u8;
                        if v_isSharedCheck_2804_ == 0 {
                            v___x_2652_ = v___x_2649_;
                            v_isShared_2653_ = v_isSharedCheck_2804_;
                            state = 2;
                            continue;
                        } else {
                            lean_inc(v_a_2650_);
                            lean_dec(v___x_2649_);
                            v___x_2652_ = lean_box(0);
                            v_isShared_2653_ = v_isSharedCheck_2804_;
                            state = 2;
                            continue;
                        }
                    } else {
                        lean_dec_ref(v___x_2646_);
                        lean_dec_ref(v_e_2633_);
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_2641_ = lean_box(0);
                v___x_2642_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_2642_, 0, v___x_2641_);
                return v___x_2642_;
            }
            2 => {
                if lean_obj_tag(v_a_2650_) == 1 {
                    v_val_2654_ = lean_ctor_get(v_a_2650_, 0);
                    v_isSharedCheck_2696_ = (!lean_is_exclusive(v_a_2650_)) as u8;
                    if v_isSharedCheck_2696_ == 0 {
                        v___x_2656_ = v_a_2650_;
                        v_isShared_2657_ = v_isSharedCheck_2696_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_val_2654_);
                        lean_dec(v_a_2650_);
                        v___x_2656_ = lean_box(0);
                        v_isShared_2657_ = v_isSharedCheck_2696_;
                        state = 3;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_2652_);
                    lean_dec(v_a_2650_);
                    v___x_2697_ = lean_st_ref_get(v___y_2638_);
                    if v_alsoCasesOn_2634_ == 0 {
                        lean_dec(v___x_2697_);
                        lean_dec(v_us_2648_);
                        lean_dec(v_declName_2647_);
                        lean_dec_ref(v_e_2633_);
                        state = 1;
                        continue;
                    } else {
                        v_env_2698_ = lean_ctor_get(v___x_2697_, 0);
                        lean_inc_ref(v_env_2698_);
                        lean_dec(v___x_2697_);
                        lean_inc(v_declName_2647_);
                        v___x_2699_ = l_Lean_isCasesOnRecursor(v_env_2698_, v_declName_2647_);
                        if v___x_2699_ == 0 {
                            lean_dec(v_us_2648_);
                            lean_dec(v_declName_2647_);
                            lean_dec_ref(v_e_2633_);
                            state = 1;
                            continue;
                        } else {
                            v_indName_2700_ = l_Lean_Name_getPrefix(v_declName_2647_);
                            v___x_2701_ = l_Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Meta_Grind_casesMatch_spec__0_spec__0(v_indName_2700_, v___y_2635_, v___y_2636_, v___y_2637_, v___y_2638_);
                            if lean_obj_tag(v___x_2701_) == 0 {
                                v_a_2702_ = lean_ctor_get(v___x_2701_, 0);
                                v_isSharedCheck_2795_ = (!lean_is_exclusive(v___x_2701_)) as u8;
                                if v_isSharedCheck_2795_ == 0 {
                                    v___x_2704_ = v___x_2701_;
                                    v_isShared_2705_ = v_isSharedCheck_2795_;
                                    state = 7;
                                    continue;
                                } else {
                                    lean_inc(v_a_2702_);
                                    lean_dec(v___x_2701_);
                                    v___x_2704_ = lean_box(0);
                                    v_isShared_2705_ = v_isSharedCheck_2795_;
                                    state = 7;
                                    continue;
                                }
                            } else {
                                lean_dec(v_us_2648_);
                                lean_dec(v_declName_2647_);
                                lean_dec_ref(v_e_2633_);
                                v_a_2796_ = lean_ctor_get(v___x_2701_, 0);
                                v_isSharedCheck_2803_ = (!lean_is_exclusive(v___x_2701_)) as u8;
                                if v_isSharedCheck_2803_ == 0 {
                                    v___x_2798_ = v___x_2701_;
                                    v_isShared_2799_ = v_isSharedCheck_2803_;
                                    state = 18;
                                    continue;
                                } else {
                                    lean_inc(v_a_2796_);
                                    lean_dec(v___x_2701_);
                                    v___x_2798_ = lean_box(0);
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
                v_dummy_2658_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Meta_matchMatcherApp_x3f___at___00Lean_Meta_Grind_casesMatch_spec__0___closed__0), core::ptr::addr_of_mut!(l_Lean_Meta_matchMatcherApp_x3f___at___00Lean_Meta_Grind_casesMatch_spec__0___closed__0_once), _init_l_Lean_Meta_matchMatcherApp_x3f___at___00Lean_Meta_Grind_casesMatch_spec__0___closed__0);
                v_nargs_2659_ = l_Lean_Expr_getAppNumArgs(v_e_2633_);
                lean_inc(v_nargs_2659_);
                v___x_2660_ = lean_mk_array(v_nargs_2659_, v_dummy_2658_);
                v___x_2661_ = lean_unsigned_to_nat(1);
                v___x_2662_ = lean_nat_sub(v_nargs_2659_, v___x_2661_);
                lean_dec(v_nargs_2659_);
                v_args_2663_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(
                    v_e_2633_,
                    v___x_2660_,
                    v___x_2662_,
                );
                v___x_2664_ = lean_array_get_size(v_args_2663_);
                v___x_2665_ = l_Lean_Meta_Match_MatcherInfo_arity(v_val_2654_);
                v___x_2666_ = lean_nat_dec_lt(v___x_2664_, v___x_2665_);
                lean_dec(v___x_2665_);
                if v___x_2666_ == 0 {
                    v_numParams_2667_ = lean_ctor_get(v_val_2654_, 0);
                    v_numDiscrs_2668_ = lean_ctor_get(v_val_2654_, 1);
                    v___x_2669_ = lean_array_mk(v_us_2648_);
                    v___x_2670_ = lean_unsigned_to_nat(0);
                    lean_inc(v_numParams_2667_);
                    v___x_2671_ =
                        l_Array_extract___redArg(v_args_2663_, v___x_2670_, v_numParams_2667_);
                    v___x_2672_ = l_Lean_instInhabitedExpr;
                    v___x_2673_ = l_Lean_Meta_Match_MatcherInfo_getMotivePos(v_val_2654_);
                    v___x_2674_ = lean_array_get(v___x_2672_, v_args_2663_, v___x_2673_);
                    lean_dec(v___x_2673_);
                    v___x_2675_ = lean_nat_add(v_numParams_2667_, v___x_2661_);
                    v___x_2676_ = lean_nat_add(v___x_2675_, v_numDiscrs_2668_);
                    lean_inc(v___x_2676_);
                    lean_inc_ref_n(v_args_2663_, 2);
                    v___x_2677_ =
                        l_Array_toSubarray___redArg(v_args_2663_, v___x_2675_, v___x_2676_);
                    v___x_2678_ = l_Subarray_copy___redArg(v___x_2677_);
                    v___x_2679_ = l_Lean_Meta_Match_MatcherInfo_numAlts(v_val_2654_);
                    v___x_2680_ = lean_nat_add(v___x_2676_, v___x_2679_);
                    lean_dec(v___x_2679_);
                    lean_inc(v___x_2680_);
                    v___x_2681_ =
                        l_Array_toSubarray___redArg(v_args_2663_, v___x_2676_, v___x_2680_);
                    v___x_2682_ = l_Subarray_copy___redArg(v___x_2681_);
                    v___x_2683_ =
                        l_Array_toSubarray___redArg(v_args_2663_, v___x_2680_, v___x_2664_);
                    v___x_2684_ = l_Subarray_copy___redArg(v___x_2683_);
                    v___x_2685_ = lean_alloc_ctor(0, 8, (0) as u32);
                    lean_ctor_set(v___x_2685_, 0, v_val_2654_);
                    lean_ctor_set(v___x_2685_, 1, v_declName_2647_);
                    lean_ctor_set(v___x_2685_, 2, v___x_2669_);
                    lean_ctor_set(v___x_2685_, 3, v___x_2671_);
                    lean_ctor_set(v___x_2685_, 4, v___x_2674_);
                    lean_ctor_set(v___x_2685_, 5, v___x_2678_);
                    lean_ctor_set(v___x_2685_, 6, v___x_2682_);
                    lean_ctor_set(v___x_2685_, 7, v___x_2684_);
                    if v_isShared_2657_ == 0 {
                        lean_ctor_set(v___x_2656_, 0, v___x_2685_);
                        v___x_2687_ = v___x_2656_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_2691_ = lean_alloc_ctor(1, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_2691_, 0, v___x_2685_);
                        v___x_2687_ = v_reuseFailAlloc_2691_;
                        state = 4;
                        continue;
                    }
                } else {
                    lean_dec_ref(v_args_2663_);
                    lean_del_object(v___x_2656_);
                    lean_dec(v_val_2654_);
                    lean_dec(v_us_2648_);
                    lean_dec(v_declName_2647_);
                    v___x_2692_ = lean_box(0);
                    if v_isShared_2653_ == 0 {
                        lean_ctor_set(v___x_2652_, 0, v___x_2692_);
                        v___x_2694_ = v___x_2652_;
                        state = 6;
                        continue;
                    } else {
                        v_reuseFailAlloc_2695_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_2695_, 0, v___x_2692_);
                        v___x_2694_ = v_reuseFailAlloc_2695_;
                        state = 6;
                        continue;
                    }
                }
            }
            4 => {
                if v_isShared_2653_ == 0 {
                    lean_ctor_set(v___x_2652_, 0, v___x_2687_);
                    v___x_2689_ = v___x_2652_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_2690_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2690_, 0, v___x_2687_);
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
                if lean_obj_tag(v_a_2702_) == 5 {
                    v_val_2706_ = lean_ctor_get(v_a_2702_, 0);
                    v_isSharedCheck_2790_ = (!lean_is_exclusive(v_a_2702_)) as u8;
                    if v_isSharedCheck_2790_ == 0 {
                        v___x_2708_ = v_a_2702_;
                        v_isShared_2709_ = v_isSharedCheck_2790_;
                        state = 8;
                        continue;
                    } else {
                        lean_inc(v_val_2706_);
                        lean_dec(v_a_2702_);
                        v___x_2708_ = lean_box(0);
                        v_isShared_2709_ = v_isSharedCheck_2790_;
                        state = 8;
                        continue;
                    }
                } else {
                    lean_dec(v_a_2702_);
                    lean_dec(v_us_2648_);
                    lean_dec(v_declName_2647_);
                    lean_dec_ref(v_e_2633_);
                    v___x_2791_ = lean_box(0);
                    if v_isShared_2705_ == 0 {
                        lean_ctor_set(v___x_2704_, 0, v___x_2791_);
                        v___x_2793_ = v___x_2704_;
                        state = 17;
                        continue;
                    } else {
                        v_reuseFailAlloc_2794_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_2794_, 0, v___x_2791_);
                        v___x_2793_ = v_reuseFailAlloc_2794_;
                        state = 17;
                        continue;
                    }
                }
            }
            8 => {
                v_toConstantVal_2710_ = lean_ctor_get(v_val_2706_, 0);
                lean_inc_ref(v_toConstantVal_2710_);
                v_numParams_2711_ = lean_ctor_get(v_val_2706_, 1);
                lean_inc(v_numParams_2711_);
                v_numIndices_2712_ = lean_ctor_get(v_val_2706_, 2);
                lean_inc(v_numIndices_2712_);
                v_ctors_2713_ = lean_ctor_get(v_val_2706_, 4);
                lean_inc(v_ctors_2713_);
                v_nargs_2714_ = l_Lean_Expr_getAppNumArgs(v_e_2633_);
                v_dummy_2715_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Meta_matchMatcherApp_x3f___at___00Lean_Meta_Grind_casesMatch_spec__0___closed__0), core::ptr::addr_of_mut!(l_Lean_Meta_matchMatcherApp_x3f___at___00Lean_Meta_Grind_casesMatch_spec__0___closed__0_once), _init_l_Lean_Meta_matchMatcherApp_x3f___at___00Lean_Meta_Grind_casesMatch_spec__0___closed__0);
                lean_inc(v_nargs_2714_);
                v___x_2716_ = lean_mk_array(v_nargs_2714_, v_dummy_2715_);
                v___x_2717_ = lean_unsigned_to_nat(1);
                v___x_2718_ = lean_nat_sub(v_nargs_2714_, v___x_2717_);
                lean_dec(v_nargs_2714_);
                v_args_2719_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(
                    v_e_2633_,
                    v___x_2716_,
                    v___x_2718_,
                );
                v___x_2720_ = lean_nat_add(v_numParams_2711_, v___x_2717_);
                v___x_2721_ = lean_nat_add(v___x_2720_, v_numIndices_2712_);
                v___x_2722_ = lean_nat_add(v___x_2721_, v___x_2717_);
                lean_dec(v___x_2721_);
                v___x_2723_ = l_Lean_InductiveVal_numCtors(v_val_2706_);
                lean_dec_ref(v_val_2706_);
                v___x_2724_ = lean_nat_add(v___x_2722_, v___x_2723_);
                lean_dec(v___x_2723_);
                v___x_2725_ = lean_array_get_size(v_args_2719_);
                v___x_2726_ = lean_nat_dec_le(v___x_2724_, v___x_2725_);
                if v___x_2726_ == 0 {
                    lean_dec(v___x_2724_);
                    lean_dec(v___x_2722_);
                    lean_dec(v___x_2720_);
                    lean_dec_ref(v_args_2719_);
                    lean_dec(v_ctors_2713_);
                    lean_dec(v_numIndices_2712_);
                    lean_dec(v_numParams_2711_);
                    lean_dec_ref(v_toConstantVal_2710_);
                    lean_del_object(v___x_2708_);
                    lean_dec(v_us_2648_);
                    lean_dec(v_declName_2647_);
                    v___x_2727_ = lean_box(0);
                    if v_isShared_2705_ == 0 {
                        lean_ctor_set(v___x_2704_, 0, v___x_2727_);
                        v___x_2729_ = v___x_2704_;
                        state = 9;
                        continue;
                    } else {
                        v_reuseFailAlloc_2730_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_2730_, 0, v___x_2727_);
                        v___x_2729_ = v_reuseFailAlloc_2730_;
                        state = 9;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_2704_);
                    v___x_2731_ = lean_unsigned_to_nat(0);
                    lean_inc(v_numParams_2711_);
                    lean_inc_ref_n(v_args_2719_, 3);
                    v_params_2732_ =
                        l_Array_toSubarray___redArg(v_args_2719_, v___x_2731_, v_numParams_2711_);
                    v___x_2733_ = l_Lean_instInhabitedExpr;
                    v_motive_2734_ = lean_array_get(v___x_2733_, v_args_2719_, v_numParams_2711_);
                    lean_dec(v_numParams_2711_);
                    lean_inc(v___x_2722_);
                    v_discrs_2735_ =
                        l_Array_toSubarray___redArg(v_args_2719_, v___x_2720_, v___x_2722_);
                    v___x_2736_ = lean_nat_add(v_numIndices_2712_, v___x_2717_);
                    lean_dec(v_numIndices_2712_);
                    v___x_2737_ = lean_box(0);
                    v_discrInfos_2738_ = lean_mk_array(v___x_2736_, v___x_2737_);
                    lean_inc(v___x_2724_);
                    v_alts_2739_ =
                        l_Array_toSubarray___redArg(v_args_2719_, v___x_2722_, v___x_2724_);
                    v___x_2789_ = lean_nat_dec_le(v___x_2724_, v___x_2731_);
                    if v___x_2789_ == 0 {
                        v_lower_2781_ = v___x_2724_;
                        v_upper_2782_ = v___x_2725_;
                        state = 16;
                        continue;
                    } else {
                        lean_dec(v___x_2724_);
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
                if lean_obj_tag(v___x_2746_) == 0 {
                    v_a_2747_ = lean_ctor_get(v___x_2746_, 0);
                    v_isSharedCheck_2771_ = (!lean_is_exclusive(v___x_2746_)) as u8;
                    if v_isSharedCheck_2771_ == 0 {
                        v___x_2749_ = v___x_2746_;
                        v_isShared_2750_ = v_isSharedCheck_2771_;
                        state = 11;
                        continue;
                    } else {
                        lean_inc(v_a_2747_);
                        lean_dec(v___x_2746_);
                        v___x_2749_ = lean_box(0);
                        v_isShared_2750_ = v_isSharedCheck_2771_;
                        state = 11;
                        continue;
                    }
                } else {
                    lean_dec(v___y_2742_);
                    lean_dec_ref(v___y_2741_);
                    lean_dec_ref(v_alts_2739_);
                    lean_dec_ref(v_discrInfos_2738_);
                    lean_dec_ref(v_discrs_2735_);
                    lean_dec(v_motive_2734_);
                    lean_dec_ref(v_params_2732_);
                    lean_del_object(v___x_2708_);
                    lean_dec(v_us_2648_);
                    lean_dec(v_declName_2647_);
                    v_a_2772_ = lean_ctor_get(v___x_2746_, 0);
                    v_isSharedCheck_2779_ = (!lean_is_exclusive(v___x_2746_)) as u8;
                    if v_isSharedCheck_2779_ == 0 {
                        v___x_2774_ = v___x_2746_;
                        v_isShared_2775_ = v_isSharedCheck_2779_;
                        state = 14;
                        continue;
                    } else {
                        lean_inc(v_a_2772_);
                        lean_dec(v___x_2746_);
                        v___x_2774_ = lean_box(0);
                        v_isShared_2775_ = v_isSharedCheck_2779_;
                        state = 14;
                        continue;
                    }
                }
            }
            11 => {
                v_start_2751_ = lean_ctor_get(v_params_2732_, 1);
                lean_inc(v_start_2751_);
                v_stop_2752_ = lean_ctor_get(v_params_2732_, 2);
                lean_inc(v_stop_2752_);
                v_start_2753_ = lean_ctor_get(v_discrs_2735_, 1);
                lean_inc(v_start_2753_);
                v_stop_2754_ = lean_ctor_get(v_discrs_2735_, 2);
                lean_inc(v_stop_2754_);
                v___x_2755_ = lean_nat_sub(v_stop_2752_, v_start_2751_);
                lean_dec(v_start_2751_);
                lean_dec(v_stop_2752_);
                v___x_2756_ = lean_nat_sub(v_stop_2754_, v_start_2753_);
                lean_dec(v_start_2753_);
                lean_dec(v_stop_2754_);
                v___x_2757_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Meta_matchMatcherApp_x3f___at___00Lean_Meta_Grind_casesMatch_spec__0___closed__2), core::ptr::addr_of_mut!(l_Lean_Meta_matchMatcherApp_x3f___at___00Lean_Meta_Grind_casesMatch_spec__0___closed__2_once), _init_l_Lean_Meta_matchMatcherApp_x3f___at___00Lean_Meta_Grind_casesMatch_spec__0___closed__2);
                v___x_2758_ = lean_alloc_ctor(0, 6, (0) as u32);
                lean_ctor_set(v___x_2758_, 0, v___x_2755_);
                lean_ctor_set(v___x_2758_, 1, v___x_2756_);
                lean_ctor_set(v___x_2758_, 2, v_a_2747_);
                lean_ctor_set(v___x_2758_, 3, v___y_2742_);
                lean_ctor_set(v___x_2758_, 4, v_discrInfos_2738_);
                lean_ctor_set(v___x_2758_, 5, v___x_2757_);
                v___x_2759_ = lean_array_mk(v_us_2648_);
                v___x_2760_ = l_Subarray_copy___redArg(v_params_2732_);
                v___x_2761_ = l_Subarray_copy___redArg(v_discrs_2735_);
                v___x_2762_ = l_Subarray_copy___redArg(v_alts_2739_);
                v___x_2763_ = l_Subarray_copy___redArg(v___y_2741_);
                v___x_2764_ = lean_alloc_ctor(0, 8, (0) as u32);
                lean_ctor_set(v___x_2764_, 0, v___x_2758_);
                lean_ctor_set(v___x_2764_, 1, v_declName_2647_);
                lean_ctor_set(v___x_2764_, 2, v___x_2759_);
                lean_ctor_set(v___x_2764_, 3, v___x_2760_);
                lean_ctor_set(v___x_2764_, 4, v_motive_2734_);
                lean_ctor_set(v___x_2764_, 5, v___x_2761_);
                lean_ctor_set(v___x_2764_, 6, v___x_2762_);
                lean_ctor_set(v___x_2764_, 7, v___x_2763_);
                if v_isShared_2709_ == 0 {
                    lean_ctor_set_tag(v___x_2708_, 1);
                    lean_ctor_set(v___x_2708_, 0, v___x_2764_);
                    v___x_2766_ = v___x_2708_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_2770_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2770_, 0, v___x_2764_);
                    v___x_2766_ = v_reuseFailAlloc_2770_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                if v_isShared_2750_ == 0 {
                    lean_ctor_set(v___x_2749_, 0, v___x_2766_);
                    v___x_2768_ = v___x_2749_;
                    state = 13;
                    continue;
                } else {
                    v_reuseFailAlloc_2769_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2769_, 0, v___x_2766_);
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
                    v_reuseFailAlloc_2778_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2778_, 0, v_a_2772_);
                    v___x_2777_ = v_reuseFailAlloc_2778_;
                    state = 15;
                    continue;
                }
            }
            15 => {
                return v___x_2777_;
            }
            16 => {
                v_levelParams_2783_ = lean_ctor_get(v_toConstantVal_2710_, 1);
                lean_inc(v_levelParams_2783_);
                lean_dec_ref(v_toConstantVal_2710_);
                v___x_2784_ =
                    l_Array_toSubarray___redArg(v_args_2719_, v_lower_2781_, v_upper_2782_);
                v___x_2785_ = l_List_lengthTR___redArg(v_levelParams_2783_);
                lean_dec(v_levelParams_2783_);
                v___x_2786_ = l_List_lengthTR___redArg(v_us_2648_);
                v___x_2787_ = lean_nat_dec_eq(v___x_2785_, v___x_2786_);
                lean_dec(v___x_2786_);
                lean_dec(v___x_2785_);
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
                    v_reuseFailAlloc_2802_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2802_, 0, v_a_2796_);
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
    mut v_e_2805_: *mut LeanObject,
    mut v_alsoCasesOn_2806_: *mut LeanObject,
    mut v___y_2807_: *mut LeanObject,
    mut v___y_2808_: *mut LeanObject,
    mut v___y_2809_: *mut LeanObject,
    mut v___y_2810_: *mut LeanObject,
    mut v___y_2811_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_alsoCasesOn_boxed_2812_: u8 = 0;
    let mut v_res_2813_: *mut LeanObject = core::ptr::null_mut();
    v_alsoCasesOn_boxed_2812_ = (lean_unbox(v_alsoCasesOn_2806_) as u8);
    v_res_2813_ = l_Lean_Meta_matchMatcherApp_x3f___at___00Lean_Meta_Grind_casesMatch_spec__0(
        v_e_2805_,
        v_alsoCasesOn_boxed_2812_,
        v___y_2807_,
        v___y_2808_,
        v___y_2809_,
        v___y_2810_,
    );
    lean_dec(v___y_2810_);
    lean_dec_ref(v___y_2809_);
    lean_dec(v___y_2808_);
    lean_dec_ref(v___y_2807_);
    return v_res_2813_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_casesMatch_spec__1_spec__5_spec__8_spec__11_spec__13___redArg(
    mut v_x_2814_: *mut LeanObject,
    mut v_x_2815_: *mut LeanObject,
    mut v_x_2816_: *mut LeanObject,
    mut v_x_2817_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_ks_2818_: *mut LeanObject = core::ptr::null_mut();
    let mut v_vs_2819_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2821_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2822_: u8 = 0;
    let mut v___x_2823_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2824_: u8 = 0;
    let mut v___x_2825_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2826_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2828_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2829_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_x27_2830_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2831_: u8 = 0;
    let mut v___x_2833_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2834_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2835_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2837_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2838_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2839_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2841_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2842_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2843_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ks_2818_ = lean_ctor_get(v_x_2814_, 0);
                v_vs_2819_ = lean_ctor_get(v_x_2814_, 1);
                v_isSharedCheck_2843_ = (!lean_is_exclusive(v_x_2814_)) as u8;
                if v_isSharedCheck_2843_ == 0 {
                    v___x_2821_ = v_x_2814_;
                    v_isShared_2822_ = v_isSharedCheck_2843_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_vs_2819_);
                    lean_inc(v_ks_2818_);
                    lean_dec(v_x_2814_);
                    v___x_2821_ = lean_box(0);
                    v_isShared_2822_ = v_isSharedCheck_2843_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_2823_ = lean_array_get_size(v_ks_2818_);
                v___x_2824_ = lean_nat_dec_lt(v_x_2815_, v___x_2823_);
                if v___x_2824_ == 0 {
                    lean_dec(v_x_2815_);
                    v___x_2825_ = lean_array_push(v_ks_2818_, v_x_2816_);
                    v___x_2826_ = lean_array_push(v_vs_2819_, v_x_2817_);
                    if v_isShared_2822_ == 0 {
                        lean_ctor_set(v___x_2821_, 1, v___x_2826_);
                        lean_ctor_set(v___x_2821_, 0, v___x_2825_);
                        v___x_2828_ = v___x_2821_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_2829_ = lean_alloc_ctor(1, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_2829_, 0, v___x_2825_);
                        lean_ctor_set(v_reuseFailAlloc_2829_, 1, v___x_2826_);
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
                            v_reuseFailAlloc_2837_ = lean_alloc_ctor(1, 2, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_2837_, 0, v_ks_2818_);
                            lean_ctor_set(v_reuseFailAlloc_2837_, 1, v_vs_2819_);
                            v___x_2833_ = v_reuseFailAlloc_2837_;
                            state = 3;
                            continue;
                        }
                    } else {
                        v___x_2838_ = lean_array_fset(v_ks_2818_, v_x_2815_, v_x_2816_);
                        v___x_2839_ = lean_array_fset(v_vs_2819_, v_x_2815_, v_x_2817_);
                        lean_dec(v_x_2815_);
                        if v_isShared_2822_ == 0 {
                            lean_ctor_set(v___x_2821_, 1, v___x_2839_);
                            lean_ctor_set(v___x_2821_, 0, v___x_2838_);
                            v___x_2841_ = v___x_2821_;
                            state = 4;
                            continue;
                        } else {
                            v_reuseFailAlloc_2842_ = lean_alloc_ctor(1, 2, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_2842_, 0, v___x_2838_);
                            lean_ctor_set(v_reuseFailAlloc_2842_, 1, v___x_2839_);
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
                v___x_2834_ = lean_unsigned_to_nat(1);
                v___x_2835_ = lean_nat_add(v_x_2815_, v___x_2834_);
                lean_dec(v_x_2815_);
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
    mut v_n_2844_: *mut LeanObject,
    mut v_k_2845_: *mut LeanObject,
    mut v_v_2846_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2847_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2848_: *mut LeanObject = core::ptr::null_mut();
    v___x_2847_ = lean_unsigned_to_nat(0);
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
    v___x_2853_ = lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_casesMatch_spec__1_spec__5_spec__8___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_casesMatch_spec__1_spec__5_spec__8___redArg___closed__0_once), _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_casesMatch_spec__1_spec__5_spec__8___redArg___closed__0);
    v___x_2854_ = lean_usize_sub(v___x_2853_, v___x_2852_);
    return v___x_2854_;
}
pub unsafe fn _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_casesMatch_spec__1_spec__5_spec__8___redArg___closed__2()
-> *mut LeanObject {
    let mut v___x_2855_: *mut LeanObject = core::ptr::null_mut();
    v___x_2855_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
    return v___x_2855_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_casesMatch_spec__1_spec__5_spec__8___redArg(
    mut v_x_2856_: *mut LeanObject,
    mut v_x_2857_: usize,
    mut v_x_2858_: usize,
    mut v_x_2859_: *mut LeanObject,
    mut v_x_2860_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_es_2861_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2862_: usize = 0;
    let mut v___x_2863_: usize = 0;
    let mut v___x_2864_: usize = 0;
    let mut v___x_2865_: usize = 0;
    let mut v_j_2866_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2867_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2868_: u8 = 0;
    let mut v___x_2870_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2871_: u8 = 0;
    let mut v_v_2872_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2873_: *mut LeanObject = core::ptr::null_mut();
    let mut v_xs_x27_2874_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2876_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2877_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2879_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2880_: *mut LeanObject = core::ptr::null_mut();
    let mut v_key_2881_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_2882_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2884_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2885_: u8 = 0;
    let mut v___x_2886_: u8 = 0;
    let mut v___x_2887_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2888_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2890_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2891_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2892_: u8 = 0;
    let mut v_node_2893_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2895_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2896_: u8 = 0;
    let mut v___x_2897_: usize = 0;
    let mut v___x_2898_: usize = 0;
    let mut v___x_2899_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2901_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2902_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2903_: u8 = 0;
    let mut v___x_2904_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2905_: u8 = 0;
    let mut v_unused_2906_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ks_2907_: *mut LeanObject = core::ptr::null_mut();
    let mut v_vs_2908_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2910_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2911_: u8 = 0;
    let mut v___x_2913_: *mut LeanObject = core::ptr::null_mut();
    let mut v_newNode_2914_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2916_: u8 = 0;
    let mut v_ks_2917_: *mut LeanObject = core::ptr::null_mut();
    let mut v_vs_2918_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2919_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2920_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2921_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2922_: usize = 0;
    let mut v___x_2923_: u8 = 0;
    let mut v___x_2924_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2925_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2926_: u8 = 0;
    let mut v_reuseFailAlloc_2927_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2928_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_2856_) == 0 {
                    v_es_2861_ = lean_ctor_get(v_x_2856_, 0);
                    v___x_2862_ = 5usize;
                    v___x_2863_ = 1usize;
                    v___x_2864_ = lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_casesMatch_spec__1_spec__5_spec__8___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_casesMatch_spec__1_spec__5_spec__8___redArg___closed__1_once), _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_casesMatch_spec__1_spec__5_spec__8___redArg___closed__1);
                    v___x_2865_ = lean_usize_land(v_x_2857_, v___x_2864_);
                    v_j_2866_ = lean_usize_to_nat(v___x_2865_);
                    v___x_2867_ = lean_array_get_size(v_es_2861_);
                    v___x_2868_ = lean_nat_dec_lt(v_j_2866_, v___x_2867_);
                    if v___x_2868_ == 0 {
                        lean_dec(v_j_2866_);
                        lean_dec(v_x_2860_);
                        lean_dec(v_x_2859_);
                        return v_x_2856_;
                    } else {
                        lean_inc_ref(v_es_2861_);
                        v_isSharedCheck_2905_ = (!lean_is_exclusive(v_x_2856_)) as u8;
                        if v_isSharedCheck_2905_ == 0 {
                            v_unused_2906_ = lean_ctor_get(v_x_2856_, 0);
                            lean_dec(v_unused_2906_);
                            v___x_2870_ = v_x_2856_;
                            v_isShared_2871_ = v_isSharedCheck_2905_;
                            state = 1;
                            continue;
                        } else {
                            lean_dec(v_x_2856_);
                            v___x_2870_ = lean_box(0);
                            v_isShared_2871_ = v_isSharedCheck_2905_;
                            state = 1;
                            continue;
                        }
                    }
                } else {
                    v_ks_2907_ = lean_ctor_get(v_x_2856_, 0);
                    v_vs_2908_ = lean_ctor_get(v_x_2856_, 1);
                    v_isSharedCheck_2928_ = (!lean_is_exclusive(v_x_2856_)) as u8;
                    if v_isSharedCheck_2928_ == 0 {
                        v___x_2910_ = v_x_2856_;
                        v_isShared_2911_ = v_isSharedCheck_2928_;
                        state = 8;
                        continue;
                    } else {
                        lean_inc(v_vs_2908_);
                        lean_inc(v_ks_2907_);
                        lean_dec(v_x_2856_);
                        v___x_2910_ = lean_box(0);
                        v_isShared_2911_ = v_isSharedCheck_2928_;
                        state = 8;
                        continue;
                    }
                }
            }
            1 => {
                v_v_2872_ = lean_array_fget(v_es_2861_, v_j_2866_);
                v___x_2873_ = lean_box(0);
                v_xs_x27_2874_ = lean_array_fset(v_es_2861_, v_j_2866_, v___x_2873_);
                match lean_obj_tag(v_v_2872_) {
                    0 => {
                        v_key_2881_ = lean_ctor_get(v_v_2872_, 0);
                        v_val_2882_ = lean_ctor_get(v_v_2872_, 1);
                        v_isSharedCheck_2892_ = (!lean_is_exclusive(v_v_2872_)) as u8;
                        if v_isSharedCheck_2892_ == 0 {
                            v___x_2884_ = v_v_2872_;
                            v_isShared_2885_ = v_isSharedCheck_2892_;
                            state = 4;
                            continue;
                        } else {
                            lean_inc(v_val_2882_);
                            lean_inc(v_key_2881_);
                            lean_dec(v_v_2872_);
                            v___x_2884_ = lean_box(0);
                            v_isShared_2885_ = v_isSharedCheck_2892_;
                            state = 4;
                            continue;
                        }
                    }
                    1 => {
                        v_node_2893_ = lean_ctor_get(v_v_2872_, 0);
                        v_isSharedCheck_2903_ = (!lean_is_exclusive(v_v_2872_)) as u8;
                        if v_isSharedCheck_2903_ == 0 {
                            v___x_2895_ = v_v_2872_;
                            v_isShared_2896_ = v_isSharedCheck_2903_;
                            state = 6;
                            continue;
                        } else {
                            lean_inc(v_node_2893_);
                            lean_dec(v_v_2872_);
                            v___x_2895_ = lean_box(0);
                            v_isShared_2896_ = v_isSharedCheck_2903_;
                            state = 6;
                            continue;
                        }
                    }
                    _ => {
                        v___x_2904_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v___x_2904_, 0, v_x_2859_);
                        lean_ctor_set(v___x_2904_, 1, v_x_2860_);
                        v___y_2876_ = v___x_2904_;
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                v___x_2877_ = lean_array_fset(v_xs_x27_2874_, v_j_2866_, v___y_2876_);
                lean_dec(v_j_2866_);
                if v_isShared_2871_ == 0 {
                    lean_ctor_set(v___x_2870_, 0, v___x_2877_);
                    v___x_2879_ = v___x_2870_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2880_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2880_, 0, v___x_2877_);
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
                    lean_del_object(v___x_2884_);
                    v___x_2887_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(
                        v_key_2881_,
                        v_val_2882_,
                        v_x_2859_,
                        v_x_2860_,
                    );
                    v___x_2888_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v___x_2888_, 0, v___x_2887_);
                    v___y_2876_ = v___x_2888_;
                    state = 2;
                    continue;
                } else {
                    lean_dec(v_val_2882_);
                    lean_dec(v_key_2881_);
                    if v_isShared_2885_ == 0 {
                        lean_ctor_set(v___x_2884_, 1, v_x_2860_);
                        lean_ctor_set(v___x_2884_, 0, v_x_2859_);
                        v___x_2890_ = v___x_2884_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_2891_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_2891_, 0, v_x_2859_);
                        lean_ctor_set(v_reuseFailAlloc_2891_, 1, v_x_2860_);
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
                    lean_ctor_set(v___x_2895_, 0, v___x_2899_);
                    v___x_2901_ = v___x_2895_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_2902_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2902_, 0, v___x_2899_);
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
                    v_reuseFailAlloc_2927_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2927_, 0, v_ks_2907_);
                    lean_ctor_set(v_reuseFailAlloc_2927_, 1, v_vs_2908_);
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
                    v___x_2925_ = lean_unsigned_to_nat(4);
                    v___x_2926_ = lean_nat_dec_lt(v___x_2924_, v___x_2925_);
                    lean_dec(v___x_2924_);
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
                    v_ks_2917_ = lean_ctor_get(v_newNode_2914_, 0);
                    lean_inc_ref(v_ks_2917_);
                    v_vs_2918_ = lean_ctor_get(v_newNode_2914_, 1);
                    lean_inc_ref(v_vs_2918_);
                    lean_dec_ref(v_newNode_2914_);
                    v___x_2919_ = lean_unsigned_to_nat(0);
                    v___x_2920_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_casesMatch_spec__1_spec__5_spec__8___redArg___closed__2), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_casesMatch_spec__1_spec__5_spec__8___redArg___closed__2_once), _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_casesMatch_spec__1_spec__5_spec__8___redArg___closed__2);
                    v___x_2921_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_casesMatch_spec__1_spec__5_spec__8_spec__12___redArg(v_x_2858_, v_ks_2917_, v_vs_2918_, v___x_2919_, v___x_2920_);
                    lean_dec_ref(v_vs_2918_);
                    lean_dec_ref(v_ks_2917_);
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
    mut v_keys_2930_: *mut LeanObject,
    mut v_vals_2931_: *mut LeanObject,
    mut v_i_2932_: *mut LeanObject,
    mut v_entries_2933_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2934_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2935_: u8 = 0;
    let mut v_k_2936_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_2937_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2938_: u64 = 0;
    let mut v_h_2939_: usize = 0;
    let mut v___x_2940_: usize = 0;
    let mut v___x_2941_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2942_: usize = 0;
    let mut v___x_2943_: usize = 0;
    let mut v___x_2944_: usize = 0;
    let mut v_h_2945_: usize = 0;
    let mut v___x_2946_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2947_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2934_ = lean_array_get_size(v_keys_2930_);
                v___x_2935_ = lean_nat_dec_lt(v_i_2932_, v___x_2934_);
                if v___x_2935_ == 0 {
                    lean_dec(v_i_2932_);
                    return v_entries_2933_;
                } else {
                    v_k_2936_ = lean_array_fget_borrowed(v_keys_2930_, v_i_2932_);
                    v_v_2937_ = lean_array_fget_borrowed(v_vals_2931_, v_i_2932_);
                    v___x_2938_ = l_Lean_instHashableMVarId_hash(v_k_2936_);
                    v_h_2939_ = lean_uint64_to_usize(v___x_2938_);
                    v___x_2940_ = 5usize;
                    v___x_2941_ = lean_unsigned_to_nat(1);
                    v___x_2942_ = 1usize;
                    v___x_2943_ = lean_usize_sub(v_depth_2929_, v___x_2942_);
                    v___x_2944_ = lean_usize_mul(v___x_2940_, v___x_2943_);
                    v_h_2945_ = lean_usize_shift_right(v_h_2939_, v___x_2944_);
                    v___x_2946_ = lean_nat_add(v_i_2932_, v___x_2941_);
                    lean_dec(v_i_2932_);
                    lean_inc(v_v_2937_);
                    lean_inc(v_k_2936_);
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
    mut v_depth_2949_: *mut LeanObject,
    mut v_keys_2950_: *mut LeanObject,
    mut v_vals_2951_: *mut LeanObject,
    mut v_i_2952_: *mut LeanObject,
    mut v_entries_2953_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_depth_boxed_2954_: usize = 0;
    let mut v_res_2955_: *mut LeanObject = core::ptr::null_mut();
    v_depth_boxed_2954_ = lean_unbox_usize(v_depth_2949_);
    lean_dec(v_depth_2949_);
    v_res_2955_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_casesMatch_spec__1_spec__5_spec__8_spec__12___redArg(v_depth_boxed_2954_, v_keys_2950_, v_vals_2951_, v_i_2952_, v_entries_2953_);
    lean_dec_ref(v_vals_2951_);
    lean_dec_ref(v_keys_2950_);
    return v_res_2955_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_casesMatch_spec__1_spec__5_spec__8___redArg___boxed(
    mut v_x_2956_: *mut LeanObject,
    mut v_x_2957_: *mut LeanObject,
    mut v_x_2958_: *mut LeanObject,
    mut v_x_2959_: *mut LeanObject,
    mut v_x_2960_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_x_9013__boxed_2961_: usize = 0;
    let mut v_x_9014__boxed_2962_: usize = 0;
    let mut v_res_2963_: *mut LeanObject = core::ptr::null_mut();
    v_x_9013__boxed_2961_ = lean_unbox_usize(v_x_2957_);
    lean_dec(v_x_2957_);
    v_x_9014__boxed_2962_ = lean_unbox_usize(v_x_2958_);
    lean_dec(v_x_2958_);
    v_res_2963_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_casesMatch_spec__1_spec__5_spec__8___redArg(v_x_2956_, v_x_9013__boxed_2961_, v_x_9014__boxed_2962_, v_x_2959_, v_x_2960_);
    return v_res_2963_;
}
pub unsafe fn l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_casesMatch_spec__1_spec__5___redArg(
    mut v_x_2964_: *mut LeanObject,
    mut v_x_2965_: *mut LeanObject,
    mut v_x_2966_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2967_: u64 = 0;
    let mut v___x_2968_: usize = 0;
    let mut v___x_2969_: usize = 0;
    let mut v___x_2970_: *mut LeanObject = core::ptr::null_mut();
    v___x_2967_ = l_Lean_instHashableMVarId_hash(v_x_2965_);
    v___x_2968_ = lean_uint64_to_usize(v___x_2967_);
    v___x_2969_ = 1usize;
    v___x_2970_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_casesMatch_spec__1_spec__5_spec__8___redArg(v_x_2964_, v___x_2968_, v___x_2969_, v_x_2965_, v_x_2966_);
    return v___x_2970_;
}
pub unsafe fn l_Lean_MVarId_assign___at___00Lean_Meta_Grind_casesMatch_spec__1___redArg(
    mut v_mvarId_2971_: *mut LeanObject,
    mut v_val_2972_: *mut LeanObject,
    mut v___y_2973_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2975_: *mut LeanObject = core::ptr::null_mut();
    let mut v_mctx_2976_: *mut LeanObject = core::ptr::null_mut();
    let mut v_cache_2977_: *mut LeanObject = core::ptr::null_mut();
    let mut v_zetaDeltaFVarIds_2978_: *mut LeanObject = core::ptr::null_mut();
    let mut v_postponed_2979_: *mut LeanObject = core::ptr::null_mut();
    let mut v_diag_2980_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2982_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2983_: u8 = 0;
    let mut v_depth_2984_: *mut LeanObject = core::ptr::null_mut();
    let mut v_levelAssignDepth_2985_: *mut LeanObject = core::ptr::null_mut();
    let mut v_lmvarCounter_2986_: *mut LeanObject = core::ptr::null_mut();
    let mut v_mvarCounter_2987_: *mut LeanObject = core::ptr::null_mut();
    let mut v_lDecls_2988_: *mut LeanObject = core::ptr::null_mut();
    let mut v_decls_2989_: *mut LeanObject = core::ptr::null_mut();
    let mut v_userNames_2990_: *mut LeanObject = core::ptr::null_mut();
    let mut v_lAssignment_2991_: *mut LeanObject = core::ptr::null_mut();
    let mut v_eAssignment_2992_: *mut LeanObject = core::ptr::null_mut();
    let mut v_dAssignment_2993_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2995_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2996_: u8 = 0;
    let mut v___x_2997_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2999_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3001_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3002_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3003_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3004_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3005_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3006_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3007_: u8 = 0;
    let mut v_isSharedCheck_3008_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2975_ = lean_st_ref_take(v___y_2973_);
                v_mctx_2976_ = lean_ctor_get(v___x_2975_, 0);
                v_cache_2977_ = lean_ctor_get(v___x_2975_, 1);
                v_zetaDeltaFVarIds_2978_ = lean_ctor_get(v___x_2975_, 2);
                v_postponed_2979_ = lean_ctor_get(v___x_2975_, 3);
                v_diag_2980_ = lean_ctor_get(v___x_2975_, 4);
                v_isSharedCheck_3008_ = (!lean_is_exclusive(v___x_2975_)) as u8;
                if v_isSharedCheck_3008_ == 0 {
                    v___x_2982_ = v___x_2975_;
                    v_isShared_2983_ = v_isSharedCheck_3008_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_diag_2980_);
                    lean_inc(v_postponed_2979_);
                    lean_inc(v_zetaDeltaFVarIds_2978_);
                    lean_inc(v_cache_2977_);
                    lean_inc(v_mctx_2976_);
                    lean_dec(v___x_2975_);
                    v___x_2982_ = lean_box(0);
                    v_isShared_2983_ = v_isSharedCheck_3008_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_depth_2984_ = lean_ctor_get(v_mctx_2976_, 0);
                v_levelAssignDepth_2985_ = lean_ctor_get(v_mctx_2976_, 1);
                v_lmvarCounter_2986_ = lean_ctor_get(v_mctx_2976_, 2);
                v_mvarCounter_2987_ = lean_ctor_get(v_mctx_2976_, 3);
                v_lDecls_2988_ = lean_ctor_get(v_mctx_2976_, 4);
                v_decls_2989_ = lean_ctor_get(v_mctx_2976_, 5);
                v_userNames_2990_ = lean_ctor_get(v_mctx_2976_, 6);
                v_lAssignment_2991_ = lean_ctor_get(v_mctx_2976_, 7);
                v_eAssignment_2992_ = lean_ctor_get(v_mctx_2976_, 8);
                v_dAssignment_2993_ = lean_ctor_get(v_mctx_2976_, 9);
                v_isSharedCheck_3007_ = (!lean_is_exclusive(v_mctx_2976_)) as u8;
                if v_isSharedCheck_3007_ == 0 {
                    v___x_2995_ = v_mctx_2976_;
                    v_isShared_2996_ = v_isSharedCheck_3007_;
                    state = 2;
                    continue;
                } else {
                    lean_inc(v_dAssignment_2993_);
                    lean_inc(v_eAssignment_2992_);
                    lean_inc(v_lAssignment_2991_);
                    lean_inc(v_userNames_2990_);
                    lean_inc(v_decls_2989_);
                    lean_inc(v_lDecls_2988_);
                    lean_inc(v_mvarCounter_2987_);
                    lean_inc(v_lmvarCounter_2986_);
                    lean_inc(v_levelAssignDepth_2985_);
                    lean_inc(v_depth_2984_);
                    lean_dec(v_mctx_2976_);
                    v___x_2995_ = lean_box(0);
                    v_isShared_2996_ = v_isSharedCheck_3007_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_2997_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_casesMatch_spec__1_spec__5___redArg(v_eAssignment_2992_, v_mvarId_2971_, v_val_2972_);
                if v_isShared_2996_ == 0 {
                    lean_ctor_set(v___x_2995_, 8, v___x_2997_);
                    v___x_2999_ = v___x_2995_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_3006_ = lean_alloc_ctor(0, 10, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3006_, 0, v_depth_2984_);
                    lean_ctor_set(v_reuseFailAlloc_3006_, 1, v_levelAssignDepth_2985_);
                    lean_ctor_set(v_reuseFailAlloc_3006_, 2, v_lmvarCounter_2986_);
                    lean_ctor_set(v_reuseFailAlloc_3006_, 3, v_mvarCounter_2987_);
                    lean_ctor_set(v_reuseFailAlloc_3006_, 4, v_lDecls_2988_);
                    lean_ctor_set(v_reuseFailAlloc_3006_, 5, v_decls_2989_);
                    lean_ctor_set(v_reuseFailAlloc_3006_, 6, v_userNames_2990_);
                    lean_ctor_set(v_reuseFailAlloc_3006_, 7, v_lAssignment_2991_);
                    lean_ctor_set(v_reuseFailAlloc_3006_, 8, v___x_2997_);
                    lean_ctor_set(v_reuseFailAlloc_3006_, 9, v_dAssignment_2993_);
                    v___x_2999_ = v_reuseFailAlloc_3006_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_2983_ == 0 {
                    lean_ctor_set(v___x_2982_, 0, v___x_2999_);
                    v___x_3001_ = v___x_2982_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3005_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3005_, 0, v___x_2999_);
                    lean_ctor_set(v_reuseFailAlloc_3005_, 1, v_cache_2977_);
                    lean_ctor_set(v_reuseFailAlloc_3005_, 2, v_zetaDeltaFVarIds_2978_);
                    lean_ctor_set(v_reuseFailAlloc_3005_, 3, v_postponed_2979_);
                    lean_ctor_set(v_reuseFailAlloc_3005_, 4, v_diag_2980_);
                    v___x_3001_ = v_reuseFailAlloc_3005_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_3002_ = lean_st_ref_set(v___y_2973_, v___x_3001_);
                v___x_3003_ = lean_box(0);
                v___x_3004_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_3004_, 0, v___x_3003_);
                return v___x_3004_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_MVarId_assign___at___00Lean_Meta_Grind_casesMatch_spec__1___redArg___boxed(
    mut v_mvarId_3009_: *mut LeanObject,
    mut v_val_3010_: *mut LeanObject,
    mut v___y_3011_: *mut LeanObject,
    mut v___y_3012_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3013_: *mut LeanObject = core::ptr::null_mut();
    v_res_3013_ = l_Lean_MVarId_assign___at___00Lean_Meta_Grind_casesMatch_spec__1___redArg(
        v_mvarId_3009_,
        v_val_3010_,
        v___y_3011_,
    );
    lean_dec(v___y_3011_);
    return v_res_3013_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_casesMatch___lam__0___closed__4() -> *mut LeanObject {
    let mut v___x_3020_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3021_: *mut LeanObject = core::ptr::null_mut();
    v___x_3020_ = l_Lean_Meta_Grind_casesMatch___lam__0___closed__3;
    v___x_3021_ = l_Lean_stringToMessageData(v___x_3020_);
    return v___x_3021_;
}
pub unsafe fn l_Lean_Meta_Grind_casesMatch___lam__0(
    mut v_e_3022_: *mut LeanObject,
    mut v___x_3023_: u8,
    mut v_mvarId_3024_: *mut LeanObject,
    mut v___y_3025_: *mut LeanObject,
    mut v___y_3026_: *mut LeanObject,
    mut v___y_3027_: *mut LeanObject,
    mut v___y_3028_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3030_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3031_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_3032_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3033_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3034_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_3035_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_3036_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3037_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3038_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toMatcherInfo_3039_: *mut LeanObject = core::ptr::null_mut();
    let mut v_matcherName_3040_: *mut LeanObject = core::ptr::null_mut();
    let mut v_matcherLevels_3041_: *mut LeanObject = core::ptr::null_mut();
    let mut v_params_3042_: *mut LeanObject = core::ptr::null_mut();
    let mut v_discrs_3043_: *mut LeanObject = core::ptr::null_mut();
    let mut v_alts_3044_: *mut LeanObject = core::ptr::null_mut();
    let mut v_us_3046_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3047_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3048_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3049_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3050_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3051_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3052_: *mut LeanObject = core::ptr::null_mut();
    let mut v_splitterName_3053_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3054_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3055_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3056_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3057_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3058_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3059_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3060_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3061_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3062_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3063_: u8 = 0;
    let mut v___x_3064_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3065_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_3066_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3067_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3068_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3069_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3070_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3072_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3073_: u8 = 0;
    let mut v___x_3074_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3075_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3076_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3078_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3079_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3080_: u8 = 0;
    let mut v_unused_3081_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3082_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3084_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3085_: u8 = 0;
    let mut v___x_3087_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3088_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3089_: u8 = 0;
    let mut v_a_3090_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3092_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3093_: u8 = 0;
    let mut v___x_3095_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3096_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3097_: u8 = 0;
    let mut v_a_3098_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3100_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3101_: u8 = 0;
    let mut v___x_3103_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3104_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3105_: u8 = 0;
    let mut v_a_3106_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3108_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3109_: u8 = 0;
    let mut v___x_3111_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3112_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3113_: u8 = 0;
    let mut v_uElimPos_x3f_3114_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_3115_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3116_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3117_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3118_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3119_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3121_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3122_: u8 = 0;
    let mut v___x_3124_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3125_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3126_: u8 = 0;
    let mut v_a_3127_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3129_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3130_: u8 = 0;
    let mut v___x_3132_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3133_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3134_: u8 = 0;
    let mut v_a_3135_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3137_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3138_: u8 = 0;
    let mut v___x_3140_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3141_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3142_: u8 = 0;
    let mut v___x_3143_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3144_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3145_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3146_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3147_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3148_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3149_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3151_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3152_: u8 = 0;
    let mut v___x_3154_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3155_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3156_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                lean_inc_ref(v_e_3022_);
                v___x_3030_ =
                    l_Lean_Meta_matchMatcherApp_x3f___at___00Lean_Meta_Grind_casesMatch_spec__0(
                        v_e_3022_,
                        v___x_3023_,
                        v___y_3025_,
                        v___y_3026_,
                        v___y_3027_,
                        v___y_3028_,
                    );
                if lean_obj_tag(v___x_3030_) == 0 {
                    v_a_3031_ = lean_ctor_get(v___x_3030_, 0);
                    lean_inc(v_a_3031_);
                    lean_dec_ref_known(v___x_3030_, 1);
                    if lean_obj_tag(v_a_3031_) == 1 {
                        v_val_3032_ = lean_ctor_get(v_a_3031_, 0);
                        lean_inc_n(v_val_3032_, 2);
                        lean_dec_ref_known(v_a_3031_, 1);
                        lean_inc(v_mvarId_3024_);
                        v___x_3033_ = l___private_Lean_Meta_Tactic_Grind_CasesMatch_0__Lean_Meta_Grind_casesMatch_mkMotiveAndRefls(v_mvarId_3024_, v_e_3022_, v_val_3032_, v___y_3025_, v___y_3026_, v___y_3027_, v___y_3028_);
                        lean_dec_ref(v_e_3022_);
                        if lean_obj_tag(v___x_3033_) == 0 {
                            v_a_3034_ = lean_ctor_get(v___x_3033_, 0);
                            lean_inc(v_a_3034_);
                            lean_dec_ref_known(v___x_3033_, 1);
                            v_fst_3035_ = lean_ctor_get(v_a_3034_, 0);
                            lean_inc(v_fst_3035_);
                            v_snd_3036_ = lean_ctor_get(v_a_3034_, 1);
                            lean_inc(v_snd_3036_);
                            lean_dec(v_a_3034_);
                            lean_inc(v_mvarId_3024_);
                            v___x_3037_ = l_Lean_MVarId_getType(
                                v_mvarId_3024_,
                                v___y_3025_,
                                v___y_3026_,
                                v___y_3027_,
                                v___y_3028_,
                            );
                            if lean_obj_tag(v___x_3037_) == 0 {
                                v_a_3038_ = lean_ctor_get(v___x_3037_, 0);
                                lean_inc(v_a_3038_);
                                lean_dec_ref_known(v___x_3037_, 1);
                                v_toMatcherInfo_3039_ = lean_ctor_get(v_val_3032_, 0);
                                lean_inc_ref(v_toMatcherInfo_3039_);
                                v_matcherName_3040_ = lean_ctor_get(v_val_3032_, 1);
                                lean_inc(v_matcherName_3040_);
                                v_matcherLevels_3041_ = lean_ctor_get(v_val_3032_, 2);
                                lean_inc_ref(v_matcherLevels_3041_);
                                v_params_3042_ = lean_ctor_get(v_val_3032_, 3);
                                lean_inc_ref(v_params_3042_);
                                v_discrs_3043_ = lean_ctor_get(v_val_3032_, 5);
                                lean_inc_ref(v_discrs_3043_);
                                v_alts_3044_ = lean_ctor_get(v_val_3032_, 6);
                                lean_inc_ref(v_alts_3044_);
                                lean_dec(v_val_3032_);
                                v_uElimPos_x3f_3114_ = lean_ctor_get(v_toMatcherInfo_3039_, 3);
                                lean_inc(v_uElimPos_x3f_3114_);
                                lean_dec_ref(v_toMatcherInfo_3039_);
                                if lean_obj_tag(v_uElimPos_x3f_3114_) == 1 {
                                    v_val_3115_ = lean_ctor_get(v_uElimPos_x3f_3114_, 0);
                                    lean_inc(v_val_3115_);
                                    lean_dec_ref_known(v_uElimPos_x3f_3114_, 1);
                                    v___x_3116_ = l_Lean_Meta_getLevel(
                                        v_a_3038_,
                                        v___y_3025_,
                                        v___y_3026_,
                                        v___y_3027_,
                                        v___y_3028_,
                                    );
                                    if lean_obj_tag(v___x_3116_) == 0 {
                                        v_a_3117_ = lean_ctor_get(v___x_3116_, 0);
                                        lean_inc(v_a_3117_);
                                        lean_dec_ref_known(v___x_3116_, 1);
                                        v___x_3118_ = lean_array_set(
                                            v_matcherLevels_3041_,
                                            v_val_3115_,
                                            v_a_3117_,
                                        );
                                        lean_dec(v_val_3115_);
                                        v_us_3046_ = v___x_3118_;
                                        v___y_3047_ = v___y_3025_;
                                        v___y_3048_ = v___y_3026_;
                                        v___y_3049_ = v___y_3027_;
                                        v___y_3050_ = v___y_3028_;
                                        state = 1;
                                        continue;
                                    } else {
                                        lean_dec(v_val_3115_);
                                        lean_dec_ref(v_alts_3044_);
                                        lean_dec_ref(v_discrs_3043_);
                                        lean_dec_ref(v_params_3042_);
                                        lean_dec_ref(v_matcherLevels_3041_);
                                        lean_dec(v_matcherName_3040_);
                                        lean_dec(v_snd_3036_);
                                        lean_dec(v_fst_3035_);
                                        lean_dec(v___y_3028_);
                                        lean_dec_ref(v___y_3027_);
                                        lean_dec(v___y_3026_);
                                        lean_dec_ref(v___y_3025_);
                                        lean_dec(v_mvarId_3024_);
                                        v_a_3119_ = lean_ctor_get(v___x_3116_, 0);
                                        v_isSharedCheck_3126_ =
                                            (!lean_is_exclusive(v___x_3116_)) as u8;
                                        if v_isSharedCheck_3126_ == 0 {
                                            v___x_3121_ = v___x_3116_;
                                            v_isShared_3122_ = v_isSharedCheck_3126_;
                                            state = 12;
                                            continue;
                                        } else {
                                            lean_inc(v_a_3119_);
                                            lean_dec(v___x_3116_);
                                            v___x_3121_ = lean_box(0);
                                            v_isShared_3122_ = v_isSharedCheck_3126_;
                                            state = 12;
                                            continue;
                                        }
                                    }
                                } else {
                                    lean_dec(v_uElimPos_x3f_3114_);
                                    lean_dec(v_a_3038_);
                                    v_us_3046_ = v_matcherLevels_3041_;
                                    v___y_3047_ = v___y_3025_;
                                    v___y_3048_ = v___y_3026_;
                                    v___y_3049_ = v___y_3027_;
                                    v___y_3050_ = v___y_3028_;
                                    state = 1;
                                    continue;
                                }
                            } else {
                                lean_dec(v_snd_3036_);
                                lean_dec(v_fst_3035_);
                                lean_dec(v_val_3032_);
                                lean_dec(v___y_3028_);
                                lean_dec_ref(v___y_3027_);
                                lean_dec(v___y_3026_);
                                lean_dec_ref(v___y_3025_);
                                lean_dec(v_mvarId_3024_);
                                v_a_3127_ = lean_ctor_get(v___x_3037_, 0);
                                v_isSharedCheck_3134_ = (!lean_is_exclusive(v___x_3037_)) as u8;
                                if v_isSharedCheck_3134_ == 0 {
                                    v___x_3129_ = v___x_3037_;
                                    v_isShared_3130_ = v_isSharedCheck_3134_;
                                    state = 14;
                                    continue;
                                } else {
                                    lean_inc(v_a_3127_);
                                    lean_dec(v___x_3037_);
                                    v___x_3129_ = lean_box(0);
                                    v_isShared_3130_ = v_isSharedCheck_3134_;
                                    state = 14;
                                    continue;
                                }
                            }
                        } else {
                            lean_dec(v_val_3032_);
                            lean_dec(v___y_3028_);
                            lean_dec_ref(v___y_3027_);
                            lean_dec(v___y_3026_);
                            lean_dec_ref(v___y_3025_);
                            lean_dec(v_mvarId_3024_);
                            v_a_3135_ = lean_ctor_get(v___x_3033_, 0);
                            v_isSharedCheck_3142_ = (!lean_is_exclusive(v___x_3033_)) as u8;
                            if v_isSharedCheck_3142_ == 0 {
                                v___x_3137_ = v___x_3033_;
                                v_isShared_3138_ = v_isSharedCheck_3142_;
                                state = 16;
                                continue;
                            } else {
                                lean_inc(v_a_3135_);
                                lean_dec(v___x_3033_);
                                v___x_3137_ = lean_box(0);
                                v_isShared_3138_ = v_isSharedCheck_3142_;
                                state = 16;
                                continue;
                            }
                        }
                    } else {
                        lean_dec(v_a_3031_);
                        v___x_3143_ = l_Lean_Meta_Grind_casesMatch___lam__0___closed__2;
                        v___x_3144_ = lean_obj_once(
                            core::ptr::addr_of_mut!(
                                l_Lean_Meta_Grind_casesMatch___lam__0___closed__4
                            ),
                            core::ptr::addr_of_mut!(
                                l_Lean_Meta_Grind_casesMatch___lam__0___closed__4_once
                            ),
                            _init_l_Lean_Meta_Grind_casesMatch___lam__0___closed__4,
                        );
                        v___x_3145_ = l_Lean_indentExpr(v_e_3022_);
                        v___x_3146_ = lean_alloc_ctor(7, 2, (0) as u32);
                        lean_ctor_set(v___x_3146_, 0, v___x_3144_);
                        lean_ctor_set(v___x_3146_, 1, v___x_3145_);
                        v___x_3147_ = lean_alloc_ctor(1, 1, (0) as u32);
                        lean_ctor_set(v___x_3147_, 0, v___x_3146_);
                        v___x_3148_ = l_Lean_Meta_throwTacticEx___redArg(
                            v___x_3143_,
                            v_mvarId_3024_,
                            v___x_3147_,
                            v___y_3025_,
                            v___y_3026_,
                            v___y_3027_,
                            v___y_3028_,
                        );
                        lean_dec(v___y_3028_);
                        lean_dec_ref(v___y_3027_);
                        lean_dec(v___y_3026_);
                        lean_dec_ref(v___y_3025_);
                        return v___x_3148_;
                    }
                } else {
                    lean_dec(v___y_3028_);
                    lean_dec_ref(v___y_3027_);
                    lean_dec(v___y_3026_);
                    lean_dec_ref(v___y_3025_);
                    lean_dec(v_mvarId_3024_);
                    lean_dec_ref(v_e_3022_);
                    v_a_3149_ = lean_ctor_get(v___x_3030_, 0);
                    v_isSharedCheck_3156_ = (!lean_is_exclusive(v___x_3030_)) as u8;
                    if v_isSharedCheck_3156_ == 0 {
                        v___x_3151_ = v___x_3030_;
                        v_isShared_3152_ = v_isSharedCheck_3156_;
                        state = 18;
                        continue;
                    } else {
                        lean_inc(v_a_3149_);
                        lean_dec(v___x_3030_);
                        v___x_3151_ = lean_box(0);
                        v_isShared_3152_ = v_isSharedCheck_3156_;
                        state = 18;
                        continue;
                    }
                }
            }
            1 => {
                lean_inc(v___y_3050_);
                lean_inc_ref(v___y_3049_);
                lean_inc(v___y_3048_);
                lean_inc_ref(v___y_3047_);
                v___x_3051_ = lean_get_match_equations_for(
                    v_matcherName_3040_,
                    v___y_3047_,
                    v___y_3048_,
                    v___y_3049_,
                    v___y_3050_,
                );
                if lean_obj_tag(v___x_3051_) == 0 {
                    v_a_3052_ = lean_ctor_get(v___x_3051_, 0);
                    lean_inc(v_a_3052_);
                    lean_dec_ref_known(v___x_3051_, 1);
                    v_splitterName_3053_ = lean_ctor_get(v_a_3052_, 1);
                    lean_inc(v_splitterName_3053_);
                    lean_dec(v_a_3052_);
                    v___x_3054_ = lean_array_to_list(v_us_3046_);
                    v___x_3055_ = l_Lean_mkConst(v_splitterName_3053_, v___x_3054_);
                    v___x_3056_ = l_Lean_mkAppN(v___x_3055_, v_params_3042_);
                    lean_dec_ref(v_params_3042_);
                    v___x_3057_ = l_Lean_Expr_app___override(v___x_3056_, v_fst_3035_);
                    v___x_3058_ = l_Lean_mkAppN(v___x_3057_, v_discrs_3043_);
                    lean_dec_ref(v_discrs_3043_);
                    lean_inc(v___y_3050_);
                    lean_inc_ref(v___y_3049_);
                    lean_inc(v___y_3048_);
                    lean_inc_ref(v___y_3047_);
                    lean_inc_ref(v___x_3058_);
                    v___x_3059_ = lean_infer_type(
                        v___x_3058_,
                        v___y_3047_,
                        v___y_3048_,
                        v___y_3049_,
                        v___y_3050_,
                    );
                    if lean_obj_tag(v___x_3059_) == 0 {
                        v_a_3060_ = lean_ctor_get(v___x_3059_, 0);
                        lean_inc(v_a_3060_);
                        lean_dec_ref_known(v___x_3059_, 1);
                        v___x_3061_ = lean_array_get_size(v_alts_3044_);
                        lean_dec_ref(v_alts_3044_);
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
                        if lean_obj_tag(v___x_3064_) == 0 {
                            v_a_3065_ = lean_ctor_get(v___x_3064_, 0);
                            lean_inc(v_a_3065_);
                            lean_dec_ref_known(v___x_3064_, 1);
                            v_fst_3066_ = lean_ctor_get(v_a_3065_, 0);
                            lean_inc(v_fst_3066_);
                            lean_dec(v_a_3065_);
                            v___x_3067_ = l_Lean_mkAppN(v___x_3058_, v_fst_3066_);
                            v___x_3068_ = l_Lean_mkAppN(v___x_3067_, v_snd_3036_);
                            lean_dec(v_snd_3036_);
                            lean_inc(v_mvarId_3024_);
                            v___x_3069_ = l_Lean_MVarId_assign___at___00Lean_Meta_Grind_casesMatch_spec__1___redArg(v_mvarId_3024_, v___x_3068_, v___y_3048_);
                            lean_dec_ref(v___x_3069_);
                            v___x_3070_ = l___private_Lean_Meta_Tactic_Grind_CasesMatch_0__Lean_Meta_Grind_casesMatch_updateTags(v_mvarId_3024_, v_fst_3066_, v___y_3047_, v___y_3048_, v___y_3049_, v___y_3050_);
                            lean_dec(v___y_3050_);
                            lean_dec_ref(v___y_3049_);
                            lean_dec(v___y_3048_);
                            lean_dec_ref(v___y_3047_);
                            if lean_obj_tag(v___x_3070_) == 0 {
                                v_isSharedCheck_3080_ = (!lean_is_exclusive(v___x_3070_)) as u8;
                                if v_isSharedCheck_3080_ == 0 {
                                    v_unused_3081_ = lean_ctor_get(v___x_3070_, 0);
                                    lean_dec(v_unused_3081_);
                                    v___x_3072_ = v___x_3070_;
                                    v_isShared_3073_ = v_isSharedCheck_3080_;
                                    state = 2;
                                    continue;
                                } else {
                                    lean_dec(v___x_3070_);
                                    v___x_3072_ = lean_box(0);
                                    v_isShared_3073_ = v_isSharedCheck_3080_;
                                    state = 2;
                                    continue;
                                }
                            } else {
                                lean_dec(v_fst_3066_);
                                v_a_3082_ = lean_ctor_get(v___x_3070_, 0);
                                v_isSharedCheck_3089_ = (!lean_is_exclusive(v___x_3070_)) as u8;
                                if v_isSharedCheck_3089_ == 0 {
                                    v___x_3084_ = v___x_3070_;
                                    v_isShared_3085_ = v_isSharedCheck_3089_;
                                    state = 4;
                                    continue;
                                } else {
                                    lean_inc(v_a_3082_);
                                    lean_dec(v___x_3070_);
                                    v___x_3084_ = lean_box(0);
                                    v_isShared_3085_ = v_isSharedCheck_3089_;
                                    state = 4;
                                    continue;
                                }
                            }
                        } else {
                            lean_dec_ref(v___x_3058_);
                            lean_dec(v___y_3050_);
                            lean_dec_ref(v___y_3049_);
                            lean_dec(v___y_3048_);
                            lean_dec_ref(v___y_3047_);
                            lean_dec(v_snd_3036_);
                            lean_dec(v_mvarId_3024_);
                            v_a_3090_ = lean_ctor_get(v___x_3064_, 0);
                            v_isSharedCheck_3097_ = (!lean_is_exclusive(v___x_3064_)) as u8;
                            if v_isSharedCheck_3097_ == 0 {
                                v___x_3092_ = v___x_3064_;
                                v_isShared_3093_ = v_isSharedCheck_3097_;
                                state = 6;
                                continue;
                            } else {
                                lean_inc(v_a_3090_);
                                lean_dec(v___x_3064_);
                                v___x_3092_ = lean_box(0);
                                v_isShared_3093_ = v_isSharedCheck_3097_;
                                state = 6;
                                continue;
                            }
                        }
                    } else {
                        lean_dec_ref(v___x_3058_);
                        lean_dec(v___y_3050_);
                        lean_dec_ref(v___y_3049_);
                        lean_dec(v___y_3048_);
                        lean_dec_ref(v___y_3047_);
                        lean_dec_ref(v_alts_3044_);
                        lean_dec(v_snd_3036_);
                        lean_dec(v_mvarId_3024_);
                        v_a_3098_ = lean_ctor_get(v___x_3059_, 0);
                        v_isSharedCheck_3105_ = (!lean_is_exclusive(v___x_3059_)) as u8;
                        if v_isSharedCheck_3105_ == 0 {
                            v___x_3100_ = v___x_3059_;
                            v_isShared_3101_ = v_isSharedCheck_3105_;
                            state = 8;
                            continue;
                        } else {
                            lean_inc(v_a_3098_);
                            lean_dec(v___x_3059_);
                            v___x_3100_ = lean_box(0);
                            v_isShared_3101_ = v_isSharedCheck_3105_;
                            state = 8;
                            continue;
                        }
                    }
                } else {
                    lean_dec(v___y_3050_);
                    lean_dec_ref(v___y_3049_);
                    lean_dec(v___y_3048_);
                    lean_dec_ref(v___y_3047_);
                    lean_dec_ref(v_us_3046_);
                    lean_dec_ref(v_alts_3044_);
                    lean_dec_ref(v_discrs_3043_);
                    lean_dec_ref(v_params_3042_);
                    lean_dec(v_snd_3036_);
                    lean_dec(v_fst_3035_);
                    lean_dec(v_mvarId_3024_);
                    v_a_3106_ = lean_ctor_get(v___x_3051_, 0);
                    v_isSharedCheck_3113_ = (!lean_is_exclusive(v___x_3051_)) as u8;
                    if v_isSharedCheck_3113_ == 0 {
                        v___x_3108_ = v___x_3051_;
                        v_isShared_3109_ = v_isSharedCheck_3113_;
                        state = 10;
                        continue;
                    } else {
                        lean_inc(v_a_3106_);
                        lean_dec(v___x_3051_);
                        v___x_3108_ = lean_box(0);
                        v_isShared_3109_ = v_isSharedCheck_3113_;
                        state = 10;
                        continue;
                    }
                }
            }
            2 => {
                v___x_3074_ = lean_array_to_list(v_fst_3066_);
                v___x_3075_ = lean_box(0);
                v___x_3076_ = l_List_mapTR_loop___at___00Lean_Meta_Grind_casesMatch_spec__2(
                    v___x_3074_,
                    v___x_3075_,
                );
                if v_isShared_3073_ == 0 {
                    lean_ctor_set(v___x_3072_, 0, v___x_3076_);
                    v___x_3078_ = v___x_3072_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_3079_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3079_, 0, v___x_3076_);
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
                    v_reuseFailAlloc_3088_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3088_, 0, v_a_3082_);
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
                    v_reuseFailAlloc_3096_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3096_, 0, v_a_3090_);
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
                    v_reuseFailAlloc_3104_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3104_, 0, v_a_3098_);
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
                    v_reuseFailAlloc_3112_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3112_, 0, v_a_3106_);
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
                    v_reuseFailAlloc_3125_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3125_, 0, v_a_3119_);
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
                    v_reuseFailAlloc_3133_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3133_, 0, v_a_3127_);
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
                    v_reuseFailAlloc_3141_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3141_, 0, v_a_3135_);
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
                    v_reuseFailAlloc_3155_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3155_, 0, v_a_3149_);
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
    mut v_e_3157_: *mut LeanObject,
    mut v___x_3158_: *mut LeanObject,
    mut v_mvarId_3159_: *mut LeanObject,
    mut v___y_3160_: *mut LeanObject,
    mut v___y_3161_: *mut LeanObject,
    mut v___y_3162_: *mut LeanObject,
    mut v___y_3163_: *mut LeanObject,
    mut v___y_3164_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_9248__boxed_3165_: u8 = 0;
    let mut v_res_3166_: *mut LeanObject = core::ptr::null_mut();
    v___x_9248__boxed_3165_ = (lean_unbox(v___x_3158_) as u8);
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
    mut v_mvarId_3167_: *mut LeanObject,
    mut v_e_3168_: *mut LeanObject,
    mut v_a_3169_: *mut LeanObject,
    mut v_a_3170_: *mut LeanObject,
    mut v_a_3171_: *mut LeanObject,
    mut v_a_3172_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3174_: u8 = 0;
    let mut v___x_3175_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_3176_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3177_: *mut LeanObject = core::ptr::null_mut();
    v___x_3174_ = 0;
    v___x_3175_ = lean_box((v___x_3174_) as usize);
    lean_inc(v_mvarId_3167_);
    v___f_3176_ = lean_alloc_closure(
        l_Lean_Meta_Grind_casesMatch___lam__0___boxed as *mut core::ffi::c_void,
        8,
        3,
    );
    lean_closure_set(v___f_3176_, 0, v_e_3168_);
    lean_closure_set(v___f_3176_, 1, v___x_3175_);
    lean_closure_set(v___f_3176_, 2, v_mvarId_3167_);
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
    mut v_mvarId_3178_: *mut LeanObject,
    mut v_e_3179_: *mut LeanObject,
    mut v_a_3180_: *mut LeanObject,
    mut v_a_3181_: *mut LeanObject,
    mut v_a_3182_: *mut LeanObject,
    mut v_a_3183_: *mut LeanObject,
    mut v_a_3184_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3185_: *mut LeanObject = core::ptr::null_mut();
    v_res_3185_ = l_Lean_Meta_Grind_casesMatch(
        v_mvarId_3178_,
        v_e_3179_,
        v_a_3180_,
        v_a_3181_,
        v_a_3182_,
        v_a_3183_,
    );
    lean_dec(v_a_3183_);
    lean_dec_ref(v_a_3182_);
    lean_dec(v_a_3181_);
    lean_dec_ref(v_a_3180_);
    return v_res_3185_;
}
pub unsafe fn l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Meta_Grind_casesMatch_spec__0_spec__2(
    mut v_declName_3186_: *mut LeanObject,
    mut v___y_3187_: *mut LeanObject,
    mut v___y_3188_: *mut LeanObject,
    mut v___y_3189_: *mut LeanObject,
    mut v___y_3190_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3192_: *mut LeanObject = core::ptr::null_mut();
    v___x_3192_ = l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Meta_Grind_casesMatch_spec__0_spec__2___redArg(v_declName_3186_, v___y_3190_);
    return v___x_3192_;
}
pub unsafe fn l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Meta_Grind_casesMatch_spec__0_spec__2___boxed(
    mut v_declName_3193_: *mut LeanObject,
    mut v___y_3194_: *mut LeanObject,
    mut v___y_3195_: *mut LeanObject,
    mut v___y_3196_: *mut LeanObject,
    mut v___y_3197_: *mut LeanObject,
    mut v___y_3198_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3199_: *mut LeanObject = core::ptr::null_mut();
    v_res_3199_ = l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Meta_Grind_casesMatch_spec__0_spec__2(v_declName_3193_, v___y_3194_, v___y_3195_, v___y_3196_, v___y_3197_);
    lean_dec(v___y_3197_);
    lean_dec_ref(v___y_3196_);
    lean_dec(v___y_3195_);
    lean_dec_ref(v___y_3194_);
    return v_res_3199_;
}
pub unsafe fn l_Lean_MVarId_assign___at___00Lean_Meta_Grind_casesMatch_spec__1(
    mut v_mvarId_3200_: *mut LeanObject,
    mut v_val_3201_: *mut LeanObject,
    mut v___y_3202_: *mut LeanObject,
    mut v___y_3203_: *mut LeanObject,
    mut v___y_3204_: *mut LeanObject,
    mut v___y_3205_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3207_: *mut LeanObject = core::ptr::null_mut();
    v___x_3207_ = l_Lean_MVarId_assign___at___00Lean_Meta_Grind_casesMatch_spec__1___redArg(
        v_mvarId_3200_,
        v_val_3201_,
        v___y_3203_,
    );
    return v___x_3207_;
}
pub unsafe fn l_Lean_MVarId_assign___at___00Lean_Meta_Grind_casesMatch_spec__1___boxed(
    mut v_mvarId_3208_: *mut LeanObject,
    mut v_val_3209_: *mut LeanObject,
    mut v___y_3210_: *mut LeanObject,
    mut v___y_3211_: *mut LeanObject,
    mut v___y_3212_: *mut LeanObject,
    mut v___y_3213_: *mut LeanObject,
    mut v___y_3214_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3215_: *mut LeanObject = core::ptr::null_mut();
    v_res_3215_ = l_Lean_MVarId_assign___at___00Lean_Meta_Grind_casesMatch_spec__1(
        v_mvarId_3208_,
        v_val_3209_,
        v___y_3210_,
        v___y_3211_,
        v___y_3212_,
        v___y_3213_,
    );
    lean_dec(v___y_3213_);
    lean_dec_ref(v___y_3212_);
    lean_dec(v___y_3211_);
    lean_dec_ref(v___y_3210_);
    return v_res_3215_;
}
pub unsafe fn l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_casesMatch_spec__1_spec__5(
    mut v_00_u03b2_3216_: *mut LeanObject,
    mut v_x_3217_: *mut LeanObject,
    mut v_x_3218_: *mut LeanObject,
    mut v_x_3219_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3220_: *mut LeanObject = core::ptr::null_mut();
    v___x_3220_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_casesMatch_spec__1_spec__5___redArg(v_x_3217_, v_x_3218_, v_x_3219_);
    return v___x_3220_;
}
pub unsafe fn l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Meta_Grind_casesMatch_spec__0_spec__0_spec__2(
    mut v_00_u03b1_3221_: *mut LeanObject,
    mut v_constName_3222_: *mut LeanObject,
    mut v___y_3223_: *mut LeanObject,
    mut v___y_3224_: *mut LeanObject,
    mut v___y_3225_: *mut LeanObject,
    mut v___y_3226_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3228_: *mut LeanObject = core::ptr::null_mut();
    v___x_3228_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Meta_Grind_casesMatch_spec__0_spec__0_spec__2___redArg(v_constName_3222_, v___y_3223_, v___y_3224_, v___y_3225_, v___y_3226_);
    return v___x_3228_;
}
pub unsafe fn l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Meta_Grind_casesMatch_spec__0_spec__0_spec__2___boxed(
    mut v_00_u03b1_3229_: *mut LeanObject,
    mut v_constName_3230_: *mut LeanObject,
    mut v___y_3231_: *mut LeanObject,
    mut v___y_3232_: *mut LeanObject,
    mut v___y_3233_: *mut LeanObject,
    mut v___y_3234_: *mut LeanObject,
    mut v___y_3235_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3236_: *mut LeanObject = core::ptr::null_mut();
    v_res_3236_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Meta_Grind_casesMatch_spec__0_spec__0_spec__2(v_00_u03b1_3229_, v_constName_3230_, v___y_3231_, v___y_3232_, v___y_3233_, v___y_3234_);
    lean_dec(v___y_3234_);
    lean_dec_ref(v___y_3233_);
    lean_dec(v___y_3232_);
    lean_dec_ref(v___y_3231_);
    return v_res_3236_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_casesMatch_spec__1_spec__5_spec__8(
    mut v_00_u03b2_3237_: *mut LeanObject,
    mut v_x_3238_: *mut LeanObject,
    mut v_x_3239_: usize,
    mut v_x_3240_: usize,
    mut v_x_3241_: *mut LeanObject,
    mut v_x_3242_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3243_: *mut LeanObject = core::ptr::null_mut();
    v___x_3243_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_casesMatch_spec__1_spec__5_spec__8___redArg(v_x_3238_, v_x_3239_, v_x_3240_, v_x_3241_, v_x_3242_);
    return v___x_3243_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_casesMatch_spec__1_spec__5_spec__8___boxed(
    mut v_00_u03b2_3244_: *mut LeanObject,
    mut v_x_3245_: *mut LeanObject,
    mut v_x_3246_: *mut LeanObject,
    mut v_x_3247_: *mut LeanObject,
    mut v_x_3248_: *mut LeanObject,
    mut v_x_3249_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_x_9585__boxed_3250_: usize = 0;
    let mut v_x_9586__boxed_3251_: usize = 0;
    let mut v_res_3252_: *mut LeanObject = core::ptr::null_mut();
    v_x_9585__boxed_3250_ = lean_unbox_usize(v_x_3246_);
    lean_dec(v_x_3246_);
    v_x_9586__boxed_3251_ = lean_unbox_usize(v_x_3247_);
    lean_dec(v_x_3247_);
    v_res_3252_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_casesMatch_spec__1_spec__5_spec__8(v_00_u03b2_3244_, v_x_3245_, v_x_9585__boxed_3250_, v_x_9586__boxed_3251_, v_x_3248_, v_x_3249_);
    return v_res_3252_;
}
pub unsafe fn l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Meta_Grind_casesMatch_spec__0_spec__0_spec__2_spec__7(
    mut v_00_u03b1_3253_: *mut LeanObject,
    mut v_ref_3254_: *mut LeanObject,
    mut v_constName_3255_: *mut LeanObject,
    mut v___y_3256_: *mut LeanObject,
    mut v___y_3257_: *mut LeanObject,
    mut v___y_3258_: *mut LeanObject,
    mut v___y_3259_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3261_: *mut LeanObject = core::ptr::null_mut();
    v___x_3261_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Meta_Grind_casesMatch_spec__0_spec__0_spec__2_spec__7___redArg(v_ref_3254_, v_constName_3255_, v___y_3256_, v___y_3257_, v___y_3258_, v___y_3259_);
    return v___x_3261_;
}
pub unsafe fn l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Meta_Grind_casesMatch_spec__0_spec__0_spec__2_spec__7___boxed(
    mut v_00_u03b1_3262_: *mut LeanObject,
    mut v_ref_3263_: *mut LeanObject,
    mut v_constName_3264_: *mut LeanObject,
    mut v___y_3265_: *mut LeanObject,
    mut v___y_3266_: *mut LeanObject,
    mut v___y_3267_: *mut LeanObject,
    mut v___y_3268_: *mut LeanObject,
    mut v___y_3269_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3270_: *mut LeanObject = core::ptr::null_mut();
    v_res_3270_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Meta_Grind_casesMatch_spec__0_spec__0_spec__2_spec__7(v_00_u03b1_3262_, v_ref_3263_, v_constName_3264_, v___y_3265_, v___y_3266_, v___y_3267_, v___y_3268_);
    lean_dec(v___y_3268_);
    lean_dec_ref(v___y_3267_);
    lean_dec(v___y_3266_);
    lean_dec_ref(v___y_3265_);
    lean_dec(v_ref_3263_);
    return v_res_3270_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_casesMatch_spec__1_spec__5_spec__8_spec__11(
    mut v_00_u03b2_3271_: *mut LeanObject,
    mut v_n_3272_: *mut LeanObject,
    mut v_k_3273_: *mut LeanObject,
    mut v_v_3274_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3275_: *mut LeanObject = core::ptr::null_mut();
    v___x_3275_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_casesMatch_spec__1_spec__5_spec__8_spec__11___redArg(v_n_3272_, v_k_3273_, v_v_3274_);
    return v___x_3275_;
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_casesMatch_spec__1_spec__5_spec__8_spec__12(
    mut v_00_u03b2_3276_: *mut LeanObject,
    mut v_depth_3277_: usize,
    mut v_keys_3278_: *mut LeanObject,
    mut v_vals_3279_: *mut LeanObject,
    mut v_heq_3280_: *mut LeanObject,
    mut v_i_3281_: *mut LeanObject,
    mut v_entries_3282_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3283_: *mut LeanObject = core::ptr::null_mut();
    v___x_3283_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_casesMatch_spec__1_spec__5_spec__8_spec__12___redArg(v_depth_3277_, v_keys_3278_, v_vals_3279_, v_i_3281_, v_entries_3282_);
    return v___x_3283_;
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_casesMatch_spec__1_spec__5_spec__8_spec__12___boxed(
    mut v_00_u03b2_3284_: *mut LeanObject,
    mut v_depth_3285_: *mut LeanObject,
    mut v_keys_3286_: *mut LeanObject,
    mut v_vals_3287_: *mut LeanObject,
    mut v_heq_3288_: *mut LeanObject,
    mut v_i_3289_: *mut LeanObject,
    mut v_entries_3290_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_depth_boxed_3291_: usize = 0;
    let mut v_res_3292_: *mut LeanObject = core::ptr::null_mut();
    v_depth_boxed_3291_ = lean_unbox_usize(v_depth_3285_);
    lean_dec(v_depth_3285_);
    v_res_3292_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_casesMatch_spec__1_spec__5_spec__8_spec__12(v_00_u03b2_3284_, v_depth_boxed_3291_, v_keys_3286_, v_vals_3287_, v_heq_3288_, v_i_3289_, v_entries_3290_);
    lean_dec_ref(v_vals_3287_);
    lean_dec_ref(v_keys_3286_);
    return v_res_3292_;
}
pub unsafe fn l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Meta_Grind_casesMatch_spec__0_spec__0_spec__2_spec__7_spec__10(
    mut v_00_u03b1_3293_: *mut LeanObject,
    mut v_ref_3294_: *mut LeanObject,
    mut v_msg_3295_: *mut LeanObject,
    mut v_declHint_3296_: *mut LeanObject,
    mut v___y_3297_: *mut LeanObject,
    mut v___y_3298_: *mut LeanObject,
    mut v___y_3299_: *mut LeanObject,
    mut v___y_3300_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3302_: *mut LeanObject = core::ptr::null_mut();
    v___x_3302_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Meta_Grind_casesMatch_spec__0_spec__0_spec__2_spec__7_spec__10___redArg(v_ref_3294_, v_msg_3295_, v_declHint_3296_, v___y_3297_, v___y_3298_, v___y_3299_, v___y_3300_);
    return v___x_3302_;
}
pub unsafe fn l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Meta_Grind_casesMatch_spec__0_spec__0_spec__2_spec__7_spec__10___boxed(
    mut v_00_u03b1_3303_: *mut LeanObject,
    mut v_ref_3304_: *mut LeanObject,
    mut v_msg_3305_: *mut LeanObject,
    mut v_declHint_3306_: *mut LeanObject,
    mut v___y_3307_: *mut LeanObject,
    mut v___y_3308_: *mut LeanObject,
    mut v___y_3309_: *mut LeanObject,
    mut v___y_3310_: *mut LeanObject,
    mut v___y_3311_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3312_: *mut LeanObject = core::ptr::null_mut();
    v_res_3312_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Meta_Grind_casesMatch_spec__0_spec__0_spec__2_spec__7_spec__10(v_00_u03b1_3303_, v_ref_3304_, v_msg_3305_, v_declHint_3306_, v___y_3307_, v___y_3308_, v___y_3309_, v___y_3310_);
    lean_dec(v___y_3310_);
    lean_dec_ref(v___y_3309_);
    lean_dec(v___y_3308_);
    lean_dec_ref(v___y_3307_);
    lean_dec(v_ref_3304_);
    return v_res_3312_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_casesMatch_spec__1_spec__5_spec__8_spec__11_spec__13(
    mut v_00_u03b2_3313_: *mut LeanObject,
    mut v_x_3314_: *mut LeanObject,
    mut v_x_3315_: *mut LeanObject,
    mut v_x_3316_: *mut LeanObject,
    mut v_x_3317_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3318_: *mut LeanObject = core::ptr::null_mut();
    v___x_3318_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_casesMatch_spec__1_spec__5_spec__8_spec__11_spec__13___redArg(v_x_3314_, v_x_3315_, v_x_3316_, v_x_3317_);
    return v___x_3318_;
}
pub unsafe fn l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Meta_Grind_casesMatch_spec__0_spec__0_spec__2_spec__7_spec__10_spec__12_spec__15(
    mut v_msg_3319_: *mut LeanObject,
    mut v_declHint_3320_: *mut LeanObject,
    mut v___y_3321_: *mut LeanObject,
    mut v___y_3322_: *mut LeanObject,
    mut v___y_3323_: *mut LeanObject,
    mut v___y_3324_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3326_: *mut LeanObject = core::ptr::null_mut();
    v___x_3326_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Meta_Grind_casesMatch_spec__0_spec__0_spec__2_spec__7_spec__10_spec__12_spec__15___redArg(v_msg_3319_, v_declHint_3320_, v___y_3324_);
    return v___x_3326_;
}
pub unsafe fn l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Meta_Grind_casesMatch_spec__0_spec__0_spec__2_spec__7_spec__10_spec__12_spec__15___boxed(
    mut v_msg_3327_: *mut LeanObject,
    mut v_declHint_3328_: *mut LeanObject,
    mut v___y_3329_: *mut LeanObject,
    mut v___y_3330_: *mut LeanObject,
    mut v___y_3331_: *mut LeanObject,
    mut v___y_3332_: *mut LeanObject,
    mut v___y_3333_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3334_: *mut LeanObject = core::ptr::null_mut();
    v_res_3334_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Meta_Grind_casesMatch_spec__0_spec__0_spec__2_spec__7_spec__10_spec__12_spec__15(v_msg_3327_, v_declHint_3328_, v___y_3329_, v___y_3330_, v___y_3331_, v___y_3332_);
    lean_dec(v___y_3332_);
    lean_dec_ref(v___y_3331_);
    lean_dec(v___y_3330_);
    lean_dec_ref(v___y_3329_);
    return v_res_3334_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Meta_Grind_casesMatch_spec__0_spec__0_spec__2_spec__7_spec__10_spec__13(
    mut v_00_u03b1_3335_: *mut LeanObject,
    mut v_ref_3336_: *mut LeanObject,
    mut v_msg_3337_: *mut LeanObject,
    mut v___y_3338_: *mut LeanObject,
    mut v___y_3339_: *mut LeanObject,
    mut v___y_3340_: *mut LeanObject,
    mut v___y_3341_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3343_: *mut LeanObject = core::ptr::null_mut();
    v___x_3343_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Meta_Grind_casesMatch_spec__0_spec__0_spec__2_spec__7_spec__10_spec__13___redArg(v_ref_3336_, v_msg_3337_, v___y_3338_, v___y_3339_, v___y_3340_, v___y_3341_);
    return v___x_3343_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Meta_Grind_casesMatch_spec__0_spec__0_spec__2_spec__7_spec__10_spec__13___boxed(
    mut v_00_u03b1_3344_: *mut LeanObject,
    mut v_ref_3345_: *mut LeanObject,
    mut v_msg_3346_: *mut LeanObject,
    mut v___y_3347_: *mut LeanObject,
    mut v___y_3348_: *mut LeanObject,
    mut v___y_3349_: *mut LeanObject,
    mut v___y_3350_: *mut LeanObject,
    mut v___y_3351_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3352_: *mut LeanObject = core::ptr::null_mut();
    v_res_3352_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Meta_Grind_casesMatch_spec__0_spec__0_spec__2_spec__7_spec__10_spec__13(v_00_u03b1_3344_, v_ref_3345_, v_msg_3346_, v___y_3347_, v___y_3348_, v___y_3349_, v___y_3350_);
    lean_dec(v___y_3350_);
    lean_dec_ref(v___y_3349_);
    lean_dec(v___y_3348_);
    lean_dec_ref(v___y_3347_);
    lean_dec(v_ref_3345_);
    return v_res_3352_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Meta_Grind_casesMatch_spec__0_spec__0_spec__2_spec__7_spec__10_spec__13_spec__17(
    mut v_00_u03b1_3353_: *mut LeanObject,
    mut v_msg_3354_: *mut LeanObject,
    mut v___y_3355_: *mut LeanObject,
    mut v___y_3356_: *mut LeanObject,
    mut v___y_3357_: *mut LeanObject,
    mut v___y_3358_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3360_: *mut LeanObject = core::ptr::null_mut();
    v___x_3360_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Meta_Grind_casesMatch_spec__0_spec__0_spec__2_spec__7_spec__10_spec__13_spec__17___redArg(v_msg_3354_, v___y_3355_, v___y_3356_, v___y_3357_, v___y_3358_);
    return v___x_3360_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Meta_Grind_casesMatch_spec__0_spec__0_spec__2_spec__7_spec__10_spec__13_spec__17___boxed(
    mut v_00_u03b1_3361_: *mut LeanObject,
    mut v_msg_3362_: *mut LeanObject,
    mut v___y_3363_: *mut LeanObject,
    mut v___y_3364_: *mut LeanObject,
    mut v___y_3365_: *mut LeanObject,
    mut v___y_3366_: *mut LeanObject,
    mut v___y_3367_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3368_: *mut LeanObject = core::ptr::null_mut();
    v_res_3368_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00Lean_Meta_Grind_casesMatch_spec__0_spec__0_spec__2_spec__7_spec__10_spec__13_spec__17(v_00_u03b1_3361_, v_msg_3362_, v___y_3363_, v___y_3364_, v___y_3365_, v___y_3366_);
    lean_dec(v___y_3366_);
    lean_dec_ref(v___y_3365_);
    lean_dec(v___y_3364_);
    lean_dec_ref(v___y_3363_);
    return v_res_3368_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Meta_Tactic_Grind_CasesMatch(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Meta_Tactic_Util(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Grind_Util(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Match_MatcherApp(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Cases(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Meta_Tactic_Grind_CasesMatch(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Meta_Tactic_Grind_CasesMatch(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Meta_Tactic_Util(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Meta_Tactic_Grind_Util(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Meta_Match_MatcherApp(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Meta_Tactic_Cases(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Grind_CasesMatch(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Lean_Meta_Tactic_Grind_CasesMatch(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Lean_Meta_Tactic_Grind_CasesMatch(builtin);
}
