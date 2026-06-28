// Lean compiler output
// Module: Lean.Elab.Tactic.Conv.Pattern
// Imports: Lean.Elab.Tactic.Simp Lean.Elab.Tactic.Conv.Basic
use crate::r#gen::Init::Data::List::Basic::{l_List_getLast_x3f___redArg, l_List_isEmpty___redArg};
use crate::r#gen::Init::Data::Repr::l_Nat_reprFast;
use crate::r#gen::Init::Meta::Defs::{l_Lean_Syntax_isNone, l_Lean_TSyntax_getNat};
use crate::r#gen::Init::MetaTypes::l_Lean_Meta_Simp_neutralConfig;
use crate::r#gen::Init::Prelude::{
    l_Lean_Name_mkStr5, l_Lean_Syntax_getArg, l_Lean_Syntax_getArgs, l_Lean_Syntax_isOfKind,
    l_Lean_Syntax_matchesNull, l_Lean_replaceRef,
};
use crate::r#gen::Lean::Data::Options::l_Lean_Options_empty;
use crate::r#gen::Lean::Data::PersistentHashMap::{
    l_Lean_PersistentHashMap_getCollisionNodeSize___redArg,
    l_Lean_PersistentHashMap_mkCollisionNode___redArg, l_Lean_PersistentHashMap_mkEmptyEntries,
    l_Lean_PersistentHashMap_mkEmptyEntriesArray,
};
use crate::r#gen::Lean::DeclarationRange::l_Lean_addBuiltinDeclarationRanges;
use crate::r#gen::Lean::Elab::Exception::l_Lean_Elab_unsupportedSyntaxExceptionId;
use crate::r#gen::Lean::Elab::Tactic::Basic::{
    l_Lean_Elab_Tactic_getMainGoal___redArg, l_Lean_Elab_Tactic_replaceMainGoal___redArg,
    l_Lean_Elab_Tactic_tacticElabAttribute, l_Lean_Elab_Tactic_withMainContext___redArg,
};
use crate::r#gen::Lean::Elab::Tactic::Conv::Basic::{
    initialize_Lean_Elab_Tactic_Conv_Basic, l_Lean_Elab_Tactic_Conv_getLhs___redArg,
    l_Lean_Elab_Tactic_Conv_getRhs___redArg, l_Lean_Elab_Tactic_Conv_mkConvGoalFor,
    runtime_initialize_Lean_Elab_Tactic_Conv_Basic,
};
use crate::r#gen::Lean::Elab::Tactic::Simp::{
    initialize_Lean_Elab_Tactic_Simp, runtime_initialize_Lean_Elab_Tactic_Simp,
};
use crate::r#gen::Lean::Elab::Term::TermElabM::{
    l_Lean_Elab_Term_elabTerm, l_Lean_Elab_Term_withoutErrToSorryImp___redArg,
    l_Lean_Elab_Term_withoutModifyingElabMetaStateWithInfo___redArg,
};
use crate::r#gen::Lean::Expr::{
    l_Lean_Expr_appArg_x21, l_Lean_Expr_appFn_x21, l_Lean_Expr_isApp, l_Lean_Expr_mvarId_x21,
    l_Lean_instBEqMVarId_beq, l_Lean_instHashableMVarId_hash, l_Lean_mkAppN,
};
use crate::r#gen::Lean::HeadIndex::{l_Lean_Expr_toHeadIndex, l_Lean_instBEqHeadIndex_beq};
use crate::r#gen::Lean::KeyedDeclsAttribute::l_Lean_KeyedDeclsAttribute_addBuiltin___redArg;
use crate::r#gen::Lean::Message::{
    l_Lean_MessageData_ofFormat, l_Lean_indentExpr, l_Lean_stringToMessageData,
};
use crate::r#gen::Lean::Meta::AbstractMVars::{
    l_Lean_Meta_abstractMVars, l_Lean_Meta_openAbstractMVarsResult,
};
use crate::r#gen::Lean::Meta::AppBuilder::l_Lean_Meta_mkCongrFun;
use crate::r#gen::Lean::Meta::Basic::{
    l___private_Lean_Meta_Basic_0__Lean_Meta_withNewMCtxDepthImp, l_Lean_Meta_Context_config,
    l_Lean_Meta_Context_configKey, l_Lean_Meta_TransparencyMode_toUInt64,
    l_Lean_Meta_isExprDefEqGuarded,
};
use crate::r#gen::Lean::Meta::Tactic::Simp::Main::l_Lean_Meta_Simp_main;
use crate::r#gen::Lean::Meta::Tactic::Simp::SimpCongrTheorems::l_Lean_Meta_getSimpCongrTheorems___redArg;
use crate::r#gen::Lean::Meta::Tactic::Simp::Types::{
    l_Lean_Meta_Simp_Context_setMemoize, l_Lean_Meta_Simp_Result_getProof,
    l_Lean_Meta_Simp_mkContext___redArg,
};
use crate::lean_imports_rs::Init::Data::Array::Basic::{
    lean_array_fswap, lean_array_size, lean_array_uget_borrowed, lean_array_uset,
};
use crate::lean_imports_rs::Init::Data::Array::Set::lean_array_fset;
use crate::lean_imports_rs::Init::Data::Nat::Bitwise::Basic::lean_nat_shiftr;
use crate::lean_imports_rs::Init::Data::UInt::Basic::{
    lean_uint64_lor, lean_uint64_shift_left, lean_uint64_shift_right, lean_uint64_to_usize,
    lean_usize_land, lean_usize_mul, lean_usize_shift_left, lean_usize_shift_right,
};
use crate::lean_imports_rs::Init::Data::UInt::BasicAux::{
    lean_usize_add, lean_usize_dec_le, lean_usize_dec_lt, lean_usize_sub, lean_usize_to_nat,
};
use crate::lean_imports_rs::Init::Prelude::{
    lean_array_fget, lean_array_fget_borrowed, lean_array_get_size, lean_array_push,
    lean_array_to_list, lean_mk_empty_array_with_capacity, lean_nat_add, lean_nat_dec_eq,
    lean_nat_dec_le, lean_nat_dec_lt, lean_nat_sub,
};
use crate::lean_imports_rs::Init::System::ST::{
    lean_st_mk_ref, lean_st_ref_get, lean_st_ref_set, lean_st_ref_take,
};
pub static l___private_Lean_Elab_Tactic_Conv_Pattern_0__Lean_Elab_Tactic_Conv_getContext___redArg___closed__0_value: crate::leanh::LeanArrayObject<0> = crate::leanh::LeanArrayObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 246 }, m_size: 0, m_capacity: 0, m_data: [] };
static mut l___private_Lean_Elab_Tactic_Conv_Pattern_0__Lean_Elab_Tactic_Conv_getContext___redArg___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Pattern_0__Lean_Elab_Tactic_Conv_getContext___redArg___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Conv_Pattern_0__Lean_Elab_Tactic_Conv_matchPattern_x3f_go_x3f___closed__0_value: crate::leanh::LeanArrayObject<0> = crate::leanh::LeanArrayObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 246 }, m_size: 0, m_capacity: 0, m_data: [] };
static mut l___private_Lean_Elab_Tactic_Conv_Pattern_0__Lean_Elab_Tactic_Conv_matchPattern_x3f_go_x3f___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Pattern_0__Lean_Elab_Tactic_Conv_matchPattern_x3f_go_x3f___closed__0_value) as *mut crate::leanh::LeanObject;
static mut l_Lean_Elab_Tactic_Conv_matchPattern_x3f___lam__0___closed__0_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_Tactic_Conv_matchPattern_x3f___lam__0___closed__0: u64 = 0;
pub static l___private_Lean_Elab_Tactic_Conv_Pattern_0__Lean_Elab_Tactic_Conv_pre___closed__0_value: crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 2 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_Conv_Pattern_0__Lean_Elab_Tactic_Conv_pre___closed__0:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Elab_Tactic_Conv_Pattern_0__Lean_Elab_Tactic_Conv_pre___closed__0_value
) as *mut crate::leanh::LeanObject;
static mut l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__0___redArg___closed__0_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__0___redArg___closed__0: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__3_spec__3_spec__4___redArg___closed__0_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__3_spec__3_spec__4___redArg___closed__0: usize = 0;
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__3_spec__3_spec__4___redArg___closed__1_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__3_spec__3_spec__4___redArg___closed__1: usize = 0;
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__3_spec__3_spec__4___redArg___closed__2_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__3_spec__3_spec__4___redArg___closed__2: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Array_mapFinIdxM_map___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__7___redArg___closed__0_value: crate::leanh::LeanStringObject<26> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 26, m_capacity: 26, m_length: 25, m_data: [112, 111, 115, 105, 116, 105, 118, 101, 32, 105, 110, 116, 101, 103, 101, 114, 32, 101, 120, 112, 101, 99, 116, 101, 100, 0]};
static mut l_Array_mapFinIdxM_map___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__7___redArg___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Array_mapFinIdxM_map___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__7___redArg___closed__0_value) as *mut crate::leanh::LeanObject;
static mut l_Array_mapFinIdxM_map___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__7___redArg___closed__1_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Array_mapFinIdxM_map___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__7___redArg___closed__1: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__0_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__1_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__2_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__3_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__4_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__5_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__6_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__6: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__7_value:
    crate::leanh::LeanStringObject<52> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 52,
    m_capacity: 52,
    m_length: 51,
    m_data: [
        39, 112, 97, 116, 116, 101, 114, 110, 39, 32, 99, 111, 110, 118, 32, 116, 97, 99, 116, 105,
        99, 32, 102, 97, 105, 108, 101, 100, 44, 32, 112, 97, 116, 116, 101, 114, 110, 32, 119, 97,
        115, 32, 110, 111, 116, 32, 102, 111, 117, 110, 100, 0,
    ],
};
static mut l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__7: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__7_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__8_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__8: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__9_value:
    crate::leanh::LeanStringObject<54> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 54,
    m_capacity: 54,
    m_length: 53,
    m_data: [
        39, 112, 97, 116, 116, 101, 114, 110, 39, 32, 99, 111, 110, 118, 32, 116, 97, 99, 116, 105,
        99, 32, 102, 97, 105, 108, 101, 100, 44, 32, 112, 97, 116, 116, 101, 114, 110, 32, 119, 97,
        115, 32, 102, 111, 117, 110, 100, 32, 111, 110, 108, 121, 32, 0,
    ],
};
static mut l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__9: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__9_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__10_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__10:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__11_value:
    crate::leanh::LeanStringObject<12> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 12,
    m_capacity: 12,
    m_length: 11,
    m_data: [32, 116, 105, 109, 101, 115, 32, 98, 117, 116, 32, 0],
};
static mut l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__11:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__11_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__12_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__12:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__13_value:
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
    m_data: [32, 101, 120, 112, 101, 99, 116, 101, 100, 0],
};
static mut l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__13:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__13_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__14_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__14:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__15_value:
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
static mut l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__15:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__15_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__16_value:
    crate::leanh::LeanStringObject<32> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 32,
    m_capacity: 32,
    m_length: 31,
    m_data: [
        111, 99, 99, 117, 114, 114, 101, 110, 99, 101, 32, 108, 105, 115, 116, 32, 105, 115, 32,
        110, 111, 116, 32, 100, 105, 115, 116, 105, 110, 99, 116, 0,
    ],
};
static mut l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__16:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__16_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__17_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__17:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__18_value:
    crate::leanh::LeanClosureObject<1> = crate::leanh::LeanClosureObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_Elab_Tactic_Conv_evalPattern___lam__4___boxed as *const core::ffi::c_void,
    m_arity: 10,
    m_num_fixed: 1,
    m_objs: [(((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject],
};
static mut l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__18:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__18_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__19_value:
    crate::leanh::LeanClosureObject<1> = crate::leanh::LeanClosureObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_Elab_Tactic_Conv_evalPattern___lam__5___boxed as *const core::ffi::c_void,
    m_arity: 10,
    m_num_fixed: 1,
    m_objs: [(((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject],
};
static mut l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__19:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__19_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__20_value:
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
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__20:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__20_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__21_value:
    crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__20_value)
            as *mut crate::leanh::LeanObject,
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__21:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__21_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__22_value:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__15_value)
            as *mut crate::leanh::LeanObject,
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__21_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__22:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__22_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__23_value:
    crate::leanh::LeanStringObject<13> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 13,
    m_capacity: 13,
    m_length: 12,
    m_data: [111, 99, 99, 115, 87, 105, 108, 100, 99, 97, 114, 100, 0],
};
static mut l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__23:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__23_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__24_value:
    crate::leanh::LeanStringObject<12> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 12,
    m_capacity: 12,
    m_length: 11,
    m_data: [111, 99, 99, 115, 73, 110, 100, 101, 120, 101, 100, 0],
};
static mut l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__24:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__24_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__25_value:
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
static mut l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__25:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__25_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__26_value:
    crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 0,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__25_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__26:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__26_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__27_value:
    crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 5,
    m_capacity: 5,
    m_length: 4,
    m_data: [111, 99, 99, 115, 0],
};
static mut l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__27:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__27_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Tactic_Conv_evalPattern___closed__0_value: crate::leanh::LeanClosureObject<
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
    m_fun: l_Lean_Elab_Tactic_Conv_evalPattern___lam__0___boxed as *const core::ffi::c_void,
    m_arity: 9,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Elab_Tactic_Conv_evalPattern___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Conv_evalPattern___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Tactic_Conv_evalPattern___closed__1_value: crate::leanh::LeanStringObject<
    5,
> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 5,
    m_capacity: 5,
    m_length: 4,
    m_data: [76, 101, 97, 110, 0],
};
static mut l_Lean_Elab_Tactic_Conv_evalPattern___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Conv_evalPattern___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Tactic_Conv_evalPattern___closed__2_value: crate::leanh::LeanStringObject<
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
    m_data: [80, 97, 114, 115, 101, 114, 0],
};
static mut l_Lean_Elab_Tactic_Conv_evalPattern___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Conv_evalPattern___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Tactic_Conv_evalPattern___closed__3_value: crate::leanh::LeanStringObject<
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
    m_data: [84, 97, 99, 116, 105, 99, 0],
};
static mut l_Lean_Elab_Tactic_Conv_evalPattern___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Conv_evalPattern___closed__3_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Tactic_Conv_evalPattern___closed__4_value: crate::leanh::LeanStringObject<
    5,
> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 5,
    m_capacity: 5,
    m_length: 4,
    m_data: [67, 111, 110, 118, 0],
};
static mut l_Lean_Elab_Tactic_Conv_evalPattern___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Conv_evalPattern___closed__4_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Tactic_Conv_evalPattern___closed__5_value: crate::leanh::LeanStringObject<
    8,
> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 8,
    m_capacity: 8,
    m_length: 7,
    m_data: [112, 97, 116, 116, 101, 114, 110, 0],
};
static mut l_Lean_Elab_Tactic_Conv_evalPattern___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Conv_evalPattern___closed__5_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Elab_Tactic_Conv_evalPattern___closed__6_value_aux_0: crate::leanh::LeanCtorObject<
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
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Conv_evalPattern___closed__1_value)
            as *mut crate::leanh::LeanObject,
        11948124481539785030 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Elab_Tactic_Conv_evalPattern___closed__6_value_aux_1: crate::leanh::LeanCtorObject<
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
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Conv_evalPattern___closed__6_value_aux_0)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Conv_evalPattern___closed__2_value)
            as *mut crate::leanh::LeanObject,
        8018486133748762727 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Elab_Tactic_Conv_evalPattern___closed__6_value_aux_2: crate::leanh::LeanCtorObject<
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
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Conv_evalPattern___closed__6_value_aux_1)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Conv_evalPattern___closed__3_value)
            as *mut crate::leanh::LeanObject,
        18344149449936419494 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Elab_Tactic_Conv_evalPattern___closed__6_value_aux_3: crate::leanh::LeanCtorObject<
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
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Conv_evalPattern___closed__6_value_aux_2)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Conv_evalPattern___closed__4_value)
            as *mut crate::leanh::LeanObject,
        2622230176999461939 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Lean_Elab_Tactic_Conv_evalPattern___closed__6_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Tactic_Conv_evalPattern___closed__6_value_aux_3)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Tactic_Conv_evalPattern___closed__5_value)
                as *mut crate::leanh::LeanObject,
            3861856325106436923 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Elab_Tactic_Conv_evalPattern___closed__6: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Conv_evalPattern___closed__6_value)
        as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Conv_Pattern_0__Lean_Elab_Tactic_Conv_evalPattern___regBuiltin_Lean_Elab_Tactic_Conv_evalPattern__1___closed__0_value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [69, 108, 97, 98, 0]};
static mut l___private_Lean_Elab_Tactic_Conv_Pattern_0__Lean_Elab_Tactic_Conv_evalPattern___regBuiltin_Lean_Elab_Tactic_Conv_evalPattern__1___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Pattern_0__Lean_Elab_Tactic_Conv_evalPattern___regBuiltin_Lean_Elab_Tactic_Conv_evalPattern__1___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Conv_Pattern_0__Lean_Elab_Tactic_Conv_evalPattern___regBuiltin_Lean_Elab_Tactic_Conv_evalPattern__1___closed__1_value: crate::leanh::LeanStringObject<12> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 12, m_capacity: 12, m_length: 11, m_data: [101, 118, 97, 108, 80, 97, 116, 116, 101, 114, 110, 0]};
static mut l___private_Lean_Elab_Tactic_Conv_Pattern_0__Lean_Elab_Tactic_Conv_evalPattern___regBuiltin_Lean_Elab_Tactic_Conv_evalPattern__1___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Pattern_0__Lean_Elab_Tactic_Conv_evalPattern___regBuiltin_Lean_Elab_Tactic_Conv_evalPattern__1___closed__1_value) as *mut crate::leanh::LeanObject;
static l___private_Lean_Elab_Tactic_Conv_Pattern_0__Lean_Elab_Tactic_Conv_evalPattern___regBuiltin_Lean_Elab_Tactic_Conv_evalPattern__1___closed__2_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Elab_Tactic_Conv_evalPattern___closed__1_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Elab_Tactic_Conv_Pattern_0__Lean_Elab_Tactic_Conv_evalPattern___regBuiltin_Lean_Elab_Tactic_Conv_evalPattern__1___closed__2_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Pattern_0__Lean_Elab_Tactic_Conv_evalPattern___regBuiltin_Lean_Elab_Tactic_Conv_evalPattern__1___closed__2_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Pattern_0__Lean_Elab_Tactic_Conv_evalPattern___regBuiltin_Lean_Elab_Tactic_Conv_evalPattern__1___closed__0_value) as *mut crate::leanh::LeanObject,11510100434945111860 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Elab_Tactic_Conv_Pattern_0__Lean_Elab_Tactic_Conv_evalPattern___regBuiltin_Lean_Elab_Tactic_Conv_evalPattern__1___closed__2_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Pattern_0__Lean_Elab_Tactic_Conv_evalPattern___regBuiltin_Lean_Elab_Tactic_Conv_evalPattern__1___closed__2_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Elab_Tactic_Conv_evalPattern___closed__3_value) as *mut crate::leanh::LeanObject,12733524109236233889 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Elab_Tactic_Conv_Pattern_0__Lean_Elab_Tactic_Conv_evalPattern___regBuiltin_Lean_Elab_Tactic_Conv_evalPattern__1___closed__2_value_aux_3: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Pattern_0__Lean_Elab_Tactic_Conv_evalPattern___regBuiltin_Lean_Elab_Tactic_Conv_evalPattern__1___closed__2_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Elab_Tactic_Conv_evalPattern___closed__4_value) as *mut crate::leanh::LeanObject,9299793053028177184 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Elab_Tactic_Conv_Pattern_0__Lean_Elab_Tactic_Conv_evalPattern___regBuiltin_Lean_Elab_Tactic_Conv_evalPattern__1___closed__2_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Pattern_0__Lean_Elab_Tactic_Conv_evalPattern___regBuiltin_Lean_Elab_Tactic_Conv_evalPattern__1___closed__2_value_aux_3) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Pattern_0__Lean_Elab_Tactic_Conv_evalPattern___regBuiltin_Lean_Elab_Tactic_Conv_evalPattern__1___closed__1_value) as *mut crate::leanh::LeanObject,6508700515234341467 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_Conv_Pattern_0__Lean_Elab_Tactic_Conv_evalPattern___regBuiltin_Lean_Elab_Tactic_Conv_evalPattern__1___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Pattern_0__Lean_Elab_Tactic_Conv_evalPattern___regBuiltin_Lean_Elab_Tactic_Conv_evalPattern__1___closed__2_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Conv_Pattern_0__Lean_Elab_Tactic_Conv_evalPattern___regBuiltin_Lean_Elab_Tactic_Conv_evalPattern_declRange__3___closed__0_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 105 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,((( 50 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_Conv_Pattern_0__Lean_Elab_Tactic_Conv_evalPattern___regBuiltin_Lean_Elab_Tactic_Conv_evalPattern_declRange__3___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Pattern_0__Lean_Elab_Tactic_Conv_evalPattern___regBuiltin_Lean_Elab_Tactic_Conv_evalPattern_declRange__3___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Conv_Pattern_0__Lean_Elab_Tactic_Conv_evalPattern___regBuiltin_Lean_Elab_Tactic_Conv_evalPattern_declRange__3___closed__1_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 142 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,((( 31 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_Conv_Pattern_0__Lean_Elab_Tactic_Conv_evalPattern___regBuiltin_Lean_Elab_Tactic_Conv_evalPattern_declRange__3___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Pattern_0__Lean_Elab_Tactic_Conv_evalPattern___regBuiltin_Lean_Elab_Tactic_Conv_evalPattern_declRange__3___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Conv_Pattern_0__Lean_Elab_Tactic_Conv_evalPattern___regBuiltin_Lean_Elab_Tactic_Conv_evalPattern_declRange__3___closed__2_value: crate::leanh::LeanCtorObject<4> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*4 + 0) as u16, other: 4, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Pattern_0__Lean_Elab_Tactic_Conv_evalPattern___regBuiltin_Lean_Elab_Tactic_Conv_evalPattern_declRange__3___closed__0_value) as *mut crate::leanh::LeanObject,((( 50 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Pattern_0__Lean_Elab_Tactic_Conv_evalPattern___regBuiltin_Lean_Elab_Tactic_Conv_evalPattern_declRange__3___closed__1_value) as *mut crate::leanh::LeanObject,((( 31 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_Conv_Pattern_0__Lean_Elab_Tactic_Conv_evalPattern___regBuiltin_Lean_Elab_Tactic_Conv_evalPattern_declRange__3___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Pattern_0__Lean_Elab_Tactic_Conv_evalPattern___regBuiltin_Lean_Elab_Tactic_Conv_evalPattern_declRange__3___closed__2_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Conv_Pattern_0__Lean_Elab_Tactic_Conv_evalPattern___regBuiltin_Lean_Elab_Tactic_Conv_evalPattern_declRange__3___closed__3_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 105 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,((( 54 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_Conv_Pattern_0__Lean_Elab_Tactic_Conv_evalPattern___regBuiltin_Lean_Elab_Tactic_Conv_evalPattern_declRange__3___closed__3: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Pattern_0__Lean_Elab_Tactic_Conv_evalPattern___regBuiltin_Lean_Elab_Tactic_Conv_evalPattern_declRange__3___closed__3_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Conv_Pattern_0__Lean_Elab_Tactic_Conv_evalPattern___regBuiltin_Lean_Elab_Tactic_Conv_evalPattern_declRange__3___closed__4_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 105 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,((( 65 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_Conv_Pattern_0__Lean_Elab_Tactic_Conv_evalPattern___regBuiltin_Lean_Elab_Tactic_Conv_evalPattern_declRange__3___closed__4: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Pattern_0__Lean_Elab_Tactic_Conv_evalPattern___regBuiltin_Lean_Elab_Tactic_Conv_evalPattern_declRange__3___closed__4_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Conv_Pattern_0__Lean_Elab_Tactic_Conv_evalPattern___regBuiltin_Lean_Elab_Tactic_Conv_evalPattern_declRange__3___closed__5_value: crate::leanh::LeanCtorObject<4> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*4 + 0) as u16, other: 4, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Pattern_0__Lean_Elab_Tactic_Conv_evalPattern___regBuiltin_Lean_Elab_Tactic_Conv_evalPattern_declRange__3___closed__3_value) as *mut crate::leanh::LeanObject,((( 54 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Pattern_0__Lean_Elab_Tactic_Conv_evalPattern___regBuiltin_Lean_Elab_Tactic_Conv_evalPattern_declRange__3___closed__4_value) as *mut crate::leanh::LeanObject,((( 65 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_Conv_Pattern_0__Lean_Elab_Tactic_Conv_evalPattern___regBuiltin_Lean_Elab_Tactic_Conv_evalPattern_declRange__3___closed__5: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Pattern_0__Lean_Elab_Tactic_Conv_evalPattern___regBuiltin_Lean_Elab_Tactic_Conv_evalPattern_declRange__3___closed__5_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Conv_Pattern_0__Lean_Elab_Tactic_Conv_evalPattern___regBuiltin_Lean_Elab_Tactic_Conv_evalPattern_declRange__3___closed__6_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Pattern_0__Lean_Elab_Tactic_Conv_evalPattern___regBuiltin_Lean_Elab_Tactic_Conv_evalPattern_declRange__3___closed__2_value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Pattern_0__Lean_Elab_Tactic_Conv_evalPattern___regBuiltin_Lean_Elab_Tactic_Conv_evalPattern_declRange__3___closed__5_value) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_Conv_Pattern_0__Lean_Elab_Tactic_Conv_evalPattern___regBuiltin_Lean_Elab_Tactic_Conv_evalPattern_declRange__3___closed__6: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Pattern_0__Lean_Elab_Tactic_Conv_evalPattern___regBuiltin_Lean_Elab_Tactic_Conv_evalPattern_declRange__3___closed__6_value) as *mut crate::leanh::LeanObject;
pub unsafe fn l___private_Lean_Elab_Tactic_Conv_Pattern_0__Lean_Elab_Tactic_Conv_getContext___redArg(
    mut v_a_2193_: *mut crate::leanh::LeanObject,
    mut v_a_2194_: *mut crate::leanh::LeanObject,
    mut v_a_2195_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2197_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2198_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2199_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2200_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2201_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2202_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2203_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2205_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2206_: u8 = 0;
    let mut v___x_2208_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2209_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2210_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2197_ = l_Lean_Meta_getSimpCongrTheorems___redArg(v_a_2195_);
                if crate::leanh::lean_obj_tag(v___x_2197_) == 0 {
                    v_a_2198_ = crate::leanh::lean_ctor_get(v___x_2197_, 0);
                    crate::leanh::lean_inc(v_a_2198_);
                    crate::leanh::lean_dec_ref_known(v___x_2197_, 1);
                    v___x_2199_ = l_Lean_Meta_Simp_neutralConfig;
                    v___x_2200_ = l___private_Lean_Elab_Tactic_Conv_Pattern_0__Lean_Elab_Tactic_Conv_getContext___redArg___closed__0;
                    v___x_2201_ = l_Lean_Options_empty;
                    v___x_2202_ = l_Lean_Meta_Simp_mkContext___redArg(
                        v___x_2199_,
                        v___x_2200_,
                        v_a_2198_,
                        v___x_2201_,
                        v_a_2193_,
                        v_a_2194_,
                        v_a_2195_,
                    );
                    return v___x_2202_;
                } else {
                    v_a_2203_ = crate::leanh::lean_ctor_get(v___x_2197_, 0);
                    v_isSharedCheck_2210_ = (!crate::leanh::lean_is_exclusive(v___x_2197_)) as u8;
                    if v_isSharedCheck_2210_ == 0 {
                        v___x_2205_ = v___x_2197_;
                        v_isShared_2206_ = v_isSharedCheck_2210_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2203_);
                        crate::leanh::lean_dec(v___x_2197_);
                        v___x_2205_ = crate::leanh::lean_box(0);
                        v_isShared_2206_ = v_isSharedCheck_2210_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_2206_ == 0 {
                    v___x_2208_ = v___x_2205_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2209_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2209_, 0, v_a_2203_);
                    v___x_2208_ = v_reuseFailAlloc_2209_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2208_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Elab_Tactic_Conv_Pattern_0__Lean_Elab_Tactic_Conv_getContext___redArg___boxed(
    mut v_a_2211_: *mut crate::leanh::LeanObject,
    mut v_a_2212_: *mut crate::leanh::LeanObject,
    mut v_a_2213_: *mut crate::leanh::LeanObject,
    mut v_a_2214_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2215_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2215_ =
        l___private_Lean_Elab_Tactic_Conv_Pattern_0__Lean_Elab_Tactic_Conv_getContext___redArg(
            v_a_2211_, v_a_2212_, v_a_2213_,
        );
    crate::leanh::lean_dec(v_a_2213_);
    crate::leanh::lean_dec_ref(v_a_2212_);
    crate::leanh::lean_dec_ref(v_a_2211_);
    return v_res_2215_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Conv_Pattern_0__Lean_Elab_Tactic_Conv_getContext(
    mut v_a_2216_: *mut crate::leanh::LeanObject,
    mut v_a_2217_: *mut crate::leanh::LeanObject,
    mut v_a_2218_: *mut crate::leanh::LeanObject,
    mut v_a_2219_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2221_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2221_ =
        l___private_Lean_Elab_Tactic_Conv_Pattern_0__Lean_Elab_Tactic_Conv_getContext___redArg(
            v_a_2216_, v_a_2218_, v_a_2219_,
        );
    return v___x_2221_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Conv_Pattern_0__Lean_Elab_Tactic_Conv_getContext___boxed(
    mut v_a_2222_: *mut crate::leanh::LeanObject,
    mut v_a_2223_: *mut crate::leanh::LeanObject,
    mut v_a_2224_: *mut crate::leanh::LeanObject,
    mut v_a_2225_: *mut crate::leanh::LeanObject,
    mut v_a_2226_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2227_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2227_ = l___private_Lean_Elab_Tactic_Conv_Pattern_0__Lean_Elab_Tactic_Conv_getContext(
        v_a_2222_, v_a_2223_, v_a_2224_, v_a_2225_,
    );
    crate::leanh::lean_dec(v_a_2225_);
    crate::leanh::lean_dec_ref(v_a_2224_);
    crate::leanh::lean_dec(v_a_2223_);
    crate::leanh::lean_dec_ref(v_a_2222_);
    return v_res_2227_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Conv_Pattern_0__Lean_Elab_Tactic_Conv_matchPattern_x3f_go_x3f(
    mut v_pattern_2230_: *mut crate::leanh::LeanObject,
    mut v_e_2231_: *mut crate::leanh::LeanObject,
    mut v_a_2232_: *mut crate::leanh::LeanObject,
    mut v_a_2233_: *mut crate::leanh::LeanObject,
    mut v_a_2234_: *mut crate::leanh::LeanObject,
    mut v_a_2235_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2237_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2238_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2239_: u8 = 0;
    let mut v___x_2240_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2241_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2242_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2243_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2245_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2246_: u8 = 0;
    let mut v___x_2247_: u8 = 0;
    let mut v___x_2248_: u8 = 0;
    let mut v___x_2249_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2251_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2252_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2253_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2254_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2255_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2257_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2258_: u8 = 0;
    let mut v_val_2259_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2261_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2262_: u8 = 0;
    let mut v_fst_2263_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2264_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2266_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2267_: u8 = 0;
    let mut v___x_2268_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2269_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2271_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2273_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2275_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2276_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2277_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2278_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2279_: u8 = 0;
    let mut v_isSharedCheck_2280_: u8 = 0;
    let mut v_isSharedCheck_2281_: u8 = 0;
    let mut v_unused_2282_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2283_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2284_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2285_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2287_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2288_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2289_: u8 = 0;
    let mut v_a_2290_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2292_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2293_: u8 = 0;
    let mut v___x_2295_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2296_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2297_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                crate::leanh::lean_inc_ref(v_e_2231_);
                v___x_2237_ = l_Lean_Expr_toHeadIndex(v_e_2231_);
                crate::leanh::lean_inc_ref(v_pattern_2230_);
                v___x_2238_ = l_Lean_Expr_toHeadIndex(v_pattern_2230_);
                v___x_2239_ = l_Lean_instBEqHeadIndex_beq(v___x_2237_, v___x_2238_);
                crate::leanh::lean_dec(v___x_2238_);
                crate::leanh::lean_dec(v___x_2237_);
                if v___x_2239_ == 0 {
                    crate::leanh::lean_dec_ref(v_e_2231_);
                    crate::leanh::lean_dec_ref(v_pattern_2230_);
                    v___x_2240_ = crate::leanh::lean_box(0);
                    v___x_2241_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2241_, 0, v___x_2240_);
                    return v___x_2241_;
                } else {
                    crate::leanh::lean_inc_ref(v_e_2231_);
                    crate::leanh::lean_inc_ref(v_pattern_2230_);
                    v___x_2242_ = l_Lean_Meta_isExprDefEqGuarded(
                        v_pattern_2230_,
                        v_e_2231_,
                        v_a_2232_,
                        v_a_2233_,
                        v_a_2234_,
                        v_a_2235_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_2242_) == 0 {
                        v_a_2243_ = crate::leanh::lean_ctor_get(v___x_2242_, 0);
                        v_isSharedCheck_2289_ =
                            (!crate::leanh::lean_is_exclusive(v___x_2242_)) as u8;
                        if v_isSharedCheck_2289_ == 0 {
                            v___x_2245_ = v___x_2242_;
                            v_isShared_2246_ = v_isSharedCheck_2289_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_2243_);
                            crate::leanh::lean_dec(v___x_2242_);
                            v___x_2245_ = crate::leanh::lean_box(0);
                            v_isShared_2246_ = v_isSharedCheck_2289_;
                            state = 1;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec_ref(v_e_2231_);
                        crate::leanh::lean_dec_ref(v_pattern_2230_);
                        v_a_2290_ = crate::leanh::lean_ctor_get(v___x_2242_, 0);
                        v_isSharedCheck_2297_ =
                            (!crate::leanh::lean_is_exclusive(v___x_2242_)) as u8;
                        if v_isSharedCheck_2297_ == 0 {
                            v___x_2292_ = v___x_2242_;
                            v_isShared_2293_ = v_isSharedCheck_2297_;
                            state = 10;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_2290_);
                            crate::leanh::lean_dec(v___x_2242_);
                            v___x_2292_ = crate::leanh::lean_box(0);
                            v_isShared_2293_ = v_isSharedCheck_2297_;
                            state = 10;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v___x_2247_ = (crate::leanh::lean_unbox(v_a_2243_) as u8);
                crate::leanh::lean_dec(v_a_2243_);
                if v___x_2247_ == 0 {
                    v___x_2248_ = l_Lean_Expr_isApp(v_e_2231_);
                    if v___x_2248_ == 0 {
                        crate::leanh::lean_dec_ref(v_e_2231_);
                        crate::leanh::lean_dec_ref(v_pattern_2230_);
                        v___x_2249_ = crate::leanh::lean_box(0);
                        if v_isShared_2246_ == 0 {
                            crate::leanh::lean_ctor_set(v___x_2245_, 0, v___x_2249_);
                            v___x_2251_ = v___x_2245_;
                            state = 2;
                            continue;
                        } else {
                            v_reuseFailAlloc_2252_ =
                                crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_2252_, 0, v___x_2249_);
                            v___x_2251_ = v_reuseFailAlloc_2252_;
                            state = 2;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_del_object(v___x_2245_);
                        v___x_2253_ = l_Lean_Expr_appFn_x21(v_e_2231_);
                        v___x_2254_ = l___private_Lean_Elab_Tactic_Conv_Pattern_0__Lean_Elab_Tactic_Conv_matchPattern_x3f_go_x3f(v_pattern_2230_, v___x_2253_, v_a_2232_, v_a_2233_, v_a_2234_, v_a_2235_);
                        if crate::leanh::lean_obj_tag(v___x_2254_) == 0 {
                            v_a_2255_ = crate::leanh::lean_ctor_get(v___x_2254_, 0);
                            crate::leanh::lean_inc(v_a_2255_);
                            if crate::leanh::lean_obj_tag(v_a_2255_) == 0 {
                                crate::leanh::lean_dec_ref(v_e_2231_);
                                return v___x_2254_;
                            } else {
                                v_isSharedCheck_2281_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_2254_)) as u8;
                                if v_isSharedCheck_2281_ == 0 {
                                    v_unused_2282_ = crate::leanh::lean_ctor_get(v___x_2254_, 0);
                                    crate::leanh::lean_dec(v_unused_2282_);
                                    v___x_2257_ = v___x_2254_;
                                    v_isShared_2258_ = v_isSharedCheck_2281_;
                                    state = 3;
                                    continue;
                                } else {
                                    crate::leanh::lean_dec(v___x_2254_);
                                    v___x_2257_ = crate::leanh::lean_box(0);
                                    v_isShared_2258_ = v_isSharedCheck_2281_;
                                    state = 3;
                                    continue;
                                }
                            }
                        } else {
                            crate::leanh::lean_dec_ref(v_e_2231_);
                            return v___x_2254_;
                        }
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_pattern_2230_);
                    v___x_2283_ = l___private_Lean_Elab_Tactic_Conv_Pattern_0__Lean_Elab_Tactic_Conv_matchPattern_x3f_go_x3f___closed__0;
                    v___x_2284_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2284_, 0, v_e_2231_);
                    crate::leanh::lean_ctor_set(v___x_2284_, 1, v___x_2283_);
                    v___x_2285_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2285_, 0, v___x_2284_);
                    if v_isShared_2246_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_2245_, 0, v___x_2285_);
                        v___x_2287_ = v___x_2245_;
                        state = 9;
                        continue;
                    } else {
                        v_reuseFailAlloc_2288_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2288_, 0, v___x_2285_);
                        v___x_2287_ = v_reuseFailAlloc_2288_;
                        state = 9;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_2251_;
            }
            3 => {
                v_val_2259_ = crate::leanh::lean_ctor_get(v_a_2255_, 0);
                v_isSharedCheck_2280_ = (!crate::leanh::lean_is_exclusive(v_a_2255_)) as u8;
                if v_isSharedCheck_2280_ == 0 {
                    v___x_2261_ = v_a_2255_;
                    v_isShared_2262_ = v_isSharedCheck_2280_;
                    state = 4;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_val_2259_);
                    crate::leanh::lean_dec(v_a_2255_);
                    v___x_2261_ = crate::leanh::lean_box(0);
                    v_isShared_2262_ = v_isSharedCheck_2280_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v_fst_2263_ = crate::leanh::lean_ctor_get(v_val_2259_, 0);
                v_snd_2264_ = crate::leanh::lean_ctor_get(v_val_2259_, 1);
                v_isSharedCheck_2279_ = (!crate::leanh::lean_is_exclusive(v_val_2259_)) as u8;
                if v_isSharedCheck_2279_ == 0 {
                    v___x_2266_ = v_val_2259_;
                    v_isShared_2267_ = v_isSharedCheck_2279_;
                    state = 5;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snd_2264_);
                    crate::leanh::lean_inc(v_fst_2263_);
                    crate::leanh::lean_dec(v_val_2259_);
                    v___x_2266_ = crate::leanh::lean_box(0);
                    v_isShared_2267_ = v_isSharedCheck_2279_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v___x_2268_ = l_Lean_Expr_appArg_x21(v_e_2231_);
                crate::leanh::lean_dec_ref(v_e_2231_);
                v___x_2269_ = lean_array_push(v_snd_2264_, v___x_2268_);
                if v_isShared_2267_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2266_, 1, v___x_2269_);
                    v___x_2271_ = v___x_2266_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_2278_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2278_, 0, v_fst_2263_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2278_, 1, v___x_2269_);
                    v___x_2271_ = v_reuseFailAlloc_2278_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                if v_isShared_2262_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2261_, 0, v___x_2271_);
                    v___x_2273_ = v___x_2261_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_2277_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2277_, 0, v___x_2271_);
                    v___x_2273_ = v_reuseFailAlloc_2277_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                if v_isShared_2258_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2257_, 0, v___x_2273_);
                    v___x_2275_ = v___x_2257_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_2276_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2276_, 0, v___x_2273_);
                    v___x_2275_ = v_reuseFailAlloc_2276_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_2275_;
            }
            9 => {
                return v___x_2287_;
            }
            10 => {
                if v_isShared_2293_ == 0 {
                    v___x_2295_ = v___x_2292_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_2296_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2296_, 0, v_a_2290_);
                    v___x_2295_ = v_reuseFailAlloc_2296_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                return v___x_2295_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Elab_Tactic_Conv_Pattern_0__Lean_Elab_Tactic_Conv_matchPattern_x3f_go_x3f___boxed(
    mut v_pattern_2298_: *mut crate::leanh::LeanObject,
    mut v_e_2299_: *mut crate::leanh::LeanObject,
    mut v_a_2300_: *mut crate::leanh::LeanObject,
    mut v_a_2301_: *mut crate::leanh::LeanObject,
    mut v_a_2302_: *mut crate::leanh::LeanObject,
    mut v_a_2303_: *mut crate::leanh::LeanObject,
    mut v_a_2304_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2305_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2305_ =
        l___private_Lean_Elab_Tactic_Conv_Pattern_0__Lean_Elab_Tactic_Conv_matchPattern_x3f_go_x3f(
            v_pattern_2298_,
            v_e_2299_,
            v_a_2300_,
            v_a_2301_,
            v_a_2302_,
            v_a_2303_,
        );
    crate::leanh::lean_dec(v_a_2303_);
    crate::leanh::lean_dec_ref(v_a_2302_);
    crate::leanh::lean_dec(v_a_2301_);
    crate::leanh::lean_dec_ref(v_a_2300_);
    return v_res_2305_;
}
pub unsafe fn l_Lean_Meta_withNewMCtxDepth___at___00Lean_Elab_Tactic_Conv_matchPattern_x3f_spec__0___redArg(
    mut v_k_2306_: *mut crate::leanh::LeanObject,
    mut v_allowLevelAssignments_2307_: u8,
    mut v___y_2308_: *mut crate::leanh::LeanObject,
    mut v___y_2309_: *mut crate::leanh::LeanObject,
    mut v___y_2310_: *mut crate::leanh::LeanObject,
    mut v___y_2311_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2313_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2314_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2316_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2317_: u8 = 0;
    let mut v___x_2319_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2320_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2321_: u8 = 0;
    let mut v_a_2322_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2324_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2325_: u8 = 0;
    let mut v___x_2327_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2328_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2329_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2313_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withNewMCtxDepthImp(
                    crate::leanh::lean_box(0),
                    v_allowLevelAssignments_2307_,
                    v_k_2306_,
                    v___y_2308_,
                    v___y_2309_,
                    v___y_2310_,
                    v___y_2311_,
                );
                if crate::leanh::lean_obj_tag(v___x_2313_) == 0 {
                    v_a_2314_ = crate::leanh::lean_ctor_get(v___x_2313_, 0);
                    v_isSharedCheck_2321_ = (!crate::leanh::lean_is_exclusive(v___x_2313_)) as u8;
                    if v_isSharedCheck_2321_ == 0 {
                        v___x_2316_ = v___x_2313_;
                        v_isShared_2317_ = v_isSharedCheck_2321_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2314_);
                        crate::leanh::lean_dec(v___x_2313_);
                        v___x_2316_ = crate::leanh::lean_box(0);
                        v_isShared_2317_ = v_isSharedCheck_2321_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_2322_ = crate::leanh::lean_ctor_get(v___x_2313_, 0);
                    v_isSharedCheck_2329_ = (!crate::leanh::lean_is_exclusive(v___x_2313_)) as u8;
                    if v_isSharedCheck_2329_ == 0 {
                        v___x_2324_ = v___x_2313_;
                        v_isShared_2325_ = v_isSharedCheck_2329_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2322_);
                        crate::leanh::lean_dec(v___x_2313_);
                        v___x_2324_ = crate::leanh::lean_box(0);
                        v_isShared_2325_ = v_isSharedCheck_2329_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_2317_ == 0 {
                    v___x_2319_ = v___x_2316_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2320_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2320_, 0, v_a_2314_);
                    v___x_2319_ = v_reuseFailAlloc_2320_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2319_;
            }
            3 => {
                if v_isShared_2325_ == 0 {
                    v___x_2327_ = v___x_2324_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2328_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2328_, 0, v_a_2322_);
                    v___x_2327_ = v_reuseFailAlloc_2328_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_2327_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_withNewMCtxDepth___at___00Lean_Elab_Tactic_Conv_matchPattern_x3f_spec__0___redArg___boxed(
    mut v_k_2330_: *mut crate::leanh::LeanObject,
    mut v_allowLevelAssignments_2331_: *mut crate::leanh::LeanObject,
    mut v___y_2332_: *mut crate::leanh::LeanObject,
    mut v___y_2333_: *mut crate::leanh::LeanObject,
    mut v___y_2334_: *mut crate::leanh::LeanObject,
    mut v___y_2335_: *mut crate::leanh::LeanObject,
    mut v___y_2336_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_allowLevelAssignments_boxed_2337_: u8 = 0;
    let mut v_res_2338_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_allowLevelAssignments_boxed_2337_ =
        (crate::leanh::lean_unbox(v_allowLevelAssignments_2331_) as u8);
    v_res_2338_ = l_Lean_Meta_withNewMCtxDepth___at___00Lean_Elab_Tactic_Conv_matchPattern_x3f_spec__0___redArg(v_k_2330_, v_allowLevelAssignments_boxed_2337_, v___y_2332_, v___y_2333_, v___y_2334_, v___y_2335_);
    crate::leanh::lean_dec(v___y_2335_);
    crate::leanh::lean_dec_ref(v___y_2334_);
    crate::leanh::lean_dec(v___y_2333_);
    crate::leanh::lean_dec_ref(v___y_2332_);
    return v_res_2338_;
}
pub unsafe fn l_Lean_Meta_withNewMCtxDepth___at___00Lean_Elab_Tactic_Conv_matchPattern_x3f_spec__0(
    mut v_00_u03b1_2339_: *mut crate::leanh::LeanObject,
    mut v_k_2340_: *mut crate::leanh::LeanObject,
    mut v_allowLevelAssignments_2341_: u8,
    mut v___y_2342_: *mut crate::leanh::LeanObject,
    mut v___y_2343_: *mut crate::leanh::LeanObject,
    mut v___y_2344_: *mut crate::leanh::LeanObject,
    mut v___y_2345_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2347_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2347_ = l_Lean_Meta_withNewMCtxDepth___at___00Lean_Elab_Tactic_Conv_matchPattern_x3f_spec__0___redArg(v_k_2340_, v_allowLevelAssignments_2341_, v___y_2342_, v___y_2343_, v___y_2344_, v___y_2345_);
    return v___x_2347_;
}
pub unsafe fn l_Lean_Meta_withNewMCtxDepth___at___00Lean_Elab_Tactic_Conv_matchPattern_x3f_spec__0___boxed(
    mut v_00_u03b1_2348_: *mut crate::leanh::LeanObject,
    mut v_k_2349_: *mut crate::leanh::LeanObject,
    mut v_allowLevelAssignments_2350_: *mut crate::leanh::LeanObject,
    mut v___y_2351_: *mut crate::leanh::LeanObject,
    mut v___y_2352_: *mut crate::leanh::LeanObject,
    mut v___y_2353_: *mut crate::leanh::LeanObject,
    mut v___y_2354_: *mut crate::leanh::LeanObject,
    mut v___y_2355_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_allowLevelAssignments_boxed_2356_: u8 = 0;
    let mut v_res_2357_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_allowLevelAssignments_boxed_2356_ =
        (crate::leanh::lean_unbox(v_allowLevelAssignments_2350_) as u8);
    v_res_2357_ =
        l_Lean_Meta_withNewMCtxDepth___at___00Lean_Elab_Tactic_Conv_matchPattern_x3f_spec__0(
            v_00_u03b1_2348_,
            v_k_2349_,
            v_allowLevelAssignments_boxed_2356_,
            v___y_2351_,
            v___y_2352_,
            v___y_2353_,
            v___y_2354_,
        );
    crate::leanh::lean_dec(v___y_2354_);
    crate::leanh::lean_dec_ref(v___y_2353_);
    crate::leanh::lean_dec(v___y_2352_);
    crate::leanh::lean_dec_ref(v___y_2351_);
    return v_res_2357_;
}
pub unsafe fn _init_l_Lean_Elab_Tactic_Conv_matchPattern_x3f___lam__0___closed__0() -> u64 {
    let mut v___x_2358_: u8 = 0;
    let mut v___x_2359_: u64 = 0;
    v___x_2358_ = 2;
    v___x_2359_ = l_Lean_Meta_TransparencyMode_toUInt64(v___x_2358_);
    return v___x_2359_;
}
pub unsafe fn l_Lean_Elab_Tactic_Conv_matchPattern_x3f___lam__0(
    mut v_pattern_2360_: *mut crate::leanh::LeanObject,
    mut v_e_2361_: *mut crate::leanh::LeanObject,
    mut v___y_2362_: *mut crate::leanh::LeanObject,
    mut v___y_2363_: *mut crate::leanh::LeanObject,
    mut v___y_2364_: *mut crate::leanh::LeanObject,
    mut v___y_2365_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2367_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2368_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2369_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2370_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2371_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_foApprox_2372_: u8 = 0;
    let mut v_ctxApprox_2373_: u8 = 0;
    let mut v_quasiPatternApprox_2374_: u8 = 0;
    let mut v_constApprox_2375_: u8 = 0;
    let mut v_isDefEqStuckEx_2376_: u8 = 0;
    let mut v_unificationHints_2377_: u8 = 0;
    let mut v_proofIrrelevance_2378_: u8 = 0;
    let mut v_assignSyntheticOpaque_2379_: u8 = 0;
    let mut v_offsetCnstrs_2380_: u8 = 0;
    let mut v_etaStruct_2381_: u8 = 0;
    let mut v_univApprox_2382_: u8 = 0;
    let mut v_iota_2383_: u8 = 0;
    let mut v_beta_2384_: u8 = 0;
    let mut v_proj_2385_: u8 = 0;
    let mut v_zeta_2386_: u8 = 0;
    let mut v_zetaDelta_2387_: u8 = 0;
    let mut v_zetaUnused_2388_: u8 = 0;
    let mut v_zetaHave_2389_: u8 = 0;
    let mut v___x_2391_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2392_: u8 = 0;
    let mut v_trackZetaDelta_2393_: u8 = 0;
    let mut v_zetaDeltaSet_2394_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_lctx_2395_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_localInstances_2396_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_defEqCtx_x3f_2397_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_synthPendingDepth_2398_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_canUnfold_x3f_2399_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_univApprox_2400_: u8 = 0;
    let mut v_inTypeClassResolution_2401_: u8 = 0;
    let mut v_cacheInferType_2402_: u8 = 0;
    let mut v___x_2403_: u8 = 0;
    let mut v_config_2405_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2406_: u64 = 0;
    let mut v___x_2408_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2409_: u8 = 0;
    let mut v___x_2410_: u64 = 0;
    let mut v___x_2411_: u64 = 0;
    let mut v___x_2412_: u64 = 0;
    let mut v___x_2413_: u64 = 0;
    let mut v_key_2414_: u64 = 0;
    let mut v___x_2415_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2417_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2418_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2419_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2420_: u8 = 0;
    let mut v_unused_2421_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2422_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2423_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2424_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2425_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2426_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2427_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2428_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2429_: u8 = 0;
    let mut v_a_2430_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2432_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2433_: u8 = 0;
    let mut v___x_2435_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2436_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2437_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2367_ = l_Lean_Meta_openAbstractMVarsResult(
                    v_pattern_2360_,
                    v___y_2362_,
                    v___y_2363_,
                    v___y_2364_,
                    v___y_2365_,
                );
                if crate::leanh::lean_obj_tag(v___x_2367_) == 0 {
                    v_a_2368_ = crate::leanh::lean_ctor_get(v___x_2367_, 0);
                    crate::leanh::lean_inc(v_a_2368_);
                    crate::leanh::lean_dec_ref_known(v___x_2367_, 1);
                    v_snd_2369_ = crate::leanh::lean_ctor_get(v_a_2368_, 1);
                    crate::leanh::lean_inc(v_snd_2369_);
                    crate::leanh::lean_dec(v_a_2368_);
                    v_snd_2370_ = crate::leanh::lean_ctor_get(v_snd_2369_, 1);
                    crate::leanh::lean_inc(v_snd_2370_);
                    crate::leanh::lean_dec(v_snd_2369_);
                    v___x_2371_ = l_Lean_Meta_Context_config(v___y_2362_);
                    v_foApprox_2372_ = crate::leanh::lean_ctor_get_uint8(v___x_2371_, 0 as u32);
                    v_ctxApprox_2373_ = crate::leanh::lean_ctor_get_uint8(v___x_2371_, 1 as u32);
                    v_quasiPatternApprox_2374_ =
                        crate::leanh::lean_ctor_get_uint8(v___x_2371_, 2 as u32);
                    v_constApprox_2375_ = crate::leanh::lean_ctor_get_uint8(v___x_2371_, 3 as u32);
                    v_isDefEqStuckEx_2376_ =
                        crate::leanh::lean_ctor_get_uint8(v___x_2371_, 4 as u32);
                    v_unificationHints_2377_ =
                        crate::leanh::lean_ctor_get_uint8(v___x_2371_, 5 as u32);
                    v_proofIrrelevance_2378_ =
                        crate::leanh::lean_ctor_get_uint8(v___x_2371_, 6 as u32);
                    v_assignSyntheticOpaque_2379_ =
                        crate::leanh::lean_ctor_get_uint8(v___x_2371_, 7 as u32);
                    v_offsetCnstrs_2380_ = crate::leanh::lean_ctor_get_uint8(v___x_2371_, 8 as u32);
                    v_etaStruct_2381_ = crate::leanh::lean_ctor_get_uint8(v___x_2371_, 10 as u32);
                    v_univApprox_2382_ = crate::leanh::lean_ctor_get_uint8(v___x_2371_, 11 as u32);
                    v_iota_2383_ = crate::leanh::lean_ctor_get_uint8(v___x_2371_, 12 as u32);
                    v_beta_2384_ = crate::leanh::lean_ctor_get_uint8(v___x_2371_, 13 as u32);
                    v_proj_2385_ = crate::leanh::lean_ctor_get_uint8(v___x_2371_, 14 as u32);
                    v_zeta_2386_ = crate::leanh::lean_ctor_get_uint8(v___x_2371_, 15 as u32);
                    v_zetaDelta_2387_ = crate::leanh::lean_ctor_get_uint8(v___x_2371_, 16 as u32);
                    v_zetaUnused_2388_ = crate::leanh::lean_ctor_get_uint8(v___x_2371_, 17 as u32);
                    v_zetaHave_2389_ = crate::leanh::lean_ctor_get_uint8(v___x_2371_, 18 as u32);
                    v_isSharedCheck_2429_ = (!crate::leanh::lean_is_exclusive(v___x_2371_)) as u8;
                    if v_isSharedCheck_2429_ == 0 {
                        v___x_2391_ = v___x_2371_;
                        v_isShared_2392_ = v_isSharedCheck_2429_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v___x_2371_);
                        v___x_2391_ = crate::leanh::lean_box(0);
                        v_isShared_2392_ = v_isSharedCheck_2429_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v___y_2362_);
                    crate::leanh::lean_dec_ref(v_e_2361_);
                    v_a_2430_ = crate::leanh::lean_ctor_get(v___x_2367_, 0);
                    v_isSharedCheck_2437_ = (!crate::leanh::lean_is_exclusive(v___x_2367_)) as u8;
                    if v_isSharedCheck_2437_ == 0 {
                        v___x_2432_ = v___x_2367_;
                        v_isShared_2433_ = v_isSharedCheck_2437_;
                        state = 5;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2430_);
                        crate::leanh::lean_dec(v___x_2367_);
                        v___x_2432_ = crate::leanh::lean_box(0);
                        v_isShared_2433_ = v_isSharedCheck_2437_;
                        state = 5;
                        continue;
                    }
                }
            }
            1 => {
                v_trackZetaDelta_2393_ = crate::leanh::lean_ctor_get_uint8(
                    v___y_2362_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 7) as u32,
                );
                v_zetaDeltaSet_2394_ = crate::leanh::lean_ctor_get(v___y_2362_, 1);
                crate::leanh::lean_inc(v_zetaDeltaSet_2394_);
                v_lctx_2395_ = crate::leanh::lean_ctor_get(v___y_2362_, 2);
                crate::leanh::lean_inc_ref(v_lctx_2395_);
                v_localInstances_2396_ = crate::leanh::lean_ctor_get(v___y_2362_, 3);
                crate::leanh::lean_inc_ref(v_localInstances_2396_);
                v_defEqCtx_x3f_2397_ = crate::leanh::lean_ctor_get(v___y_2362_, 4);
                crate::leanh::lean_inc(v_defEqCtx_x3f_2397_);
                v_synthPendingDepth_2398_ = crate::leanh::lean_ctor_get(v___y_2362_, 5);
                crate::leanh::lean_inc(v_synthPendingDepth_2398_);
                v_canUnfold_x3f_2399_ = crate::leanh::lean_ctor_get(v___y_2362_, 6);
                crate::leanh::lean_inc(v_canUnfold_x3f_2399_);
                v_univApprox_2400_ = crate::leanh::lean_ctor_get_uint8(
                    v___y_2362_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 7 + 1) as u32,
                );
                v_inTypeClassResolution_2401_ = crate::leanh::lean_ctor_get_uint8(
                    v___y_2362_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 7 + 2) as u32,
                );
                v_cacheInferType_2402_ = crate::leanh::lean_ctor_get_uint8(
                    v___y_2362_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 7 + 3) as u32,
                );
                v___x_2403_ = 2;
                if v_isShared_2392_ == 0 {
                    v_config_2405_ = v___x_2391_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2428_ = crate::leanh::lean_alloc_ctor(0, 0, (19) as u32);
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_2428_,
                        0 as u32,
                        v_foApprox_2372_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_2428_,
                        1 as u32,
                        v_ctxApprox_2373_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_2428_,
                        2 as u32,
                        v_quasiPatternApprox_2374_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_2428_,
                        3 as u32,
                        v_constApprox_2375_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_2428_,
                        4 as u32,
                        v_isDefEqStuckEx_2376_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_2428_,
                        5 as u32,
                        v_unificationHints_2377_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_2428_,
                        6 as u32,
                        v_proofIrrelevance_2378_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_2428_,
                        7 as u32,
                        v_assignSyntheticOpaque_2379_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_2428_,
                        8 as u32,
                        v_offsetCnstrs_2380_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_2428_,
                        10 as u32,
                        v_etaStruct_2381_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_2428_,
                        11 as u32,
                        v_univApprox_2382_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_2428_,
                        12 as u32,
                        v_iota_2383_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_2428_,
                        13 as u32,
                        v_beta_2384_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_2428_,
                        14 as u32,
                        v_proj_2385_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_2428_,
                        15 as u32,
                        v_zeta_2386_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_2428_,
                        16 as u32,
                        v_zetaDelta_2387_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_2428_,
                        17 as u32,
                        v_zetaUnused_2388_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_2428_,
                        18 as u32,
                        v_zetaHave_2389_,
                    );
                    v_config_2405_ = v_reuseFailAlloc_2428_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                crate::leanh::lean_ctor_set_uint8(v_config_2405_, 9 as u32, v___x_2403_);
                v___x_2406_ = l_Lean_Meta_Context_configKey(v___y_2362_);
                v_isSharedCheck_2420_ = (!crate::leanh::lean_is_exclusive(v___y_2362_)) as u8;
                if v_isSharedCheck_2420_ == 0 {
                    v_unused_2421_ = crate::leanh::lean_ctor_get(v___y_2362_, 6);
                    crate::leanh::lean_dec(v_unused_2421_);
                    v_unused_2422_ = crate::leanh::lean_ctor_get(v___y_2362_, 5);
                    crate::leanh::lean_dec(v_unused_2422_);
                    v_unused_2423_ = crate::leanh::lean_ctor_get(v___y_2362_, 4);
                    crate::leanh::lean_dec(v_unused_2423_);
                    v_unused_2424_ = crate::leanh::lean_ctor_get(v___y_2362_, 3);
                    crate::leanh::lean_dec(v_unused_2424_);
                    v_unused_2425_ = crate::leanh::lean_ctor_get(v___y_2362_, 2);
                    crate::leanh::lean_dec(v_unused_2425_);
                    v_unused_2426_ = crate::leanh::lean_ctor_get(v___y_2362_, 1);
                    crate::leanh::lean_dec(v_unused_2426_);
                    v_unused_2427_ = crate::leanh::lean_ctor_get(v___y_2362_, 0);
                    crate::leanh::lean_dec(v_unused_2427_);
                    v___x_2408_ = v___y_2362_;
                    v_isShared_2409_ = v_isSharedCheck_2420_;
                    state = 3;
                    continue;
                } else {
                    crate::leanh::lean_dec(v___y_2362_);
                    v___x_2408_ = crate::leanh::lean_box(0);
                    v_isShared_2409_ = v_isSharedCheck_2420_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_2410_ = 3u64;
                v___x_2411_ = lean_uint64_shift_right(v___x_2406_, v___x_2410_);
                v___x_2412_ = lean_uint64_shift_left(v___x_2411_, v___x_2410_);
                v___x_2413_ = crate::leanh::lean_uint64_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_Elab_Tactic_Conv_matchPattern_x3f___lam__0___closed__0
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_Elab_Tactic_Conv_matchPattern_x3f___lam__0___closed__0_once
                    ),
                    _init_l_Lean_Elab_Tactic_Conv_matchPattern_x3f___lam__0___closed__0,
                );
                v_key_2414_ = lean_uint64_lor(v___x_2412_, v___x_2413_);
                v___x_2415_ = crate::leanh::lean_alloc_ctor(0, 1, (8) as u32);
                crate::leanh::lean_ctor_set(v___x_2415_, 0, v_config_2405_);
                crate::leanh::lean_ctor_set_uint64(
                    v___x_2415_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    v_key_2414_,
                );
                if v_isShared_2409_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2408_, 0, v___x_2415_);
                    v___x_2417_ = v___x_2408_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2419_ = crate::leanh::lean_alloc_ctor(0, 7, (4) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2419_, 0, v___x_2415_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2419_, 1, v_zetaDeltaSet_2394_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2419_, 2, v_lctx_2395_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2419_, 3, v_localInstances_2396_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2419_, 4, v_defEqCtx_x3f_2397_);
                    crate::leanh::lean_ctor_set(
                        v_reuseFailAlloc_2419_,
                        5,
                        v_synthPendingDepth_2398_,
                    );
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2419_, 6, v_canUnfold_x3f_2399_);
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_2419_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 7) as u32,
                        v_trackZetaDelta_2393_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_2419_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 7 + 1) as u32,
                        v_univApprox_2400_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_2419_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 7 + 2) as u32,
                        v_inTypeClassResolution_2401_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_2419_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 7 + 3) as u32,
                        v_cacheInferType_2402_,
                    );
                    v___x_2417_ = v_reuseFailAlloc_2419_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_2418_ = l___private_Lean_Elab_Tactic_Conv_Pattern_0__Lean_Elab_Tactic_Conv_matchPattern_x3f_go_x3f(v_snd_2370_, v_e_2361_, v___x_2417_, v___y_2363_, v___y_2364_, v___y_2365_);
                crate::leanh::lean_dec_ref(v___x_2417_);
                return v___x_2418_;
            }
            5 => {
                if v_isShared_2433_ == 0 {
                    v___x_2435_ = v___x_2432_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_2436_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2436_, 0, v_a_2430_);
                    v___x_2435_ = v_reuseFailAlloc_2436_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_2435_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_Tactic_Conv_matchPattern_x3f___lam__0___boxed(
    mut v_pattern_2438_: *mut crate::leanh::LeanObject,
    mut v_e_2439_: *mut crate::leanh::LeanObject,
    mut v___y_2440_: *mut crate::leanh::LeanObject,
    mut v___y_2441_: *mut crate::leanh::LeanObject,
    mut v___y_2442_: *mut crate::leanh::LeanObject,
    mut v___y_2443_: *mut crate::leanh::LeanObject,
    mut v___y_2444_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2445_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2445_ = l_Lean_Elab_Tactic_Conv_matchPattern_x3f___lam__0(
        v_pattern_2438_,
        v_e_2439_,
        v___y_2440_,
        v___y_2441_,
        v___y_2442_,
        v___y_2443_,
    );
    crate::leanh::lean_dec(v___y_2443_);
    crate::leanh::lean_dec_ref(v___y_2442_);
    crate::leanh::lean_dec(v___y_2441_);
    return v_res_2445_;
}
pub unsafe fn l_Lean_Elab_Tactic_Conv_matchPattern_x3f(
    mut v_pattern_2446_: *mut crate::leanh::LeanObject,
    mut v_e_2447_: *mut crate::leanh::LeanObject,
    mut v_a_2448_: *mut crate::leanh::LeanObject,
    mut v_a_2449_: *mut crate::leanh::LeanObject,
    mut v_a_2450_: *mut crate::leanh::LeanObject,
    mut v_a_2451_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_2453_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2454_: u8 = 0;
    let mut v___x_2455_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_2453_ = crate::leanh::lean_alloc_closure(
        l_Lean_Elab_Tactic_Conv_matchPattern_x3f___lam__0___boxed as *mut core::ffi::c_void,
        7,
        2,
    );
    crate::leanh::lean_closure_set(v___f_2453_, 0, v_pattern_2446_);
    crate::leanh::lean_closure_set(v___f_2453_, 1, v_e_2447_);
    v___x_2454_ = 0;
    v___x_2455_ = l_Lean_Meta_withNewMCtxDepth___at___00Lean_Elab_Tactic_Conv_matchPattern_x3f_spec__0___redArg(v___f_2453_, v___x_2454_, v_a_2448_, v_a_2449_, v_a_2450_, v_a_2451_);
    return v___x_2455_;
}
pub unsafe fn l_Lean_Elab_Tactic_Conv_matchPattern_x3f___boxed(
    mut v_pattern_2456_: *mut crate::leanh::LeanObject,
    mut v_e_2457_: *mut crate::leanh::LeanObject,
    mut v_a_2458_: *mut crate::leanh::LeanObject,
    mut v_a_2459_: *mut crate::leanh::LeanObject,
    mut v_a_2460_: *mut crate::leanh::LeanObject,
    mut v_a_2461_: *mut crate::leanh::LeanObject,
    mut v_a_2462_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2463_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2463_ = l_Lean_Elab_Tactic_Conv_matchPattern_x3f(
        v_pattern_2456_,
        v_e_2457_,
        v_a_2458_,
        v_a_2459_,
        v_a_2460_,
        v_a_2461_,
    );
    crate::leanh::lean_dec(v_a_2461_);
    crate::leanh::lean_dec_ref(v_a_2460_);
    crate::leanh::lean_dec(v_a_2459_);
    crate::leanh::lean_dec_ref(v_a_2458_);
    return v_res_2463_;
}
pub unsafe fn l_Lean_Elab_Tactic_Conv_PatternMatchState_ctorIdx(
    mut v_x_2464_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_2464_) == 0 {
        let mut v___x_2465_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_2465_ = crate::leanh::lean_unsigned_to_nat(0);
        return v___x_2465_;
    } else {
        let mut v___x_2466_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_2466_ = crate::leanh::lean_unsigned_to_nat(1);
        return v___x_2466_;
    }
}
pub unsafe fn l_Lean_Elab_Tactic_Conv_PatternMatchState_ctorIdx___boxed(
    mut v_x_2467_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2468_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2468_ = l_Lean_Elab_Tactic_Conv_PatternMatchState_ctorIdx(v_x_2467_);
    crate::leanh::lean_dec_ref(v_x_2467_);
    return v_res_2468_;
}
pub unsafe fn l_Lean_Elab_Tactic_Conv_PatternMatchState_ctorElim___redArg(
    mut v_t_2469_: *mut crate::leanh::LeanObject,
    mut v_k_2470_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_t_2469_) == 0 {
        let mut v_subgoals_2471_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2472_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_subgoals_2471_ = crate::leanh::lean_ctor_get(v_t_2469_, 0);
        crate::leanh::lean_inc_ref(v_subgoals_2471_);
        crate::leanh::lean_dec_ref_known(v_t_2469_, 1);
        v___x_2472_ = crate::leanh::lean_apply_1(v_k_2470_, v_subgoals_2471_);
        return v___x_2472_;
    } else {
        let mut v_subgoals_2473_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_idx_2474_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_remaining_2475_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2476_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_subgoals_2473_ = crate::leanh::lean_ctor_get(v_t_2469_, 0);
        crate::leanh::lean_inc_ref(v_subgoals_2473_);
        v_idx_2474_ = crate::leanh::lean_ctor_get(v_t_2469_, 1);
        crate::leanh::lean_inc(v_idx_2474_);
        v_remaining_2475_ = crate::leanh::lean_ctor_get(v_t_2469_, 2);
        crate::leanh::lean_inc(v_remaining_2475_);
        crate::leanh::lean_dec_ref_known(v_t_2469_, 3);
        v___x_2476_ =
            crate::leanh::lean_apply_3(v_k_2470_, v_subgoals_2473_, v_idx_2474_, v_remaining_2475_);
        return v___x_2476_;
    }
}
pub unsafe fn l_Lean_Elab_Tactic_Conv_PatternMatchState_ctorElim(
    mut v_motive_2477_: *mut crate::leanh::LeanObject,
    mut v_ctorIdx_2478_: *mut crate::leanh::LeanObject,
    mut v_t_2479_: *mut crate::leanh::LeanObject,
    mut v_h_2480_: *mut crate::leanh::LeanObject,
    mut v_k_2481_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2482_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2482_ = l_Lean_Elab_Tactic_Conv_PatternMatchState_ctorElim___redArg(v_t_2479_, v_k_2481_);
    return v___x_2482_;
}
pub unsafe fn l_Lean_Elab_Tactic_Conv_PatternMatchState_ctorElim___boxed(
    mut v_motive_2483_: *mut crate::leanh::LeanObject,
    mut v_ctorIdx_2484_: *mut crate::leanh::LeanObject,
    mut v_t_2485_: *mut crate::leanh::LeanObject,
    mut v_h_2486_: *mut crate::leanh::LeanObject,
    mut v_k_2487_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2488_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2488_ = l_Lean_Elab_Tactic_Conv_PatternMatchState_ctorElim(
        v_motive_2483_,
        v_ctorIdx_2484_,
        v_t_2485_,
        v_h_2486_,
        v_k_2487_,
    );
    crate::leanh::lean_dec(v_ctorIdx_2484_);
    return v_res_2488_;
}
pub unsafe fn l_Lean_Elab_Tactic_Conv_PatternMatchState_all_elim___redArg(
    mut v_t_2489_: *mut crate::leanh::LeanObject,
    mut v_all_2490_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2491_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2491_ =
        l_Lean_Elab_Tactic_Conv_PatternMatchState_ctorElim___redArg(v_t_2489_, v_all_2490_);
    return v___x_2491_;
}
pub unsafe fn l_Lean_Elab_Tactic_Conv_PatternMatchState_all_elim(
    mut v_motive_2492_: *mut crate::leanh::LeanObject,
    mut v_t_2493_: *mut crate::leanh::LeanObject,
    mut v_h_2494_: *mut crate::leanh::LeanObject,
    mut v_all_2495_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2496_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2496_ =
        l_Lean_Elab_Tactic_Conv_PatternMatchState_ctorElim___redArg(v_t_2493_, v_all_2495_);
    return v___x_2496_;
}
pub unsafe fn l_Lean_Elab_Tactic_Conv_PatternMatchState_occs_elim___redArg(
    mut v_t_2497_: *mut crate::leanh::LeanObject,
    mut v_occs_2498_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2499_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2499_ =
        l_Lean_Elab_Tactic_Conv_PatternMatchState_ctorElim___redArg(v_t_2497_, v_occs_2498_);
    return v___x_2499_;
}
pub unsafe fn l_Lean_Elab_Tactic_Conv_PatternMatchState_occs_elim(
    mut v_motive_2500_: *mut crate::leanh::LeanObject,
    mut v_t_2501_: *mut crate::leanh::LeanObject,
    mut v_h_2502_: *mut crate::leanh::LeanObject,
    mut v_occs_2503_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2504_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2504_ =
        l_Lean_Elab_Tactic_Conv_PatternMatchState_ctorElim___redArg(v_t_2501_, v_occs_2503_);
    return v___x_2504_;
}
pub unsafe fn l_Lean_Elab_Tactic_Conv_PatternMatchState_isDone(
    mut v_x_2505_: *mut crate::leanh::LeanObject,
) -> u8 {
    if crate::leanh::lean_obj_tag(v_x_2505_) == 0 {
        let mut v___x_2506_: u8 = 0;
        v___x_2506_ = 0;
        return v___x_2506_;
    } else {
        let mut v_remaining_2507_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2508_: u8 = 0;
        v_remaining_2507_ = crate::leanh::lean_ctor_get(v_x_2505_, 2);
        v___x_2508_ = l_List_isEmpty___redArg(v_remaining_2507_);
        return v___x_2508_;
    }
}
pub unsafe fn l_Lean_Elab_Tactic_Conv_PatternMatchState_isDone___boxed(
    mut v_x_2509_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2510_: u8 = 0;
    let mut v_r_2511_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2510_ = l_Lean_Elab_Tactic_Conv_PatternMatchState_isDone(v_x_2509_);
    crate::leanh::lean_dec_ref(v_x_2509_);
    v_r_2511_ = crate::leanh::lean_box((v_res_2510_) as usize);
    return v_r_2511_;
}
pub unsafe fn l_Lean_Elab_Tactic_Conv_PatternMatchState_isReady(
    mut v_x_2512_: *mut crate::leanh::LeanObject,
) -> u8 {
    if crate::leanh::lean_obj_tag(v_x_2512_) == 0 {
        let mut v___x_2513_: u8 = 0;
        v___x_2513_ = 1;
        return v___x_2513_;
    } else {
        let mut v_remaining_2514_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_remaining_2514_ = crate::leanh::lean_ctor_get(v_x_2512_, 2);
        if crate::leanh::lean_obj_tag(v_remaining_2514_) == 1 {
            let mut v_head_2515_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_idx_2516_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_fst_2517_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2518_: u8 = 0;
            v_head_2515_ = crate::leanh::lean_ctor_get(v_remaining_2514_, 0);
            v_idx_2516_ = crate::leanh::lean_ctor_get(v_x_2512_, 1);
            v_fst_2517_ = crate::leanh::lean_ctor_get(v_head_2515_, 0);
            v___x_2518_ = lean_nat_dec_eq(v_idx_2516_, v_fst_2517_);
            return v___x_2518_;
        } else {
            let mut v___x_2519_: u8 = 0;
            v___x_2519_ = 0;
            return v___x_2519_;
        }
    }
}
pub unsafe fn l_Lean_Elab_Tactic_Conv_PatternMatchState_isReady___boxed(
    mut v_x_2520_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2521_: u8 = 0;
    let mut v_r_2522_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2521_ = l_Lean_Elab_Tactic_Conv_PatternMatchState_isReady(v_x_2520_);
    crate::leanh::lean_dec_ref(v_x_2520_);
    v_r_2522_ = crate::leanh::lean_box((v_res_2521_) as usize);
    return v_r_2522_;
}
pub unsafe fn l_Lean_Elab_Tactic_Conv_PatternMatchState_skip(
    mut v_x_2523_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_subgoals_2524_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_idx_2525_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_remaining_2526_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2528_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2529_: u8 = 0;
    let mut v___x_2530_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2531_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2533_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2534_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2535_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_2523_) == 1 {
                    v_subgoals_2524_ = crate::leanh::lean_ctor_get(v_x_2523_, 0);
                    v_idx_2525_ = crate::leanh::lean_ctor_get(v_x_2523_, 1);
                    v_remaining_2526_ = crate::leanh::lean_ctor_get(v_x_2523_, 2);
                    v_isSharedCheck_2535_ = (!crate::leanh::lean_is_exclusive(v_x_2523_)) as u8;
                    if v_isSharedCheck_2535_ == 0 {
                        v___x_2528_ = v_x_2523_;
                        v_isShared_2529_ = v_isSharedCheck_2535_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_remaining_2526_);
                        crate::leanh::lean_inc(v_idx_2525_);
                        crate::leanh::lean_inc(v_subgoals_2524_);
                        crate::leanh::lean_dec(v_x_2523_);
                        v___x_2528_ = crate::leanh::lean_box(0);
                        v_isShared_2529_ = v_isSharedCheck_2535_;
                        state = 1;
                        continue;
                    }
                } else {
                    return v_x_2523_;
                }
            }
            1 => {
                v___x_2530_ = crate::leanh::lean_unsigned_to_nat(1);
                v___x_2531_ = lean_nat_add(v_idx_2525_, v___x_2530_);
                crate::leanh::lean_dec(v_idx_2525_);
                if v_isShared_2529_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2528_, 1, v___x_2531_);
                    v___x_2533_ = v___x_2528_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2534_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2534_, 0, v_subgoals_2524_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2534_, 1, v___x_2531_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2534_, 2, v_remaining_2526_);
                    v___x_2533_ = v_reuseFailAlloc_2534_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2533_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_Tactic_Conv_PatternMatchState_accept(
    mut v_mvarId_2536_: *mut crate::leanh::LeanObject,
    mut v_x_2537_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_subgoals_2538_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2540_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2541_: u8 = 0;
    let mut v___x_2542_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2544_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2545_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2546_: u8 = 0;
    let mut v_remaining_2547_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_2548_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_subgoals_2549_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_idx_2550_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2552_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2553_: u8 = 0;
    let mut v_tail_2554_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2555_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2557_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2558_: u8 = 0;
    let mut v___x_2560_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2561_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2562_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2563_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2565_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2566_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2567_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2568_: u8 = 0;
    let mut v_unused_2569_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2570_: u8 = 0;
    let mut v_unused_2571_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_2537_) == 0 {
                    v_subgoals_2538_ = crate::leanh::lean_ctor_get(v_x_2537_, 0);
                    v_isSharedCheck_2546_ = (!crate::leanh::lean_is_exclusive(v_x_2537_)) as u8;
                    if v_isSharedCheck_2546_ == 0 {
                        v___x_2540_ = v_x_2537_;
                        v_isShared_2541_ = v_isSharedCheck_2546_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_subgoals_2538_);
                        crate::leanh::lean_dec(v_x_2537_);
                        v___x_2540_ = crate::leanh::lean_box(0);
                        v_isShared_2541_ = v_isSharedCheck_2546_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_remaining_2547_ = crate::leanh::lean_ctor_get(v_x_2537_, 2);
                    if crate::leanh::lean_obj_tag(v_remaining_2547_) == 1 {
                        crate::leanh::lean_inc_ref(v_remaining_2547_);
                        v_head_2548_ = crate::leanh::lean_ctor_get(v_remaining_2547_, 0);
                        crate::leanh::lean_inc(v_head_2548_);
                        v_subgoals_2549_ = crate::leanh::lean_ctor_get(v_x_2537_, 0);
                        v_idx_2550_ = crate::leanh::lean_ctor_get(v_x_2537_, 1);
                        v_isSharedCheck_2570_ = (!crate::leanh::lean_is_exclusive(v_x_2537_)) as u8;
                        if v_isSharedCheck_2570_ == 0 {
                            v_unused_2571_ = crate::leanh::lean_ctor_get(v_x_2537_, 2);
                            crate::leanh::lean_dec(v_unused_2571_);
                            v___x_2552_ = v_x_2537_;
                            v_isShared_2553_ = v_isSharedCheck_2570_;
                            state = 3;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_idx_2550_);
                            crate::leanh::lean_inc(v_subgoals_2549_);
                            crate::leanh::lean_dec(v_x_2537_);
                            v___x_2552_ = crate::leanh::lean_box(0);
                            v_isShared_2553_ = v_isSharedCheck_2570_;
                            state = 3;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec(v_mvarId_2536_);
                        return v_x_2537_;
                    }
                }
            }
            1 => {
                v___x_2542_ = lean_array_push(v_subgoals_2538_, v_mvarId_2536_);
                if v_isShared_2541_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2540_, 0, v___x_2542_);
                    v___x_2544_ = v___x_2540_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2545_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2545_, 0, v___x_2542_);
                    v___x_2544_ = v_reuseFailAlloc_2545_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2544_;
            }
            3 => {
                v_tail_2554_ = crate::leanh::lean_ctor_get(v_remaining_2547_, 1);
                crate::leanh::lean_inc(v_tail_2554_);
                crate::leanh::lean_dec_ref_known(v_remaining_2547_, 2);
                v_snd_2555_ = crate::leanh::lean_ctor_get(v_head_2548_, 1);
                v_isSharedCheck_2568_ = (!crate::leanh::lean_is_exclusive(v_head_2548_)) as u8;
                if v_isSharedCheck_2568_ == 0 {
                    v_unused_2569_ = crate::leanh::lean_ctor_get(v_head_2548_, 0);
                    crate::leanh::lean_dec(v_unused_2569_);
                    v___x_2557_ = v_head_2548_;
                    v_isShared_2558_ = v_isSharedCheck_2568_;
                    state = 4;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snd_2555_);
                    crate::leanh::lean_dec(v_head_2548_);
                    v___x_2557_ = crate::leanh::lean_box(0);
                    v_isShared_2558_ = v_isSharedCheck_2568_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                if v_isShared_2558_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2557_, 1, v_mvarId_2536_);
                    crate::leanh::lean_ctor_set(v___x_2557_, 0, v_snd_2555_);
                    v___x_2560_ = v___x_2557_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_2567_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2567_, 0, v_snd_2555_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2567_, 1, v_mvarId_2536_);
                    v___x_2560_ = v_reuseFailAlloc_2567_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v___x_2561_ = lean_array_push(v_subgoals_2549_, v___x_2560_);
                v___x_2562_ = crate::leanh::lean_unsigned_to_nat(1);
                v___x_2563_ = lean_nat_add(v_idx_2550_, v___x_2562_);
                crate::leanh::lean_dec(v_idx_2550_);
                if v_isShared_2553_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2552_, 2, v_tail_2554_);
                    crate::leanh::lean_ctor_set(v___x_2552_, 1, v___x_2563_);
                    crate::leanh::lean_ctor_set(v___x_2552_, 0, v___x_2561_);
                    v___x_2565_ = v___x_2552_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_2566_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2566_, 0, v___x_2561_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2566_, 1, v___x_2563_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2566_, 2, v_tail_2554_);
                    v___x_2565_ = v_reuseFailAlloc_2566_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_2565_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Conv_Pattern_0__Lean_Elab_Tactic_Conv_pre_spec__0___redArg(
    mut v_as_2572_: *mut crate::leanh::LeanObject,
    mut v_sz_2573_: usize,
    mut v_i_2574_: usize,
    mut v_b_2575_: *mut crate::leanh::LeanObject,
    mut v___y_2576_: *mut crate::leanh::LeanObject,
    mut v___y_2577_: *mut crate::leanh::LeanObject,
    mut v___y_2578_: *mut crate::leanh::LeanObject,
    mut v___y_2579_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2581_: u8 = 0;
    let mut v___x_2582_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2583_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2584_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2585_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2586_: usize = 0;
    let mut v___x_2587_: usize = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2581_ = lean_usize_dec_lt(v_i_2574_, v_sz_2573_);
                if v___x_2581_ == 0 {
                    v___x_2582_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2582_, 0, v_b_2575_);
                    return v___x_2582_;
                } else {
                    v_a_2583_ = lean_array_uget_borrowed(v_as_2572_, v_i_2574_);
                    crate::leanh::lean_inc(v_a_2583_);
                    v___x_2584_ = l_Lean_Meta_mkCongrFun(
                        v_b_2575_,
                        v_a_2583_,
                        v___y_2576_,
                        v___y_2577_,
                        v___y_2578_,
                        v___y_2579_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_2584_) == 0 {
                        v_a_2585_ = crate::leanh::lean_ctor_get(v___x_2584_, 0);
                        crate::leanh::lean_inc(v_a_2585_);
                        crate::leanh::lean_dec_ref_known(v___x_2584_, 1);
                        v___x_2586_ = 1usize;
                        v___x_2587_ = lean_usize_add(v_i_2574_, v___x_2586_);
                        v_i_2574_ = v___x_2587_;
                        v_b_2575_ = v_a_2585_;
                        state = 0;
                        continue;
                    } else {
                        return v___x_2584_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Conv_Pattern_0__Lean_Elab_Tactic_Conv_pre_spec__0___redArg___boxed(
    mut v_as_2589_: *mut crate::leanh::LeanObject,
    mut v_sz_2590_: *mut crate::leanh::LeanObject,
    mut v_i_2591_: *mut crate::leanh::LeanObject,
    mut v_b_2592_: *mut crate::leanh::LeanObject,
    mut v___y_2593_: *mut crate::leanh::LeanObject,
    mut v___y_2594_: *mut crate::leanh::LeanObject,
    mut v___y_2595_: *mut crate::leanh::LeanObject,
    mut v___y_2596_: *mut crate::leanh::LeanObject,
    mut v___y_2597_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_boxed_2598_: usize = 0;
    let mut v_i_boxed_2599_: usize = 0;
    let mut v_res_2600_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_2598_ = crate::leanh::lean_unbox_usize(v_sz_2590_);
    crate::leanh::lean_dec(v_sz_2590_);
    v_i_boxed_2599_ = crate::leanh::lean_unbox_usize(v_i_2591_);
    crate::leanh::lean_dec(v_i_2591_);
    v_res_2600_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Conv_Pattern_0__Lean_Elab_Tactic_Conv_pre_spec__0___redArg(v_as_2589_, v_sz_boxed_2598_, v_i_boxed_2599_, v_b_2592_, v___y_2593_, v___y_2594_, v___y_2595_, v___y_2596_);
    crate::leanh::lean_dec(v___y_2596_);
    crate::leanh::lean_dec_ref(v___y_2595_);
    crate::leanh::lean_dec(v___y_2594_);
    crate::leanh::lean_dec_ref(v___y_2593_);
    crate::leanh::lean_dec_ref(v_as_2589_);
    return v_res_2600_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Conv_Pattern_0__Lean_Elab_Tactic_Conv_pre(
    mut v_pattern_2603_: *mut crate::leanh::LeanObject,
    mut v_state_2604_: *mut crate::leanh::LeanObject,
    mut v_e_2605_: *mut crate::leanh::LeanObject,
    mut v_a_2606_: *mut crate::leanh::LeanObject,
    mut v_a_2607_: *mut crate::leanh::LeanObject,
    mut v_a_2608_: *mut crate::leanh::LeanObject,
    mut v_a_2609_: *mut crate::leanh::LeanObject,
    mut v_a_2610_: *mut crate::leanh::LeanObject,
    mut v_a_2611_: *mut crate::leanh::LeanObject,
    mut v_a_2612_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2614_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2615_: u8 = 0;
    let mut v___x_2616_: u8 = 0;
    let mut v___x_2617_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2618_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2620_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2621_: u8 = 0;
    let mut v_val_2622_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2624_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2625_: u8 = 0;
    let mut v_fst_2626_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2627_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2628_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2629_: u8 = 0;
    let mut v___x_2630_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2631_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2632_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2633_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2635_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2636_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2637_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2638_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2639_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_2640_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2641_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2642_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2643_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2644_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2645_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_2646_: usize = 0;
    let mut v___x_2647_: usize = 0;
    let mut v___x_2648_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2649_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2651_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2652_: u8 = 0;
    let mut v___x_2653_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2655_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2656_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2657_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2659_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2660_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2661_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2662_: u8 = 0;
    let mut v_a_2663_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2665_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2666_: u8 = 0;
    let mut v___x_2668_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2669_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2670_: u8 = 0;
    let mut v_a_2671_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2673_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2674_: u8 = 0;
    let mut v___x_2676_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2677_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2678_: u8 = 0;
    let mut v_isSharedCheck_2679_: u8 = 0;
    let mut v___x_2680_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2682_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2683_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2684_: u8 = 0;
    let mut v_a_2685_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2687_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2688_: u8 = 0;
    let mut v___x_2690_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2691_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2692_: u8 = 0;
    let mut v___x_2693_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2694_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2695_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2696_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2614_ = lean_st_ref_get(v_state_2604_);
                v___x_2615_ = l_Lean_Elab_Tactic_Conv_PatternMatchState_isDone(v___x_2614_);
                crate::leanh::lean_dec(v___x_2614_);
                v___x_2616_ = 1;
                if v___x_2615_ == 0 {
                    v___x_2617_ = l_Lean_Elab_Tactic_Conv_matchPattern_x3f(
                        v_pattern_2603_,
                        v_e_2605_,
                        v_a_2609_,
                        v_a_2610_,
                        v_a_2611_,
                        v_a_2612_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_2617_) == 0 {
                        v_a_2618_ = crate::leanh::lean_ctor_get(v___x_2617_, 0);
                        v_isSharedCheck_2684_ =
                            (!crate::leanh::lean_is_exclusive(v___x_2617_)) as u8;
                        if v_isSharedCheck_2684_ == 0 {
                            v___x_2620_ = v___x_2617_;
                            v_isShared_2621_ = v_isSharedCheck_2684_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_2618_);
                            crate::leanh::lean_dec(v___x_2617_);
                            v___x_2620_ = crate::leanh::lean_box(0);
                            v_isShared_2621_ = v_isSharedCheck_2684_;
                            state = 1;
                            continue;
                        }
                    } else {
                        v_a_2685_ = crate::leanh::lean_ctor_get(v___x_2617_, 0);
                        v_isSharedCheck_2692_ =
                            (!crate::leanh::lean_is_exclusive(v___x_2617_)) as u8;
                        if v_isSharedCheck_2692_ == 0 {
                            v___x_2687_ = v___x_2617_;
                            v_isShared_2688_ = v_isSharedCheck_2692_;
                            state = 12;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_2685_);
                            crate::leanh::lean_dec(v___x_2617_);
                            v___x_2687_ = crate::leanh::lean_box(0);
                            v_isShared_2688_ = v_isSharedCheck_2692_;
                            state = 12;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_pattern_2603_);
                    v___x_2693_ = crate::leanh::lean_box(0);
                    v___x_2694_ = crate::leanh::lean_alloc_ctor(0, 2, (1) as u32);
                    crate::leanh::lean_ctor_set(v___x_2694_, 0, v_e_2605_);
                    crate::leanh::lean_ctor_set(v___x_2694_, 1, v___x_2693_);
                    crate::leanh::lean_ctor_set_uint8(
                        v___x_2694_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2) as u32,
                        v___x_2616_,
                    );
                    v___x_2695_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2695_, 0, v___x_2694_);
                    v___x_2696_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2696_, 0, v___x_2695_);
                    return v___x_2696_;
                }
            }
            1 => {
                if crate::leanh::lean_obj_tag(v_a_2618_) == 1 {
                    v_val_2622_ = crate::leanh::lean_ctor_get(v_a_2618_, 0);
                    v_isSharedCheck_2679_ = (!crate::leanh::lean_is_exclusive(v_a_2618_)) as u8;
                    if v_isSharedCheck_2679_ == 0 {
                        v___x_2624_ = v_a_2618_;
                        v_isShared_2625_ = v_isSharedCheck_2679_;
                        state = 2;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_val_2622_);
                        crate::leanh::lean_dec(v_a_2618_);
                        v___x_2624_ = crate::leanh::lean_box(0);
                        v_isShared_2625_ = v_isSharedCheck_2679_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_a_2618_);
                    v___x_2680_ = l___private_Lean_Elab_Tactic_Conv_Pattern_0__Lean_Elab_Tactic_Conv_pre___closed__0;
                    if v_isShared_2621_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_2620_, 0, v___x_2680_);
                        v___x_2682_ = v___x_2620_;
                        state = 11;
                        continue;
                    } else {
                        v_reuseFailAlloc_2683_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2683_, 0, v___x_2680_);
                        v___x_2682_ = v_reuseFailAlloc_2683_;
                        state = 11;
                        continue;
                    }
                }
            }
            2 => {
                v_fst_2626_ = crate::leanh::lean_ctor_get(v_val_2622_, 0);
                crate::leanh::lean_inc(v_fst_2626_);
                v_snd_2627_ = crate::leanh::lean_ctor_get(v_val_2622_, 1);
                crate::leanh::lean_inc(v_snd_2627_);
                crate::leanh::lean_dec(v_val_2622_);
                v___x_2628_ = lean_st_ref_get(v_state_2604_);
                v___x_2629_ = l_Lean_Elab_Tactic_Conv_PatternMatchState_isReady(v___x_2628_);
                crate::leanh::lean_dec(v___x_2628_);
                if v___x_2629_ == 0 {
                    crate::leanh::lean_dec(v_snd_2627_);
                    crate::leanh::lean_dec(v_fst_2626_);
                    crate::leanh::lean_del_object(v___x_2624_);
                    v___x_2630_ = lean_st_ref_take(v_state_2604_);
                    v___x_2631_ = l_Lean_Elab_Tactic_Conv_PatternMatchState_skip(v___x_2630_);
                    v___x_2632_ = lean_st_ref_set(v_state_2604_, v___x_2631_);
                    v___x_2633_ = l___private_Lean_Elab_Tactic_Conv_Pattern_0__Lean_Elab_Tactic_Conv_pre___closed__0;
                    if v_isShared_2621_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_2620_, 0, v___x_2633_);
                        v___x_2635_ = v___x_2620_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_2636_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2636_, 0, v___x_2633_);
                        v___x_2635_ = v_reuseFailAlloc_2636_;
                        state = 3;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_2620_);
                    v___x_2637_ = crate::leanh::lean_box(0);
                    v___x_2638_ = l_Lean_Elab_Tactic_Conv_mkConvGoalFor(
                        v_fst_2626_,
                        v___x_2637_,
                        v_a_2609_,
                        v_a_2610_,
                        v_a_2611_,
                        v_a_2612_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_2638_) == 0 {
                        v_a_2639_ = crate::leanh::lean_ctor_get(v___x_2638_, 0);
                        crate::leanh::lean_inc(v_a_2639_);
                        crate::leanh::lean_dec_ref_known(v___x_2638_, 1);
                        v_fst_2640_ = crate::leanh::lean_ctor_get(v_a_2639_, 0);
                        crate::leanh::lean_inc(v_fst_2640_);
                        v_snd_2641_ = crate::leanh::lean_ctor_get(v_a_2639_, 1);
                        crate::leanh::lean_inc(v_snd_2641_);
                        crate::leanh::lean_dec(v_a_2639_);
                        v___x_2642_ = lean_st_ref_take(v_state_2604_);
                        v___x_2643_ = l_Lean_Expr_mvarId_x21(v_snd_2641_);
                        v___x_2644_ = l_Lean_Elab_Tactic_Conv_PatternMatchState_accept(
                            v___x_2643_,
                            v___x_2642_,
                        );
                        v___x_2645_ = lean_st_ref_set(v_state_2604_, v___x_2644_);
                        v_sz_2646_ = lean_array_size(v_snd_2627_);
                        v___x_2647_ = 0usize;
                        v___x_2648_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Conv_Pattern_0__Lean_Elab_Tactic_Conv_pre_spec__0___redArg(v_snd_2627_, v_sz_2646_, v___x_2647_, v_snd_2641_, v_a_2609_, v_a_2610_, v_a_2611_, v_a_2612_);
                        if crate::leanh::lean_obj_tag(v___x_2648_) == 0 {
                            v_a_2649_ = crate::leanh::lean_ctor_get(v___x_2648_, 0);
                            v_isSharedCheck_2662_ =
                                (!crate::leanh::lean_is_exclusive(v___x_2648_)) as u8;
                            if v_isSharedCheck_2662_ == 0 {
                                v___x_2651_ = v___x_2648_;
                                v_isShared_2652_ = v_isSharedCheck_2662_;
                                state = 4;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_2649_);
                                crate::leanh::lean_dec(v___x_2648_);
                                v___x_2651_ = crate::leanh::lean_box(0);
                                v_isShared_2652_ = v_isSharedCheck_2662_;
                                state = 4;
                                continue;
                            }
                        } else {
                            crate::leanh::lean_dec(v_fst_2640_);
                            crate::leanh::lean_dec(v_snd_2627_);
                            crate::leanh::lean_del_object(v___x_2624_);
                            v_a_2663_ = crate::leanh::lean_ctor_get(v___x_2648_, 0);
                            v_isSharedCheck_2670_ =
                                (!crate::leanh::lean_is_exclusive(v___x_2648_)) as u8;
                            if v_isSharedCheck_2670_ == 0 {
                                v___x_2665_ = v___x_2648_;
                                v_isShared_2666_ = v_isSharedCheck_2670_;
                                state = 7;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_2663_);
                                crate::leanh::lean_dec(v___x_2648_);
                                v___x_2665_ = crate::leanh::lean_box(0);
                                v_isShared_2666_ = v_isSharedCheck_2670_;
                                state = 7;
                                continue;
                            }
                        }
                    } else {
                        crate::leanh::lean_dec(v_snd_2627_);
                        crate::leanh::lean_del_object(v___x_2624_);
                        v_a_2671_ = crate::leanh::lean_ctor_get(v___x_2638_, 0);
                        v_isSharedCheck_2678_ =
                            (!crate::leanh::lean_is_exclusive(v___x_2638_)) as u8;
                        if v_isSharedCheck_2678_ == 0 {
                            v___x_2673_ = v___x_2638_;
                            v_isShared_2674_ = v_isSharedCheck_2678_;
                            state = 9;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_2671_);
                            crate::leanh::lean_dec(v___x_2638_);
                            v___x_2673_ = crate::leanh::lean_box(0);
                            v_isShared_2674_ = v_isSharedCheck_2678_;
                            state = 9;
                            continue;
                        }
                    }
                }
            }
            3 => {
                return v___x_2635_;
            }
            4 => {
                v___x_2653_ = l_Lean_mkAppN(v_fst_2640_, v_snd_2627_);
                crate::leanh::lean_dec(v_snd_2627_);
                if v_isShared_2625_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2624_, 0, v_a_2649_);
                    v___x_2655_ = v___x_2624_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_2661_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2661_, 0, v_a_2649_);
                    v___x_2655_ = v_reuseFailAlloc_2661_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v___x_2656_ = crate::leanh::lean_alloc_ctor(0, 2, (1) as u32);
                crate::leanh::lean_ctor_set(v___x_2656_, 0, v___x_2653_);
                crate::leanh::lean_ctor_set(v___x_2656_, 1, v___x_2655_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_2656_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2) as u32,
                    v___x_2616_,
                );
                v___x_2657_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2657_, 0, v___x_2656_);
                if v_isShared_2652_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2651_, 0, v___x_2657_);
                    v___x_2659_ = v___x_2651_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_2660_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2660_, 0, v___x_2657_);
                    v___x_2659_ = v_reuseFailAlloc_2660_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_2659_;
            }
            7 => {
                if v_isShared_2666_ == 0 {
                    v___x_2668_ = v___x_2665_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_2669_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2669_, 0, v_a_2663_);
                    v___x_2668_ = v_reuseFailAlloc_2669_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_2668_;
            }
            9 => {
                if v_isShared_2674_ == 0 {
                    v___x_2676_ = v___x_2673_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_2677_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2677_, 0, v_a_2671_);
                    v___x_2676_ = v_reuseFailAlloc_2677_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_2676_;
            }
            11 => {
                return v___x_2682_;
            }
            12 => {
                if v_isShared_2688_ == 0 {
                    v___x_2690_ = v___x_2687_;
                    state = 13;
                    continue;
                } else {
                    v_reuseFailAlloc_2691_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2691_, 0, v_a_2685_);
                    v___x_2690_ = v_reuseFailAlloc_2691_;
                    state = 13;
                    continue;
                }
            }
            13 => {
                return v___x_2690_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Elab_Tactic_Conv_Pattern_0__Lean_Elab_Tactic_Conv_pre___boxed(
    mut v_pattern_2697_: *mut crate::leanh::LeanObject,
    mut v_state_2698_: *mut crate::leanh::LeanObject,
    mut v_e_2699_: *mut crate::leanh::LeanObject,
    mut v_a_2700_: *mut crate::leanh::LeanObject,
    mut v_a_2701_: *mut crate::leanh::LeanObject,
    mut v_a_2702_: *mut crate::leanh::LeanObject,
    mut v_a_2703_: *mut crate::leanh::LeanObject,
    mut v_a_2704_: *mut crate::leanh::LeanObject,
    mut v_a_2705_: *mut crate::leanh::LeanObject,
    mut v_a_2706_: *mut crate::leanh::LeanObject,
    mut v_a_2707_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2708_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2708_ = l___private_Lean_Elab_Tactic_Conv_Pattern_0__Lean_Elab_Tactic_Conv_pre(
        v_pattern_2697_,
        v_state_2698_,
        v_e_2699_,
        v_a_2700_,
        v_a_2701_,
        v_a_2702_,
        v_a_2703_,
        v_a_2704_,
        v_a_2705_,
        v_a_2706_,
    );
    crate::leanh::lean_dec(v_a_2706_);
    crate::leanh::lean_dec_ref(v_a_2705_);
    crate::leanh::lean_dec(v_a_2704_);
    crate::leanh::lean_dec_ref(v_a_2703_);
    crate::leanh::lean_dec(v_a_2702_);
    crate::leanh::lean_dec_ref(v_a_2701_);
    crate::leanh::lean_dec(v_a_2700_);
    crate::leanh::lean_dec(v_state_2698_);
    return v_res_2708_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Conv_Pattern_0__Lean_Elab_Tactic_Conv_pre_spec__0(
    mut v_as_2709_: *mut crate::leanh::LeanObject,
    mut v_sz_2710_: usize,
    mut v_i_2711_: usize,
    mut v_b_2712_: *mut crate::leanh::LeanObject,
    mut v___y_2713_: *mut crate::leanh::LeanObject,
    mut v___y_2714_: *mut crate::leanh::LeanObject,
    mut v___y_2715_: *mut crate::leanh::LeanObject,
    mut v___y_2716_: *mut crate::leanh::LeanObject,
    mut v___y_2717_: *mut crate::leanh::LeanObject,
    mut v___y_2718_: *mut crate::leanh::LeanObject,
    mut v___y_2719_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2721_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2721_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Conv_Pattern_0__Lean_Elab_Tactic_Conv_pre_spec__0___redArg(v_as_2709_, v_sz_2710_, v_i_2711_, v_b_2712_, v___y_2716_, v___y_2717_, v___y_2718_, v___y_2719_);
    return v___x_2721_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Conv_Pattern_0__Lean_Elab_Tactic_Conv_pre_spec__0___boxed(
    mut v_as_2722_: *mut crate::leanh::LeanObject,
    mut v_sz_2723_: *mut crate::leanh::LeanObject,
    mut v_i_2724_: *mut crate::leanh::LeanObject,
    mut v_b_2725_: *mut crate::leanh::LeanObject,
    mut v___y_2726_: *mut crate::leanh::LeanObject,
    mut v___y_2727_: *mut crate::leanh::LeanObject,
    mut v___y_2728_: *mut crate::leanh::LeanObject,
    mut v___y_2729_: *mut crate::leanh::LeanObject,
    mut v___y_2730_: *mut crate::leanh::LeanObject,
    mut v___y_2731_: *mut crate::leanh::LeanObject,
    mut v___y_2732_: *mut crate::leanh::LeanObject,
    mut v___y_2733_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_boxed_2734_: usize = 0;
    let mut v_i_boxed_2735_: usize = 0;
    let mut v_res_2736_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_2734_ = crate::leanh::lean_unbox_usize(v_sz_2723_);
    crate::leanh::lean_dec(v_sz_2723_);
    v_i_boxed_2735_ = crate::leanh::lean_unbox_usize(v_i_2724_);
    crate::leanh::lean_dec(v_i_2724_);
    v_res_2736_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Conv_Pattern_0__Lean_Elab_Tactic_Conv_pre_spec__0(v_as_2722_, v_sz_boxed_2734_, v_i_boxed_2735_, v_b_2725_, v___y_2726_, v___y_2727_, v___y_2728_, v___y_2729_, v___y_2730_, v___y_2731_, v___y_2732_);
    crate::leanh::lean_dec(v___y_2732_);
    crate::leanh::lean_dec_ref(v___y_2731_);
    crate::leanh::lean_dec(v___y_2730_);
    crate::leanh::lean_dec_ref(v___y_2729_);
    crate::leanh::lean_dec(v___y_2728_);
    crate::leanh::lean_dec_ref(v___y_2727_);
    crate::leanh::lean_dec(v___y_2726_);
    crate::leanh::lean_dec_ref(v_as_2722_);
    return v_res_2736_;
}
pub unsafe fn _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__0___redArg___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2737_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2738_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2739_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2737_ = crate::leanh::lean_box(0);
    v___x_2738_ = l_Lean_Elab_unsupportedSyntaxExceptionId;
    v___x_2739_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2739_, 0, v___x_2738_);
    crate::leanh::lean_ctor_set(v___x_2739_, 1, v___x_2737_);
    return v___x_2739_;
}
pub unsafe fn l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__0___redArg()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2741_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2742_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2741_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__0___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__0___redArg___closed__0_once), _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__0___redArg___closed__0);
    v___x_2742_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2742_, 0, v___x_2741_);
    return v___x_2742_;
}
pub unsafe fn l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__0___redArg___boxed(
    mut v___y_2743_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2744_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2744_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__0___redArg();
    return v_res_2744_;
}
pub unsafe fn l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__0(
    mut v_00_u03b1_2745_: *mut crate::leanh::LeanObject,
    mut v___y_2746_: *mut crate::leanh::LeanObject,
    mut v___y_2747_: *mut crate::leanh::LeanObject,
    mut v___y_2748_: *mut crate::leanh::LeanObject,
    mut v___y_2749_: *mut crate::leanh::LeanObject,
    mut v___y_2750_: *mut crate::leanh::LeanObject,
    mut v___y_2751_: *mut crate::leanh::LeanObject,
    mut v___y_2752_: *mut crate::leanh::LeanObject,
    mut v___y_2753_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2755_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2755_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__0___redArg();
    return v___x_2755_;
}
pub unsafe fn l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__0___boxed(
    mut v_00_u03b1_2756_: *mut crate::leanh::LeanObject,
    mut v___y_2757_: *mut crate::leanh::LeanObject,
    mut v___y_2758_: *mut crate::leanh::LeanObject,
    mut v___y_2759_: *mut crate::leanh::LeanObject,
    mut v___y_2760_: *mut crate::leanh::LeanObject,
    mut v___y_2761_: *mut crate::leanh::LeanObject,
    mut v___y_2762_: *mut crate::leanh::LeanObject,
    mut v___y_2763_: *mut crate::leanh::LeanObject,
    mut v___y_2764_: *mut crate::leanh::LeanObject,
    mut v___y_2765_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2766_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2766_ =
        l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__0(
            v_00_u03b1_2756_,
            v___y_2757_,
            v___y_2758_,
            v___y_2759_,
            v___y_2760_,
            v___y_2761_,
            v___y_2762_,
            v___y_2763_,
            v___y_2764_,
        );
    crate::leanh::lean_dec(v___y_2764_);
    crate::leanh::lean_dec_ref(v___y_2763_);
    crate::leanh::lean_dec(v___y_2762_);
    crate::leanh::lean_dec_ref(v___y_2761_);
    crate::leanh::lean_dec(v___y_2760_);
    crate::leanh::lean_dec_ref(v___y_2759_);
    crate::leanh::lean_dec(v___y_2758_);
    crate::leanh::lean_dec_ref(v___y_2757_);
    return v_res_2766_;
}
pub unsafe fn l_Lean_Elab_Term_withoutErrToSorry___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__2___redArg(
    mut v_a_2767_: *mut crate::leanh::LeanObject,
    mut v___y_2768_: *mut crate::leanh::LeanObject,
    mut v___y_2769_: *mut crate::leanh::LeanObject,
    mut v___y_2770_: *mut crate::leanh::LeanObject,
    mut v___y_2771_: *mut crate::leanh::LeanObject,
    mut v___y_2772_: *mut crate::leanh::LeanObject,
    mut v___y_2773_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2775_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2775_ = l_Lean_Elab_Term_withoutErrToSorryImp___redArg(
        v_a_2767_,
        v___y_2768_,
        v___y_2769_,
        v___y_2770_,
        v___y_2771_,
        v___y_2772_,
        v___y_2773_,
    );
    return v___x_2775_;
}
pub unsafe fn l_Lean_Elab_Term_withoutErrToSorry___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__2___redArg___boxed(
    mut v_a_2776_: *mut crate::leanh::LeanObject,
    mut v___y_2777_: *mut crate::leanh::LeanObject,
    mut v___y_2778_: *mut crate::leanh::LeanObject,
    mut v___y_2779_: *mut crate::leanh::LeanObject,
    mut v___y_2780_: *mut crate::leanh::LeanObject,
    mut v___y_2781_: *mut crate::leanh::LeanObject,
    mut v___y_2782_: *mut crate::leanh::LeanObject,
    mut v___y_2783_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2784_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2784_ = l_Lean_Elab_Term_withoutErrToSorry___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__2___redArg(v_a_2776_, v___y_2777_, v___y_2778_, v___y_2779_, v___y_2780_, v___y_2781_, v___y_2782_);
    crate::leanh::lean_dec(v___y_2782_);
    crate::leanh::lean_dec_ref(v___y_2781_);
    crate::leanh::lean_dec(v___y_2780_);
    crate::leanh::lean_dec_ref(v___y_2779_);
    crate::leanh::lean_dec(v___y_2778_);
    crate::leanh::lean_dec_ref(v___y_2777_);
    return v_res_2784_;
}
pub unsafe fn l_Lean_Elab_Term_withoutErrToSorry___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__2(
    mut v_00_u03b1_2785_: *mut crate::leanh::LeanObject,
    mut v_a_2786_: *mut crate::leanh::LeanObject,
    mut v___y_2787_: *mut crate::leanh::LeanObject,
    mut v___y_2788_: *mut crate::leanh::LeanObject,
    mut v___y_2789_: *mut crate::leanh::LeanObject,
    mut v___y_2790_: *mut crate::leanh::LeanObject,
    mut v___y_2791_: *mut crate::leanh::LeanObject,
    mut v___y_2792_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2794_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2794_ = l_Lean_Elab_Term_withoutErrToSorryImp___redArg(
        v_a_2786_,
        v___y_2787_,
        v___y_2788_,
        v___y_2789_,
        v___y_2790_,
        v___y_2791_,
        v___y_2792_,
    );
    return v___x_2794_;
}
pub unsafe fn l_Lean_Elab_Term_withoutErrToSorry___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__2___boxed(
    mut v_00_u03b1_2795_: *mut crate::leanh::LeanObject,
    mut v_a_2796_: *mut crate::leanh::LeanObject,
    mut v___y_2797_: *mut crate::leanh::LeanObject,
    mut v___y_2798_: *mut crate::leanh::LeanObject,
    mut v___y_2799_: *mut crate::leanh::LeanObject,
    mut v___y_2800_: *mut crate::leanh::LeanObject,
    mut v___y_2801_: *mut crate::leanh::LeanObject,
    mut v___y_2802_: *mut crate::leanh::LeanObject,
    mut v___y_2803_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2804_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2804_ =
        l_Lean_Elab_Term_withoutErrToSorry___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__2(
            v_00_u03b1_2795_,
            v_a_2796_,
            v___y_2797_,
            v___y_2798_,
            v___y_2799_,
            v___y_2800_,
            v___y_2801_,
            v___y_2802_,
        );
    crate::leanh::lean_dec(v___y_2802_);
    crate::leanh::lean_dec_ref(v___y_2801_);
    crate::leanh::lean_dec(v___y_2800_);
    crate::leanh::lean_dec_ref(v___y_2799_);
    crate::leanh::lean_dec(v___y_2798_);
    crate::leanh::lean_dec_ref(v___y_2797_);
    return v_res_2804_;
}
pub unsafe fn l_Lean_Elab_Tactic_Conv_evalPattern___lam__0(
    mut v_e_2805_: *mut crate::leanh::LeanObject,
    mut v___y_2806_: *mut crate::leanh::LeanObject,
    mut v___y_2807_: *mut crate::leanh::LeanObject,
    mut v___y_2808_: *mut crate::leanh::LeanObject,
    mut v___y_2809_: *mut crate::leanh::LeanObject,
    mut v___y_2810_: *mut crate::leanh::LeanObject,
    mut v___y_2811_: *mut crate::leanh::LeanObject,
    mut v___y_2812_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2814_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2815_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2814_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2814_, 0, v_e_2805_);
    v___x_2815_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2815_, 0, v___x_2814_);
    return v___x_2815_;
}
pub unsafe fn l_Lean_Elab_Tactic_Conv_evalPattern___lam__0___boxed(
    mut v_e_2816_: *mut crate::leanh::LeanObject,
    mut v___y_2817_: *mut crate::leanh::LeanObject,
    mut v___y_2818_: *mut crate::leanh::LeanObject,
    mut v___y_2819_: *mut crate::leanh::LeanObject,
    mut v___y_2820_: *mut crate::leanh::LeanObject,
    mut v___y_2821_: *mut crate::leanh::LeanObject,
    mut v___y_2822_: *mut crate::leanh::LeanObject,
    mut v___y_2823_: *mut crate::leanh::LeanObject,
    mut v___y_2824_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2825_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2825_ = l_Lean_Elab_Tactic_Conv_evalPattern___lam__0(
        v_e_2816_,
        v___y_2817_,
        v___y_2818_,
        v___y_2819_,
        v___y_2820_,
        v___y_2821_,
        v___y_2822_,
        v___y_2823_,
    );
    crate::leanh::lean_dec(v___y_2823_);
    crate::leanh::lean_dec_ref(v___y_2822_);
    crate::leanh::lean_dec(v___y_2821_);
    crate::leanh::lean_dec_ref(v___y_2820_);
    crate::leanh::lean_dec(v___y_2819_);
    crate::leanh::lean_dec_ref(v___y_2818_);
    crate::leanh::lean_dec(v___y_2817_);
    return v_res_2825_;
}
pub unsafe fn l_Lean_Elab_Tactic_Conv_evalPattern___lam__1(
    mut v___x_2826_: *mut crate::leanh::LeanObject,
    mut v___x_2827_: *mut crate::leanh::LeanObject,
    mut v___x_2828_: u8,
    mut v___y_2829_: *mut crate::leanh::LeanObject,
    mut v___y_2830_: *mut crate::leanh::LeanObject,
    mut v___y_2831_: *mut crate::leanh::LeanObject,
    mut v___y_2832_: *mut crate::leanh::LeanObject,
    mut v___y_2833_: *mut crate::leanh::LeanObject,
    mut v___y_2834_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2836_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2837_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2838_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2839_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2841_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2842_: u8 = 0;
    let mut v___x_2844_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2845_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2846_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2836_ = l_Lean_Elab_Term_elabTerm(
                    v___x_2826_,
                    v___x_2827_,
                    v___x_2828_,
                    v___x_2828_,
                    v___y_2829_,
                    v___y_2830_,
                    v___y_2831_,
                    v___y_2832_,
                    v___y_2833_,
                    v___y_2834_,
                );
                if crate::leanh::lean_obj_tag(v___x_2836_) == 0 {
                    v_a_2837_ = crate::leanh::lean_ctor_get(v___x_2836_, 0);
                    crate::leanh::lean_inc(v_a_2837_);
                    crate::leanh::lean_dec_ref_known(v___x_2836_, 1);
                    v___x_2838_ = l_Lean_Meta_abstractMVars(
                        v_a_2837_,
                        v___x_2828_,
                        v___y_2831_,
                        v___y_2832_,
                        v___y_2833_,
                        v___y_2834_,
                    );
                    return v___x_2838_;
                } else {
                    v_a_2839_ = crate::leanh::lean_ctor_get(v___x_2836_, 0);
                    v_isSharedCheck_2846_ = (!crate::leanh::lean_is_exclusive(v___x_2836_)) as u8;
                    if v_isSharedCheck_2846_ == 0 {
                        v___x_2841_ = v___x_2836_;
                        v_isShared_2842_ = v_isSharedCheck_2846_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2839_);
                        crate::leanh::lean_dec(v___x_2836_);
                        v___x_2841_ = crate::leanh::lean_box(0);
                        v_isShared_2842_ = v_isSharedCheck_2846_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_2842_ == 0 {
                    v___x_2844_ = v___x_2841_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2845_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2845_, 0, v_a_2839_);
                    v___x_2844_ = v_reuseFailAlloc_2845_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2844_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_Tactic_Conv_evalPattern___lam__1___boxed(
    mut v___x_2847_: *mut crate::leanh::LeanObject,
    mut v___x_2848_: *mut crate::leanh::LeanObject,
    mut v___x_2849_: *mut crate::leanh::LeanObject,
    mut v___y_2850_: *mut crate::leanh::LeanObject,
    mut v___y_2851_: *mut crate::leanh::LeanObject,
    mut v___y_2852_: *mut crate::leanh::LeanObject,
    mut v___y_2853_: *mut crate::leanh::LeanObject,
    mut v___y_2854_: *mut crate::leanh::LeanObject,
    mut v___y_2855_: *mut crate::leanh::LeanObject,
    mut v___y_2856_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_18448__boxed_2857_: u8 = 0;
    let mut v_res_2858_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_18448__boxed_2857_ = (crate::leanh::lean_unbox(v___x_2849_) as u8);
    v_res_2858_ = l_Lean_Elab_Tactic_Conv_evalPattern___lam__1(
        v___x_2847_,
        v___x_2848_,
        v___x_18448__boxed_2857_,
        v___y_2850_,
        v___y_2851_,
        v___y_2852_,
        v___y_2853_,
        v___y_2854_,
        v___y_2855_,
    );
    crate::leanh::lean_dec(v___y_2855_);
    crate::leanh::lean_dec_ref(v___y_2854_);
    crate::leanh::lean_dec(v___y_2853_);
    crate::leanh::lean_dec_ref(v___y_2852_);
    crate::leanh::lean_dec(v___y_2851_);
    crate::leanh::lean_dec_ref(v___y_2850_);
    return v_res_2858_;
}
pub unsafe fn l_Lean_Elab_Tactic_Conv_evalPattern___lam__2(
    mut v___x_2859_: *mut crate::leanh::LeanObject,
    mut v___f_2860_: *mut crate::leanh::LeanObject,
    mut v___y_2861_: *mut crate::leanh::LeanObject,
    mut v___y_2862_: *mut crate::leanh::LeanObject,
    mut v___y_2863_: *mut crate::leanh::LeanObject,
    mut v___y_2864_: *mut crate::leanh::LeanObject,
    mut v___y_2865_: *mut crate::leanh::LeanObject,
    mut v___y_2866_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_fileName_2868_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fileMap_2869_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_2870_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_currRecDepth_2871_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_maxRecDepth_2872_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_2873_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_currNamespace_2874_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_openDecls_2875_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_initHeartbeats_2876_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_maxHeartbeats_2877_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_quotContext_2878_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_currMacroScope_2879_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_diag_2880_: u8 = 0;
    let mut v_cancelTk_x3f_2881_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_suppressElabErrors_2882_: u8 = 0;
    let mut v_inheritedTraceOptions_2883_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2885_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2886_: u8 = 0;
    let mut v_ref_2887_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2889_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2890_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2891_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2892_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_fileName_2868_ = crate::leanh::lean_ctor_get(v___y_2865_, 0);
                v_fileMap_2869_ = crate::leanh::lean_ctor_get(v___y_2865_, 1);
                v_options_2870_ = crate::leanh::lean_ctor_get(v___y_2865_, 2);
                v_currRecDepth_2871_ = crate::leanh::lean_ctor_get(v___y_2865_, 3);
                v_maxRecDepth_2872_ = crate::leanh::lean_ctor_get(v___y_2865_, 4);
                v_ref_2873_ = crate::leanh::lean_ctor_get(v___y_2865_, 5);
                v_currNamespace_2874_ = crate::leanh::lean_ctor_get(v___y_2865_, 6);
                v_openDecls_2875_ = crate::leanh::lean_ctor_get(v___y_2865_, 7);
                v_initHeartbeats_2876_ = crate::leanh::lean_ctor_get(v___y_2865_, 8);
                v_maxHeartbeats_2877_ = crate::leanh::lean_ctor_get(v___y_2865_, 9);
                v_quotContext_2878_ = crate::leanh::lean_ctor_get(v___y_2865_, 10);
                v_currMacroScope_2879_ = crate::leanh::lean_ctor_get(v___y_2865_, 11);
                v_diag_2880_ = crate::leanh::lean_ctor_get_uint8(
                    v___y_2865_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 14) as u32,
                );
                v_cancelTk_x3f_2881_ = crate::leanh::lean_ctor_get(v___y_2865_, 12);
                v_suppressElabErrors_2882_ = crate::leanh::lean_ctor_get_uint8(
                    v___y_2865_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 14 + 1) as u32,
                );
                v_inheritedTraceOptions_2883_ = crate::leanh::lean_ctor_get(v___y_2865_, 13);
                v_isSharedCheck_2892_ = (!crate::leanh::lean_is_exclusive(v___y_2865_)) as u8;
                if v_isSharedCheck_2892_ == 0 {
                    v___x_2885_ = v___y_2865_;
                    v_isShared_2886_ = v_isSharedCheck_2892_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_inheritedTraceOptions_2883_);
                    crate::leanh::lean_inc(v_cancelTk_x3f_2881_);
                    crate::leanh::lean_inc(v_currMacroScope_2879_);
                    crate::leanh::lean_inc(v_quotContext_2878_);
                    crate::leanh::lean_inc(v_maxHeartbeats_2877_);
                    crate::leanh::lean_inc(v_initHeartbeats_2876_);
                    crate::leanh::lean_inc(v_openDecls_2875_);
                    crate::leanh::lean_inc(v_currNamespace_2874_);
                    crate::leanh::lean_inc(v_ref_2873_);
                    crate::leanh::lean_inc(v_maxRecDepth_2872_);
                    crate::leanh::lean_inc(v_currRecDepth_2871_);
                    crate::leanh::lean_inc(v_options_2870_);
                    crate::leanh::lean_inc(v_fileMap_2869_);
                    crate::leanh::lean_inc(v_fileName_2868_);
                    crate::leanh::lean_dec(v___y_2865_);
                    v___x_2885_ = crate::leanh::lean_box(0);
                    v_isShared_2886_ = v_isSharedCheck_2892_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_ref_2887_ = l_Lean_replaceRef(v___x_2859_, v_ref_2873_);
                crate::leanh::lean_dec(v_ref_2873_);
                if v_isShared_2886_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2885_, 5, v_ref_2887_);
                    v___x_2889_ = v___x_2885_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2891_ = crate::leanh::lean_alloc_ctor(0, 14, (2) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2891_, 0, v_fileName_2868_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2891_, 1, v_fileMap_2869_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2891_, 2, v_options_2870_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2891_, 3, v_currRecDepth_2871_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2891_, 4, v_maxRecDepth_2872_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2891_, 5, v_ref_2887_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2891_, 6, v_currNamespace_2874_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2891_, 7, v_openDecls_2875_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2891_, 8, v_initHeartbeats_2876_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2891_, 9, v_maxHeartbeats_2877_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2891_, 10, v_quotContext_2878_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2891_, 11, v_currMacroScope_2879_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2891_, 12, v_cancelTk_x3f_2881_);
                    crate::leanh::lean_ctor_set(
                        v_reuseFailAlloc_2891_,
                        13,
                        v_inheritedTraceOptions_2883_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_2891_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 14) as u32,
                        v_diag_2880_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_2891_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 14 + 1) as u32,
                        v_suppressElabErrors_2882_,
                    );
                    v___x_2889_ = v_reuseFailAlloc_2891_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_2890_ = l_Lean_Elab_Term_withoutErrToSorryImp___redArg(
                    v___f_2860_,
                    v___y_2861_,
                    v___y_2862_,
                    v___y_2863_,
                    v___y_2864_,
                    v___x_2889_,
                    v___y_2866_,
                );
                crate::leanh::lean_dec_ref(v___x_2889_);
                return v___x_2890_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_Tactic_Conv_evalPattern___lam__2___boxed(
    mut v___x_2893_: *mut crate::leanh::LeanObject,
    mut v___f_2894_: *mut crate::leanh::LeanObject,
    mut v___y_2895_: *mut crate::leanh::LeanObject,
    mut v___y_2896_: *mut crate::leanh::LeanObject,
    mut v___y_2897_: *mut crate::leanh::LeanObject,
    mut v___y_2898_: *mut crate::leanh::LeanObject,
    mut v___y_2899_: *mut crate::leanh::LeanObject,
    mut v___y_2900_: *mut crate::leanh::LeanObject,
    mut v___y_2901_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2902_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2902_ = l_Lean_Elab_Tactic_Conv_evalPattern___lam__2(
        v___x_2893_,
        v___f_2894_,
        v___y_2895_,
        v___y_2896_,
        v___y_2897_,
        v___y_2898_,
        v___y_2899_,
        v___y_2900_,
    );
    crate::leanh::lean_dec(v___y_2900_);
    crate::leanh::lean_dec(v___y_2898_);
    crate::leanh::lean_dec_ref(v___y_2897_);
    crate::leanh::lean_dec(v___y_2896_);
    crate::leanh::lean_dec_ref(v___y_2895_);
    crate::leanh::lean_dec(v___x_2893_);
    return v_res_2902_;
}
pub unsafe fn l_Lean_Elab_Tactic_Conv_evalPattern___lam__3(
    mut v___x_2903_: *mut crate::leanh::LeanObject,
    mut v___x_2904_: u8,
    mut v_e_2905_: *mut crate::leanh::LeanObject,
    mut v___y_2906_: *mut crate::leanh::LeanObject,
    mut v___y_2907_: *mut crate::leanh::LeanObject,
    mut v___y_2908_: *mut crate::leanh::LeanObject,
    mut v___y_2909_: *mut crate::leanh::LeanObject,
    mut v___y_2910_: *mut crate::leanh::LeanObject,
    mut v___y_2911_: *mut crate::leanh::LeanObject,
    mut v___y_2912_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2914_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2915_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2916_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2914_ = crate::leanh::lean_alloc_ctor(0, 2, (1) as u32);
    crate::leanh::lean_ctor_set(v___x_2914_, 0, v_e_2905_);
    crate::leanh::lean_ctor_set(v___x_2914_, 1, v___x_2903_);
    crate::leanh::lean_ctor_set_uint8(
        v___x_2914_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2) as u32,
        v___x_2904_,
    );
    v___x_2915_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2915_, 0, v___x_2914_);
    v___x_2916_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2916_, 0, v___x_2915_);
    return v___x_2916_;
}
pub unsafe fn l_Lean_Elab_Tactic_Conv_evalPattern___lam__3___boxed(
    mut v___x_2917_: *mut crate::leanh::LeanObject,
    mut v___x_2918_: *mut crate::leanh::LeanObject,
    mut v_e_2919_: *mut crate::leanh::LeanObject,
    mut v___y_2920_: *mut crate::leanh::LeanObject,
    mut v___y_2921_: *mut crate::leanh::LeanObject,
    mut v___y_2922_: *mut crate::leanh::LeanObject,
    mut v___y_2923_: *mut crate::leanh::LeanObject,
    mut v___y_2924_: *mut crate::leanh::LeanObject,
    mut v___y_2925_: *mut crate::leanh::LeanObject,
    mut v___y_2926_: *mut crate::leanh::LeanObject,
    mut v___y_2927_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_18542__boxed_2928_: u8 = 0;
    let mut v_res_2929_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_18542__boxed_2928_ = (crate::leanh::lean_unbox(v___x_2918_) as u8);
    v_res_2929_ = l_Lean_Elab_Tactic_Conv_evalPattern___lam__3(
        v___x_2917_,
        v___x_18542__boxed_2928_,
        v_e_2919_,
        v___y_2920_,
        v___y_2921_,
        v___y_2922_,
        v___y_2923_,
        v___y_2924_,
        v___y_2925_,
        v___y_2926_,
    );
    crate::leanh::lean_dec(v___y_2926_);
    crate::leanh::lean_dec_ref(v___y_2925_);
    crate::leanh::lean_dec(v___y_2924_);
    crate::leanh::lean_dec_ref(v___y_2923_);
    crate::leanh::lean_dec(v___y_2922_);
    crate::leanh::lean_dec_ref(v___y_2921_);
    crate::leanh::lean_dec(v___y_2920_);
    return v_res_2929_;
}
pub unsafe fn l_Lean_Elab_Tactic_Conv_evalPattern___lam__4(
    mut v___x_2930_: *mut crate::leanh::LeanObject,
    mut v_x_2931_: *mut crate::leanh::LeanObject,
    mut v___y_2932_: *mut crate::leanh::LeanObject,
    mut v___y_2933_: *mut crate::leanh::LeanObject,
    mut v___y_2934_: *mut crate::leanh::LeanObject,
    mut v___y_2935_: *mut crate::leanh::LeanObject,
    mut v___y_2936_: *mut crate::leanh::LeanObject,
    mut v___y_2937_: *mut crate::leanh::LeanObject,
    mut v___y_2938_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2940_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2941_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2940_ = crate::leanh::lean_alloc_ctor(2, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2940_, 0, v___x_2930_);
    v___x_2941_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2941_, 0, v___x_2940_);
    return v___x_2941_;
}
pub unsafe fn l_Lean_Elab_Tactic_Conv_evalPattern___lam__4___boxed(
    mut v___x_2942_: *mut crate::leanh::LeanObject,
    mut v_x_2943_: *mut crate::leanh::LeanObject,
    mut v___y_2944_: *mut crate::leanh::LeanObject,
    mut v___y_2945_: *mut crate::leanh::LeanObject,
    mut v___y_2946_: *mut crate::leanh::LeanObject,
    mut v___y_2947_: *mut crate::leanh::LeanObject,
    mut v___y_2948_: *mut crate::leanh::LeanObject,
    mut v___y_2949_: *mut crate::leanh::LeanObject,
    mut v___y_2950_: *mut crate::leanh::LeanObject,
    mut v___y_2951_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2952_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2952_ = l_Lean_Elab_Tactic_Conv_evalPattern___lam__4(
        v___x_2942_,
        v_x_2943_,
        v___y_2944_,
        v___y_2945_,
        v___y_2946_,
        v___y_2947_,
        v___y_2948_,
        v___y_2949_,
        v___y_2950_,
    );
    crate::leanh::lean_dec(v___y_2950_);
    crate::leanh::lean_dec_ref(v___y_2949_);
    crate::leanh::lean_dec(v___y_2948_);
    crate::leanh::lean_dec_ref(v___y_2947_);
    crate::leanh::lean_dec(v___y_2946_);
    crate::leanh::lean_dec_ref(v___y_2945_);
    crate::leanh::lean_dec(v___y_2944_);
    crate::leanh::lean_dec_ref(v_x_2943_);
    return v_res_2952_;
}
pub unsafe fn l_Lean_Elab_Tactic_Conv_evalPattern___lam__5(
    mut v___x_2953_: *mut crate::leanh::LeanObject,
    mut v_x_2954_: *mut crate::leanh::LeanObject,
    mut v___y_2955_: *mut crate::leanh::LeanObject,
    mut v___y_2956_: *mut crate::leanh::LeanObject,
    mut v___y_2957_: *mut crate::leanh::LeanObject,
    mut v___y_2958_: *mut crate::leanh::LeanObject,
    mut v___y_2959_: *mut crate::leanh::LeanObject,
    mut v___y_2960_: *mut crate::leanh::LeanObject,
    mut v___y_2961_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2963_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2963_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2963_, 0, v___x_2953_);
    return v___x_2963_;
}
pub unsafe fn l_Lean_Elab_Tactic_Conv_evalPattern___lam__5___boxed(
    mut v___x_2964_: *mut crate::leanh::LeanObject,
    mut v_x_2965_: *mut crate::leanh::LeanObject,
    mut v___y_2966_: *mut crate::leanh::LeanObject,
    mut v___y_2967_: *mut crate::leanh::LeanObject,
    mut v___y_2968_: *mut crate::leanh::LeanObject,
    mut v___y_2969_: *mut crate::leanh::LeanObject,
    mut v___y_2970_: *mut crate::leanh::LeanObject,
    mut v___y_2971_: *mut crate::leanh::LeanObject,
    mut v___y_2972_: *mut crate::leanh::LeanObject,
    mut v___y_2973_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2974_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2974_ = l_Lean_Elab_Tactic_Conv_evalPattern___lam__5(
        v___x_2964_,
        v_x_2965_,
        v___y_2966_,
        v___y_2967_,
        v___y_2968_,
        v___y_2969_,
        v___y_2970_,
        v___y_2971_,
        v___y_2972_,
    );
    crate::leanh::lean_dec(v___y_2972_);
    crate::leanh::lean_dec_ref(v___y_2971_);
    crate::leanh::lean_dec(v___y_2970_);
    crate::leanh::lean_dec_ref(v___y_2969_);
    crate::leanh::lean_dec(v___y_2968_);
    crate::leanh::lean_dec_ref(v___y_2967_);
    crate::leanh::lean_dec(v___y_2966_);
    crate::leanh::lean_dec_ref(v_x_2965_);
    return v_res_2974_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__5(
    mut v_sz_2975_: usize,
    mut v_i_2976_: usize,
    mut v_bs_2977_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2978_: u8 = 0;
    let mut v_v_2979_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2980_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2981_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_2982_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2983_: usize = 0;
    let mut v___x_2984_: usize = 0;
    let mut v___x_2985_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2978_ = lean_usize_dec_lt(v_i_2976_, v_sz_2975_);
                if v___x_2978_ == 0 {
                    return v_bs_2977_;
                } else {
                    v_v_2979_ = lean_array_uget_borrowed(v_bs_2977_, v_i_2976_);
                    v_snd_2980_ = crate::leanh::lean_ctor_get(v_v_2979_, 1);
                    crate::leanh::lean_inc(v_snd_2980_);
                    v___x_2981_ = crate::leanh::lean_unsigned_to_nat(0);
                    v_bs_x27_2982_ = lean_array_uset(v_bs_2977_, v_i_2976_, v___x_2981_);
                    v___x_2983_ = 1usize;
                    v___x_2984_ = lean_usize_add(v_i_2976_, v___x_2983_);
                    v___x_2985_ = lean_array_uset(v_bs_x27_2982_, v_i_2976_, v_snd_2980_);
                    v_i_2976_ = v___x_2984_;
                    v_bs_2977_ = v___x_2985_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__5___boxed(
    mut v_sz_2987_: *mut crate::leanh::LeanObject,
    mut v_i_2988_: *mut crate::leanh::LeanObject,
    mut v_bs_2989_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_boxed_2990_: usize = 0;
    let mut v_i_boxed_2991_: usize = 0;
    let mut v_res_2992_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_2990_ = crate::leanh::lean_unbox_usize(v_sz_2987_);
    crate::leanh::lean_dec(v_sz_2987_);
    v_i_boxed_2991_ = crate::leanh::lean_unbox_usize(v_i_2988_);
    crate::leanh::lean_dec(v_i_2988_);
    v_res_2992_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__5(v_sz_boxed_2990_, v_i_boxed_2991_, v_bs_2989_);
    return v_res_2992_;
}
pub unsafe fn l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__6_spec__8___redArg(
    mut v_hi_2993_: *mut crate::leanh::LeanObject,
    mut v_pivot_2994_: *mut crate::leanh::LeanObject,
    mut v_as_2995_: *mut crate::leanh::LeanObject,
    mut v_i_2996_: *mut crate::leanh::LeanObject,
    mut v_k_2997_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2998_: u8 = 0;
    let mut v___x_2999_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3000_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3001_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_3002_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_3003_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3004_: u8 = 0;
    let mut v___x_3005_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3006_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3008_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3009_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3010_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3011_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2998_ = lean_nat_dec_lt(v_k_2997_, v_hi_2993_);
                if v___x_2998_ == 0 {
                    crate::leanh::lean_dec(v_k_2997_);
                    v___x_2999_ = lean_array_fswap(v_as_2995_, v_i_2996_, v_hi_2993_);
                    v___x_3000_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3000_, 0, v_i_2996_);
                    crate::leanh::lean_ctor_set(v___x_3000_, 1, v___x_2999_);
                    return v___x_3000_;
                } else {
                    v___x_3001_ = lean_array_fget_borrowed(v_as_2995_, v_k_2997_);
                    v_fst_3002_ = crate::leanh::lean_ctor_get(v___x_3001_, 0);
                    v_fst_3003_ = crate::leanh::lean_ctor_get(v_pivot_2994_, 0);
                    v___x_3004_ = lean_nat_dec_lt(v_fst_3002_, v_fst_3003_);
                    if v___x_3004_ == 0 {
                        v___x_3005_ = crate::leanh::lean_unsigned_to_nat(1);
                        v___x_3006_ = lean_nat_add(v_k_2997_, v___x_3005_);
                        crate::leanh::lean_dec(v_k_2997_);
                        v_k_2997_ = v___x_3006_;
                        state = 0;
                        continue;
                    } else {
                        v___x_3008_ = lean_array_fswap(v_as_2995_, v_i_2996_, v_k_2997_);
                        v___x_3009_ = crate::leanh::lean_unsigned_to_nat(1);
                        v___x_3010_ = lean_nat_add(v_i_2996_, v___x_3009_);
                        crate::leanh::lean_dec(v_i_2996_);
                        v___x_3011_ = lean_nat_add(v_k_2997_, v___x_3009_);
                        crate::leanh::lean_dec(v_k_2997_);
                        v_as_2995_ = v___x_3008_;
                        v_i_2996_ = v___x_3010_;
                        v_k_2997_ = v___x_3011_;
                        state = 0;
                        continue;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__6_spec__8___redArg___boxed(
    mut v_hi_3013_: *mut crate::leanh::LeanObject,
    mut v_pivot_3014_: *mut crate::leanh::LeanObject,
    mut v_as_3015_: *mut crate::leanh::LeanObject,
    mut v_i_3016_: *mut crate::leanh::LeanObject,
    mut v_k_3017_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3018_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3018_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__6_spec__8___redArg(v_hi_3013_, v_pivot_3014_, v_as_3015_, v_i_3016_, v_k_3017_);
    crate::leanh::lean_dec_ref(v_pivot_3014_);
    crate::leanh::lean_dec(v_hi_3013_);
    return v_res_3018_;
}
pub unsafe fn l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__6___redArg___lam__0(
    mut v_x1_3019_: *mut crate::leanh::LeanObject,
    mut v_x2_3020_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v_fst_3021_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_3022_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3023_: u8 = 0;
    v_fst_3021_ = crate::leanh::lean_ctor_get(v_x1_3019_, 0);
    v_fst_3022_ = crate::leanh::lean_ctor_get(v_x2_3020_, 0);
    v___x_3023_ = lean_nat_dec_lt(v_fst_3021_, v_fst_3022_);
    return v___x_3023_;
}
pub unsafe fn l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__6___redArg___lam__0___boxed(
    mut v_x1_3024_: *mut crate::leanh::LeanObject,
    mut v_x2_3025_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3026_: u8 = 0;
    let mut v_r_3027_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3026_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__6___redArg___lam__0(v_x1_3024_, v_x2_3025_);
    crate::leanh::lean_dec_ref(v_x2_3025_);
    crate::leanh::lean_dec_ref(v_x1_3024_);
    v_r_3027_ = crate::leanh::lean_box((v_res_3026_) as usize);
    return v_r_3027_;
}
pub unsafe fn l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__6___redArg(
    mut v_n_3028_: *mut crate::leanh::LeanObject,
    mut v_as_3029_: *mut crate::leanh::LeanObject,
    mut v_lo_3030_: *mut crate::leanh::LeanObject,
    mut v_hi_3031_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_3033_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_pivot_3034_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3035_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_3036_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3037_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3038_: u8 = 0;
    let mut v___x_3039_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3040_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3041_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3043_: u8 = 0;
    let mut v___x_3044_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3045_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mid_3046_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3048_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3049_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3050_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3051_: u8 = 0;
    let mut v___x_3052_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3054_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3055_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3056_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3057_: u8 = 0;
    let mut v___x_3058_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3059_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3060_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3061_: u8 = 0;
    let mut v___x_3062_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3043_ = lean_nat_dec_lt(v_lo_3030_, v_hi_3031_);
                if v___x_3043_ == 0 {
                    crate::leanh::lean_dec(v_lo_3030_);
                    return v_as_3029_;
                } else {
                    v___x_3044_ = lean_nat_add(v_lo_3030_, v_hi_3031_);
                    v___x_3045_ = crate::leanh::lean_unsigned_to_nat(1);
                    v_mid_3046_ = lean_nat_shiftr(v___x_3044_, v___x_3045_);
                    crate::leanh::lean_dec(v___x_3044_);
                    v___x_3059_ = lean_array_fget_borrowed(v_as_3029_, v_mid_3046_);
                    v___x_3060_ = lean_array_fget_borrowed(v_as_3029_, v_lo_3030_);
                    v___x_3061_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__6___redArg___lam__0(v___x_3059_, v___x_3060_);
                    if v___x_3061_ == 0 {
                        v___y_3054_ = v_as_3029_;
                        state = 3;
                        continue;
                    } else {
                        v___x_3062_ = lean_array_fswap(v_as_3029_, v_lo_3030_, v_mid_3046_);
                        v___y_3054_ = v___x_3062_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v_pivot_3034_ = lean_array_fget(v___y_3033_, v_hi_3031_);
                crate::leanh::lean_inc_n(v_lo_3030_, 2);
                v___x_3035_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__6_spec__8___redArg(v_hi_3031_, v_pivot_3034_, v___y_3033_, v_lo_3030_, v_lo_3030_);
                crate::leanh::lean_dec(v_pivot_3034_);
                v_fst_3036_ = crate::leanh::lean_ctor_get(v___x_3035_, 0);
                crate::leanh::lean_inc(v_fst_3036_);
                v_snd_3037_ = crate::leanh::lean_ctor_get(v___x_3035_, 1);
                crate::leanh::lean_inc(v_snd_3037_);
                crate::leanh::lean_dec_ref(v___x_3035_);
                v___x_3038_ = lean_nat_dec_le(v_hi_3031_, v_fst_3036_);
                if v___x_3038_ == 0 {
                    v___x_3039_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__6___redArg(v_n_3028_, v_snd_3037_, v_lo_3030_, v_fst_3036_);
                    v___x_3040_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_3041_ = lean_nat_add(v_fst_3036_, v___x_3040_);
                    crate::leanh::lean_dec(v_fst_3036_);
                    v_as_3029_ = v___x_3039_;
                    v_lo_3030_ = v___x_3041_;
                    state = 0;
                    continue;
                } else {
                    crate::leanh::lean_dec(v_fst_3036_);
                    crate::leanh::lean_dec(v_lo_3030_);
                    return v_snd_3037_;
                }
            }
            2 => {
                v___x_3049_ = lean_array_fget_borrowed(v___y_3048_, v_mid_3046_);
                v___x_3050_ = lean_array_fget_borrowed(v___y_3048_, v_hi_3031_);
                v___x_3051_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__6___redArg___lam__0(v___x_3049_, v___x_3050_);
                if v___x_3051_ == 0 {
                    crate::leanh::lean_dec(v_mid_3046_);
                    v___y_3033_ = v___y_3048_;
                    state = 1;
                    continue;
                } else {
                    v___x_3052_ = lean_array_fswap(v___y_3048_, v_mid_3046_, v_hi_3031_);
                    crate::leanh::lean_dec(v_mid_3046_);
                    v___y_3033_ = v___x_3052_;
                    state = 1;
                    continue;
                }
            }
            3 => {
                v___x_3055_ = lean_array_fget_borrowed(v___y_3054_, v_hi_3031_);
                v___x_3056_ = lean_array_fget_borrowed(v___y_3054_, v_lo_3030_);
                v___x_3057_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__6___redArg___lam__0(v___x_3055_, v___x_3056_);
                if v___x_3057_ == 0 {
                    v___y_3048_ = v___y_3054_;
                    state = 2;
                    continue;
                } else {
                    v___x_3058_ = lean_array_fswap(v___y_3054_, v_lo_3030_, v_hi_3031_);
                    v___y_3048_ = v___x_3058_;
                    state = 2;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__6___redArg___boxed(
    mut v_n_3063_: *mut crate::leanh::LeanObject,
    mut v_as_3064_: *mut crate::leanh::LeanObject,
    mut v_lo_3065_: *mut crate::leanh::LeanObject,
    mut v_hi_3066_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3067_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3067_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__6___redArg(v_n_3063_, v_as_3064_, v_lo_3065_, v_hi_3066_);
    crate::leanh::lean_dec(v_hi_3066_);
    crate::leanh::lean_dec(v_n_3063_);
    return v_res_3067_;
}
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__4_spec__5(
    mut v_msgData_3068_: *mut crate::leanh::LeanObject,
    mut v___y_3069_: *mut crate::leanh::LeanObject,
    mut v___y_3070_: *mut crate::leanh::LeanObject,
    mut v___y_3071_: *mut crate::leanh::LeanObject,
    mut v___y_3072_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3074_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_3075_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3076_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_3077_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_lctx_3078_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_3079_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3080_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3081_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3082_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3074_ = lean_st_ref_get(v___y_3072_);
    v_env_3075_ = crate::leanh::lean_ctor_get(v___x_3074_, 0);
    crate::leanh::lean_inc_ref(v_env_3075_);
    crate::leanh::lean_dec(v___x_3074_);
    v___x_3076_ = lean_st_ref_get(v___y_3070_);
    v_mctx_3077_ = crate::leanh::lean_ctor_get(v___x_3076_, 0);
    crate::leanh::lean_inc_ref(v_mctx_3077_);
    crate::leanh::lean_dec(v___x_3076_);
    v_lctx_3078_ = crate::leanh::lean_ctor_get(v___y_3069_, 2);
    v_options_3079_ = crate::leanh::lean_ctor_get(v___y_3071_, 2);
    crate::leanh::lean_inc_ref(v_options_3079_);
    crate::leanh::lean_inc_ref(v_lctx_3078_);
    v___x_3080_ = crate::leanh::lean_alloc_ctor(0, 4, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3080_, 0, v_env_3075_);
    crate::leanh::lean_ctor_set(v___x_3080_, 1, v_mctx_3077_);
    crate::leanh::lean_ctor_set(v___x_3080_, 2, v_lctx_3078_);
    crate::leanh::lean_ctor_set(v___x_3080_, 3, v_options_3079_);
    v___x_3081_ = crate::leanh::lean_alloc_ctor(3, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3081_, 0, v___x_3080_);
    crate::leanh::lean_ctor_set(v___x_3081_, 1, v_msgData_3068_);
    v___x_3082_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3082_, 0, v___x_3081_);
    return v___x_3082_;
}
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__4_spec__5___boxed(
    mut v_msgData_3083_: *mut crate::leanh::LeanObject,
    mut v___y_3084_: *mut crate::leanh::LeanObject,
    mut v___y_3085_: *mut crate::leanh::LeanObject,
    mut v___y_3086_: *mut crate::leanh::LeanObject,
    mut v___y_3087_: *mut crate::leanh::LeanObject,
    mut v___y_3088_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3089_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3089_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__4_spec__5(v_msgData_3083_, v___y_3084_, v___y_3085_, v___y_3086_, v___y_3087_);
    crate::leanh::lean_dec(v___y_3087_);
    crate::leanh::lean_dec_ref(v___y_3086_);
    crate::leanh::lean_dec(v___y_3085_);
    crate::leanh::lean_dec_ref(v___y_3084_);
    return v_res_3089_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__4___redArg(
    mut v_msg_3090_: *mut crate::leanh::LeanObject,
    mut v___y_3091_: *mut crate::leanh::LeanObject,
    mut v___y_3092_: *mut crate::leanh::LeanObject,
    mut v___y_3093_: *mut crate::leanh::LeanObject,
    mut v___y_3094_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_ref_3096_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3097_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3098_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3100_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3101_: u8 = 0;
    let mut v___x_3102_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3104_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3105_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3106_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ref_3096_ = crate::leanh::lean_ctor_get(v___y_3093_, 5);
                v___x_3097_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__4_spec__5(v_msg_3090_, v___y_3091_, v___y_3092_, v___y_3093_, v___y_3094_);
                v_a_3098_ = crate::leanh::lean_ctor_get(v___x_3097_, 0);
                v_isSharedCheck_3106_ = (!crate::leanh::lean_is_exclusive(v___x_3097_)) as u8;
                if v_isSharedCheck_3106_ == 0 {
                    v___x_3100_ = v___x_3097_;
                    v_isShared_3101_ = v_isSharedCheck_3106_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_a_3098_);
                    crate::leanh::lean_dec(v___x_3097_);
                    v___x_3100_ = crate::leanh::lean_box(0);
                    v_isShared_3101_ = v_isSharedCheck_3106_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                crate::leanh::lean_inc(v_ref_3096_);
                v___x_3102_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3102_, 0, v_ref_3096_);
                crate::leanh::lean_ctor_set(v___x_3102_, 1, v_a_3098_);
                if v_isShared_3101_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_3100_, 1);
                    crate::leanh::lean_ctor_set(v___x_3100_, 0, v___x_3102_);
                    v___x_3104_ = v___x_3100_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3105_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3105_, 0, v___x_3102_);
                    v___x_3104_ = v_reuseFailAlloc_3105_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3104_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_throwError___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__4___redArg___boxed(
    mut v_msg_3107_: *mut crate::leanh::LeanObject,
    mut v___y_3108_: *mut crate::leanh::LeanObject,
    mut v___y_3109_: *mut crate::leanh::LeanObject,
    mut v___y_3110_: *mut crate::leanh::LeanObject,
    mut v___y_3111_: *mut crate::leanh::LeanObject,
    mut v___y_3112_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3113_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3113_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__4___redArg(
        v_msg_3107_,
        v___y_3108_,
        v___y_3109_,
        v___y_3110_,
        v___y_3111_,
    );
    crate::leanh::lean_dec(v___y_3111_);
    crate::leanh::lean_dec_ref(v___y_3110_);
    crate::leanh::lean_dec(v___y_3109_);
    crate::leanh::lean_dec_ref(v___y_3108_);
    return v_res_3113_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__3_spec__3_spec__4_spec__12_spec__16___redArg(
    mut v_x_3114_: *mut crate::leanh::LeanObject,
    mut v_x_3115_: *mut crate::leanh::LeanObject,
    mut v_x_3116_: *mut crate::leanh::LeanObject,
    mut v_x_3117_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_ks_3118_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_vs_3119_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3121_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3122_: u8 = 0;
    let mut v___x_3123_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3124_: u8 = 0;
    let mut v___x_3125_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3126_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3128_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3129_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_x27_3130_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3131_: u8 = 0;
    let mut v___x_3133_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3134_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3135_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3137_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3138_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3139_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3141_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3142_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3143_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ks_3118_ = crate::leanh::lean_ctor_get(v_x_3114_, 0);
                v_vs_3119_ = crate::leanh::lean_ctor_get(v_x_3114_, 1);
                v_isSharedCheck_3143_ = (!crate::leanh::lean_is_exclusive(v_x_3114_)) as u8;
                if v_isSharedCheck_3143_ == 0 {
                    v___x_3121_ = v_x_3114_;
                    v_isShared_3122_ = v_isSharedCheck_3143_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_vs_3119_);
                    crate::leanh::lean_inc(v_ks_3118_);
                    crate::leanh::lean_dec(v_x_3114_);
                    v___x_3121_ = crate::leanh::lean_box(0);
                    v_isShared_3122_ = v_isSharedCheck_3143_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_3123_ = lean_array_get_size(v_ks_3118_);
                v___x_3124_ = lean_nat_dec_lt(v_x_3115_, v___x_3123_);
                if v___x_3124_ == 0 {
                    crate::leanh::lean_dec(v_x_3115_);
                    v___x_3125_ = lean_array_push(v_ks_3118_, v_x_3116_);
                    v___x_3126_ = lean_array_push(v_vs_3119_, v_x_3117_);
                    if v_isShared_3122_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_3121_, 1, v___x_3126_);
                        crate::leanh::lean_ctor_set(v___x_3121_, 0, v___x_3125_);
                        v___x_3128_ = v___x_3121_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_3129_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3129_, 0, v___x_3125_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3129_, 1, v___x_3126_);
                        v___x_3128_ = v_reuseFailAlloc_3129_;
                        state = 2;
                        continue;
                    }
                } else {
                    v_k_x27_3130_ = lean_array_fget_borrowed(v_ks_3118_, v_x_3115_);
                    v___x_3131_ = l_Lean_instBEqMVarId_beq(v_x_3116_, v_k_x27_3130_);
                    if v___x_3131_ == 0 {
                        if v_isShared_3122_ == 0 {
                            v___x_3133_ = v___x_3121_;
                            state = 3;
                            continue;
                        } else {
                            v_reuseFailAlloc_3137_ =
                                crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_3137_, 0, v_ks_3118_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_3137_, 1, v_vs_3119_);
                            v___x_3133_ = v_reuseFailAlloc_3137_;
                            state = 3;
                            continue;
                        }
                    } else {
                        v___x_3138_ = lean_array_fset(v_ks_3118_, v_x_3115_, v_x_3116_);
                        v___x_3139_ = lean_array_fset(v_vs_3119_, v_x_3115_, v_x_3117_);
                        crate::leanh::lean_dec(v_x_3115_);
                        if v_isShared_3122_ == 0 {
                            crate::leanh::lean_ctor_set(v___x_3121_, 1, v___x_3139_);
                            crate::leanh::lean_ctor_set(v___x_3121_, 0, v___x_3138_);
                            v___x_3141_ = v___x_3121_;
                            state = 4;
                            continue;
                        } else {
                            v_reuseFailAlloc_3142_ =
                                crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_3142_, 0, v___x_3138_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_3142_, 1, v___x_3139_);
                            v___x_3141_ = v_reuseFailAlloc_3142_;
                            state = 4;
                            continue;
                        }
                    }
                }
            }
            2 => {
                return v___x_3128_;
            }
            3 => {
                v___x_3134_ = crate::leanh::lean_unsigned_to_nat(1);
                v___x_3135_ = lean_nat_add(v_x_3115_, v___x_3134_);
                crate::leanh::lean_dec(v_x_3115_);
                v_x_3114_ = v___x_3133_;
                v_x_3115_ = v___x_3135_;
                state = 0;
                continue;
            }
            4 => {
                return v___x_3141_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__3_spec__3_spec__4_spec__12___redArg(
    mut v_n_3144_: *mut crate::leanh::LeanObject,
    mut v_k_3145_: *mut crate::leanh::LeanObject,
    mut v_v_3146_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3147_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3148_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3147_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_3148_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__3_spec__3_spec__4_spec__12_spec__16___redArg(v_n_3144_, v___x_3147_, v_k_3145_, v_v_3146_);
    return v___x_3148_;
}
pub unsafe fn _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__3_spec__3_spec__4___redArg___closed__0()
-> usize {
    let mut v___x_3149_: usize = 0;
    let mut v___x_3150_: usize = 0;
    let mut v___x_3151_: usize = 0;
    v___x_3149_ = 5usize;
    v___x_3150_ = 1usize;
    v___x_3151_ = lean_usize_shift_left(v___x_3150_, v___x_3149_);
    return v___x_3151_;
}
pub unsafe fn _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__3_spec__3_spec__4___redArg___closed__1()
-> usize {
    let mut v___x_3152_: usize = 0;
    let mut v___x_3153_: usize = 0;
    let mut v___x_3154_: usize = 0;
    v___x_3152_ = 1usize;
    v___x_3153_ = crate::leanh::lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__3_spec__3_spec__4___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__3_spec__3_spec__4___redArg___closed__0_once), _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__3_spec__3_spec__4___redArg___closed__0);
    v___x_3154_ = lean_usize_sub(v___x_3153_, v___x_3152_);
    return v___x_3154_;
}
pub unsafe fn _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__3_spec__3_spec__4___redArg___closed__2()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3155_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3155_ = l_Lean_PersistentHashMap_mkEmptyEntries(
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
    );
    return v___x_3155_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__3_spec__3_spec__4___redArg(
    mut v_x_3156_: *mut crate::leanh::LeanObject,
    mut v_x_3157_: usize,
    mut v_x_3158_: usize,
    mut v_x_3159_: *mut crate::leanh::LeanObject,
    mut v_x_3160_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_es_3161_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3162_: usize = 0;
    let mut v___x_3163_: usize = 0;
    let mut v___x_3164_: usize = 0;
    let mut v___x_3165_: usize = 0;
    let mut v_j_3166_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3167_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3168_: u8 = 0;
    let mut v___x_3170_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3171_: u8 = 0;
    let mut v_v_3172_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3173_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_xs_x27_3174_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3176_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3177_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3179_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3180_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_key_3181_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3182_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3184_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3185_: u8 = 0;
    let mut v___x_3186_: u8 = 0;
    let mut v___x_3187_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3188_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3190_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3191_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3192_: u8 = 0;
    let mut v_node_3193_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3195_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3196_: u8 = 0;
    let mut v___x_3197_: usize = 0;
    let mut v___x_3198_: usize = 0;
    let mut v___x_3199_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3201_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3202_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3203_: u8 = 0;
    let mut v___x_3204_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3205_: u8 = 0;
    let mut v_unused_3206_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ks_3207_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_vs_3208_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3210_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3211_: u8 = 0;
    let mut v___x_3213_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_newNode_3214_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3216_: u8 = 0;
    let mut v_ks_3217_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_vs_3218_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3219_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3220_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3221_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3222_: usize = 0;
    let mut v___x_3223_: u8 = 0;
    let mut v___x_3224_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3225_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3226_: u8 = 0;
    let mut v_reuseFailAlloc_3227_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3228_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_3156_) == 0 {
                    v_es_3161_ = crate::leanh::lean_ctor_get(v_x_3156_, 0);
                    v___x_3162_ = 5usize;
                    v___x_3163_ = 1usize;
                    v___x_3164_ = crate::leanh::lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__3_spec__3_spec__4___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__3_spec__3_spec__4___redArg___closed__1_once), _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__3_spec__3_spec__4___redArg___closed__1);
                    v___x_3165_ = lean_usize_land(v_x_3157_, v___x_3164_);
                    v_j_3166_ = lean_usize_to_nat(v___x_3165_);
                    v___x_3167_ = lean_array_get_size(v_es_3161_);
                    v___x_3168_ = lean_nat_dec_lt(v_j_3166_, v___x_3167_);
                    if v___x_3168_ == 0 {
                        crate::leanh::lean_dec(v_j_3166_);
                        crate::leanh::lean_dec(v_x_3160_);
                        crate::leanh::lean_dec(v_x_3159_);
                        return v_x_3156_;
                    } else {
                        crate::leanh::lean_inc_ref(v_es_3161_);
                        v_isSharedCheck_3205_ = (!crate::leanh::lean_is_exclusive(v_x_3156_)) as u8;
                        if v_isSharedCheck_3205_ == 0 {
                            v_unused_3206_ = crate::leanh::lean_ctor_get(v_x_3156_, 0);
                            crate::leanh::lean_dec(v_unused_3206_);
                            v___x_3170_ = v_x_3156_;
                            v_isShared_3171_ = v_isSharedCheck_3205_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_dec(v_x_3156_);
                            v___x_3170_ = crate::leanh::lean_box(0);
                            v_isShared_3171_ = v_isSharedCheck_3205_;
                            state = 1;
                            continue;
                        }
                    }
                } else {
                    v_ks_3207_ = crate::leanh::lean_ctor_get(v_x_3156_, 0);
                    v_vs_3208_ = crate::leanh::lean_ctor_get(v_x_3156_, 1);
                    v_isSharedCheck_3228_ = (!crate::leanh::lean_is_exclusive(v_x_3156_)) as u8;
                    if v_isSharedCheck_3228_ == 0 {
                        v___x_3210_ = v_x_3156_;
                        v_isShared_3211_ = v_isSharedCheck_3228_;
                        state = 8;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_vs_3208_);
                        crate::leanh::lean_inc(v_ks_3207_);
                        crate::leanh::lean_dec(v_x_3156_);
                        v___x_3210_ = crate::leanh::lean_box(0);
                        v_isShared_3211_ = v_isSharedCheck_3228_;
                        state = 8;
                        continue;
                    }
                }
            }
            1 => {
                v_v_3172_ = lean_array_fget(v_es_3161_, v_j_3166_);
                v___x_3173_ = crate::leanh::lean_box(0);
                v_xs_x27_3174_ = lean_array_fset(v_es_3161_, v_j_3166_, v___x_3173_);
                match crate::leanh::lean_obj_tag(v_v_3172_) {
                    0 => {
                        v_key_3181_ = crate::leanh::lean_ctor_get(v_v_3172_, 0);
                        v_val_3182_ = crate::leanh::lean_ctor_get(v_v_3172_, 1);
                        v_isSharedCheck_3192_ = (!crate::leanh::lean_is_exclusive(v_v_3172_)) as u8;
                        if v_isSharedCheck_3192_ == 0 {
                            v___x_3184_ = v_v_3172_;
                            v_isShared_3185_ = v_isSharedCheck_3192_;
                            state = 4;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_val_3182_);
                            crate::leanh::lean_inc(v_key_3181_);
                            crate::leanh::lean_dec(v_v_3172_);
                            v___x_3184_ = crate::leanh::lean_box(0);
                            v_isShared_3185_ = v_isSharedCheck_3192_;
                            state = 4;
                            continue;
                        }
                    }
                    1 => {
                        v_node_3193_ = crate::leanh::lean_ctor_get(v_v_3172_, 0);
                        v_isSharedCheck_3203_ = (!crate::leanh::lean_is_exclusive(v_v_3172_)) as u8;
                        if v_isSharedCheck_3203_ == 0 {
                            v___x_3195_ = v_v_3172_;
                            v_isShared_3196_ = v_isSharedCheck_3203_;
                            state = 6;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_node_3193_);
                            crate::leanh::lean_dec(v_v_3172_);
                            v___x_3195_ = crate::leanh::lean_box(0);
                            v_isShared_3196_ = v_isSharedCheck_3203_;
                            state = 6;
                            continue;
                        }
                    }
                    _ => {
                        v___x_3204_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_3204_, 0, v_x_3159_);
                        crate::leanh::lean_ctor_set(v___x_3204_, 1, v_x_3160_);
                        v___y_3176_ = v___x_3204_;
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                v___x_3177_ = lean_array_fset(v_xs_x27_3174_, v_j_3166_, v___y_3176_);
                crate::leanh::lean_dec(v_j_3166_);
                if v_isShared_3171_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3170_, 0, v___x_3177_);
                    v___x_3179_ = v___x_3170_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_3180_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3180_, 0, v___x_3177_);
                    v___x_3179_ = v_reuseFailAlloc_3180_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_3179_;
            }
            4 => {
                v___x_3186_ = l_Lean_instBEqMVarId_beq(v_x_3159_, v_key_3181_);
                if v___x_3186_ == 0 {
                    crate::leanh::lean_del_object(v___x_3184_);
                    v___x_3187_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(
                        v_key_3181_,
                        v_val_3182_,
                        v_x_3159_,
                        v_x_3160_,
                    );
                    v___x_3188_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3188_, 0, v___x_3187_);
                    v___y_3176_ = v___x_3188_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_dec(v_val_3182_);
                    crate::leanh::lean_dec(v_key_3181_);
                    if v_isShared_3185_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_3184_, 1, v_x_3160_);
                        crate::leanh::lean_ctor_set(v___x_3184_, 0, v_x_3159_);
                        v___x_3190_ = v___x_3184_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_3191_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3191_, 0, v_x_3159_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3191_, 1, v_x_3160_);
                        v___x_3190_ = v_reuseFailAlloc_3191_;
                        state = 5;
                        continue;
                    }
                }
            }
            5 => {
                v___y_3176_ = v___x_3190_;
                state = 2;
                continue;
            }
            6 => {
                v___x_3197_ = lean_usize_shift_right(v_x_3157_, v___x_3162_);
                v___x_3198_ = lean_usize_add(v_x_3158_, v___x_3163_);
                v___x_3199_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__3_spec__3_spec__4___redArg(v_node_3193_, v___x_3197_, v___x_3198_, v_x_3159_, v_x_3160_);
                if v_isShared_3196_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3195_, 0, v___x_3199_);
                    v___x_3201_ = v___x_3195_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_3202_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3202_, 0, v___x_3199_);
                    v___x_3201_ = v_reuseFailAlloc_3202_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                v___y_3176_ = v___x_3201_;
                state = 2;
                continue;
            }
            8 => {
                if v_isShared_3211_ == 0 {
                    v___x_3213_ = v___x_3210_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_3227_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3227_, 0, v_ks_3207_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3227_, 1, v_vs_3208_);
                    v___x_3213_ = v_reuseFailAlloc_3227_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                v_newNode_3214_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__3_spec__3_spec__4_spec__12___redArg(v___x_3213_, v_x_3159_, v_x_3160_);
                v___x_3222_ = 7usize;
                v___x_3223_ = lean_usize_dec_le(v___x_3222_, v_x_3158_);
                if v___x_3223_ == 0 {
                    v___x_3224_ =
                        l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_3214_);
                    v___x_3225_ = crate::leanh::lean_unsigned_to_nat(4);
                    v___x_3226_ = lean_nat_dec_lt(v___x_3224_, v___x_3225_);
                    crate::leanh::lean_dec(v___x_3224_);
                    v___y_3216_ = v___x_3226_;
                    state = 10;
                    continue;
                } else {
                    v___y_3216_ = v___x_3223_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                if v___y_3216_ == 0 {
                    v_ks_3217_ = crate::leanh::lean_ctor_get(v_newNode_3214_, 0);
                    crate::leanh::lean_inc_ref(v_ks_3217_);
                    v_vs_3218_ = crate::leanh::lean_ctor_get(v_newNode_3214_, 1);
                    crate::leanh::lean_inc_ref(v_vs_3218_);
                    crate::leanh::lean_dec_ref(v_newNode_3214_);
                    v___x_3219_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___x_3220_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__3_spec__3_spec__4___redArg___closed__2), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__3_spec__3_spec__4___redArg___closed__2_once), _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__3_spec__3_spec__4___redArg___closed__2);
                    v___x_3221_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__3_spec__3_spec__4_spec__13___redArg(v_x_3158_, v_ks_3217_, v_vs_3218_, v___x_3219_, v___x_3220_);
                    crate::leanh::lean_dec_ref(v_vs_3218_);
                    crate::leanh::lean_dec_ref(v_ks_3217_);
                    return v___x_3221_;
                } else {
                    return v_newNode_3214_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__3_spec__3_spec__4_spec__13___redArg(
    mut v_depth_3229_: usize,
    mut v_keys_3230_: *mut crate::leanh::LeanObject,
    mut v_vals_3231_: *mut crate::leanh::LeanObject,
    mut v_i_3232_: *mut crate::leanh::LeanObject,
    mut v_entries_3233_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3234_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3235_: u8 = 0;
    let mut v_k_3236_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_3237_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3238_: u64 = 0;
    let mut v_h_3239_: usize = 0;
    let mut v___x_3240_: usize = 0;
    let mut v___x_3241_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3242_: usize = 0;
    let mut v___x_3243_: usize = 0;
    let mut v___x_3244_: usize = 0;
    let mut v_h_3245_: usize = 0;
    let mut v___x_3246_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3247_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3234_ = lean_array_get_size(v_keys_3230_);
                v___x_3235_ = lean_nat_dec_lt(v_i_3232_, v___x_3234_);
                if v___x_3235_ == 0 {
                    crate::leanh::lean_dec(v_i_3232_);
                    return v_entries_3233_;
                } else {
                    v_k_3236_ = lean_array_fget_borrowed(v_keys_3230_, v_i_3232_);
                    v_v_3237_ = lean_array_fget_borrowed(v_vals_3231_, v_i_3232_);
                    v___x_3238_ = l_Lean_instHashableMVarId_hash(v_k_3236_);
                    v_h_3239_ = lean_uint64_to_usize(v___x_3238_);
                    v___x_3240_ = 5usize;
                    v___x_3241_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_3242_ = 1usize;
                    v___x_3243_ = lean_usize_sub(v_depth_3229_, v___x_3242_);
                    v___x_3244_ = lean_usize_mul(v___x_3240_, v___x_3243_);
                    v_h_3245_ = lean_usize_shift_right(v_h_3239_, v___x_3244_);
                    v___x_3246_ = lean_nat_add(v_i_3232_, v___x_3241_);
                    crate::leanh::lean_dec(v_i_3232_);
                    crate::leanh::lean_inc(v_v_3237_);
                    crate::leanh::lean_inc(v_k_3236_);
                    v___x_3247_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__3_spec__3_spec__4___redArg(v_entries_3233_, v_h_3245_, v_depth_3229_, v_k_3236_, v_v_3237_);
                    v_i_3232_ = v___x_3246_;
                    v_entries_3233_ = v___x_3247_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__3_spec__3_spec__4_spec__13___redArg___boxed(
    mut v_depth_3249_: *mut crate::leanh::LeanObject,
    mut v_keys_3250_: *mut crate::leanh::LeanObject,
    mut v_vals_3251_: *mut crate::leanh::LeanObject,
    mut v_i_3252_: *mut crate::leanh::LeanObject,
    mut v_entries_3253_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_depth_boxed_3254_: usize = 0;
    let mut v_res_3255_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_depth_boxed_3254_ = crate::leanh::lean_unbox_usize(v_depth_3249_);
    crate::leanh::lean_dec(v_depth_3249_);
    v_res_3255_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__3_spec__3_spec__4_spec__13___redArg(v_depth_boxed_3254_, v_keys_3250_, v_vals_3251_, v_i_3252_, v_entries_3253_);
    crate::leanh::lean_dec_ref(v_vals_3251_);
    crate::leanh::lean_dec_ref(v_keys_3250_);
    return v_res_3255_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__3_spec__3_spec__4___redArg___boxed(
    mut v_x_3256_: *mut crate::leanh::LeanObject,
    mut v_x_3257_: *mut crate::leanh::LeanObject,
    mut v_x_3258_: *mut crate::leanh::LeanObject,
    mut v_x_3259_: *mut crate::leanh::LeanObject,
    mut v_x_3260_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_18897__boxed_3261_: usize = 0;
    let mut v_x_18898__boxed_3262_: usize = 0;
    let mut v_res_3263_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_18897__boxed_3261_ = crate::leanh::lean_unbox_usize(v_x_3257_);
    crate::leanh::lean_dec(v_x_3257_);
    v_x_18898__boxed_3262_ = crate::leanh::lean_unbox_usize(v_x_3258_);
    crate::leanh::lean_dec(v_x_3258_);
    v_res_3263_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__3_spec__3_spec__4___redArg(v_x_3256_, v_x_18897__boxed_3261_, v_x_18898__boxed_3262_, v_x_3259_, v_x_3260_);
    return v_res_3263_;
}
pub unsafe fn l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__3_spec__3___redArg(
    mut v_x_3264_: *mut crate::leanh::LeanObject,
    mut v_x_3265_: *mut crate::leanh::LeanObject,
    mut v_x_3266_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3267_: u64 = 0;
    let mut v___x_3268_: usize = 0;
    let mut v___x_3269_: usize = 0;
    let mut v___x_3270_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3267_ = l_Lean_instHashableMVarId_hash(v_x_3265_);
    v___x_3268_ = lean_uint64_to_usize(v___x_3267_);
    v___x_3269_ = 1usize;
    v___x_3270_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__3_spec__3_spec__4___redArg(v_x_3264_, v___x_3268_, v___x_3269_, v_x_3265_, v_x_3266_);
    return v___x_3270_;
}
pub unsafe fn l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__3___redArg(
    mut v_mvarId_3271_: *mut crate::leanh::LeanObject,
    mut v_val_3272_: *mut crate::leanh::LeanObject,
    mut v___y_3273_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3275_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_3276_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_cache_3277_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_zetaDeltaFVarIds_3278_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_postponed_3279_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_diag_3280_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3282_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3283_: u8 = 0;
    let mut v_depth_3284_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_levelAssignDepth_3285_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_lmvarCounter_3286_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mvarCounter_3287_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_lDecls_3288_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_decls_3289_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_userNames_3290_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_lAssignment_3291_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_eAssignment_3292_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_dAssignment_3293_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3295_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3296_: u8 = 0;
    let mut v___x_3297_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3299_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3301_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3302_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3303_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3304_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3305_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3306_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3307_: u8 = 0;
    let mut v_isSharedCheck_3308_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3275_ = lean_st_ref_take(v___y_3273_);
                v_mctx_3276_ = crate::leanh::lean_ctor_get(v___x_3275_, 0);
                v_cache_3277_ = crate::leanh::lean_ctor_get(v___x_3275_, 1);
                v_zetaDeltaFVarIds_3278_ = crate::leanh::lean_ctor_get(v___x_3275_, 2);
                v_postponed_3279_ = crate::leanh::lean_ctor_get(v___x_3275_, 3);
                v_diag_3280_ = crate::leanh::lean_ctor_get(v___x_3275_, 4);
                v_isSharedCheck_3308_ = (!crate::leanh::lean_is_exclusive(v___x_3275_)) as u8;
                if v_isSharedCheck_3308_ == 0 {
                    v___x_3282_ = v___x_3275_;
                    v_isShared_3283_ = v_isSharedCheck_3308_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_diag_3280_);
                    crate::leanh::lean_inc(v_postponed_3279_);
                    crate::leanh::lean_inc(v_zetaDeltaFVarIds_3278_);
                    crate::leanh::lean_inc(v_cache_3277_);
                    crate::leanh::lean_inc(v_mctx_3276_);
                    crate::leanh::lean_dec(v___x_3275_);
                    v___x_3282_ = crate::leanh::lean_box(0);
                    v_isShared_3283_ = v_isSharedCheck_3308_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_depth_3284_ = crate::leanh::lean_ctor_get(v_mctx_3276_, 0);
                v_levelAssignDepth_3285_ = crate::leanh::lean_ctor_get(v_mctx_3276_, 1);
                v_lmvarCounter_3286_ = crate::leanh::lean_ctor_get(v_mctx_3276_, 2);
                v_mvarCounter_3287_ = crate::leanh::lean_ctor_get(v_mctx_3276_, 3);
                v_lDecls_3288_ = crate::leanh::lean_ctor_get(v_mctx_3276_, 4);
                v_decls_3289_ = crate::leanh::lean_ctor_get(v_mctx_3276_, 5);
                v_userNames_3290_ = crate::leanh::lean_ctor_get(v_mctx_3276_, 6);
                v_lAssignment_3291_ = crate::leanh::lean_ctor_get(v_mctx_3276_, 7);
                v_eAssignment_3292_ = crate::leanh::lean_ctor_get(v_mctx_3276_, 8);
                v_dAssignment_3293_ = crate::leanh::lean_ctor_get(v_mctx_3276_, 9);
                v_isSharedCheck_3307_ = (!crate::leanh::lean_is_exclusive(v_mctx_3276_)) as u8;
                if v_isSharedCheck_3307_ == 0 {
                    v___x_3295_ = v_mctx_3276_;
                    v_isShared_3296_ = v_isSharedCheck_3307_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_dAssignment_3293_);
                    crate::leanh::lean_inc(v_eAssignment_3292_);
                    crate::leanh::lean_inc(v_lAssignment_3291_);
                    crate::leanh::lean_inc(v_userNames_3290_);
                    crate::leanh::lean_inc(v_decls_3289_);
                    crate::leanh::lean_inc(v_lDecls_3288_);
                    crate::leanh::lean_inc(v_mvarCounter_3287_);
                    crate::leanh::lean_inc(v_lmvarCounter_3286_);
                    crate::leanh::lean_inc(v_levelAssignDepth_3285_);
                    crate::leanh::lean_inc(v_depth_3284_);
                    crate::leanh::lean_dec(v_mctx_3276_);
                    v___x_3295_ = crate::leanh::lean_box(0);
                    v_isShared_3296_ = v_isSharedCheck_3307_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_3297_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__3_spec__3___redArg(v_eAssignment_3292_, v_mvarId_3271_, v_val_3272_);
                if v_isShared_3296_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3295_, 8, v___x_3297_);
                    v___x_3299_ = v___x_3295_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_3306_ = crate::leanh::lean_alloc_ctor(0, 10, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3306_, 0, v_depth_3284_);
                    crate::leanh::lean_ctor_set(
                        v_reuseFailAlloc_3306_,
                        1,
                        v_levelAssignDepth_3285_,
                    );
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3306_, 2, v_lmvarCounter_3286_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3306_, 3, v_mvarCounter_3287_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3306_, 4, v_lDecls_3288_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3306_, 5, v_decls_3289_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3306_, 6, v_userNames_3290_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3306_, 7, v_lAssignment_3291_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3306_, 8, v___x_3297_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3306_, 9, v_dAssignment_3293_);
                    v___x_3299_ = v_reuseFailAlloc_3306_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_3283_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3282_, 0, v___x_3299_);
                    v___x_3301_ = v___x_3282_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3305_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3305_, 0, v___x_3299_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3305_, 1, v_cache_3277_);
                    crate::leanh::lean_ctor_set(
                        v_reuseFailAlloc_3305_,
                        2,
                        v_zetaDeltaFVarIds_3278_,
                    );
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3305_, 3, v_postponed_3279_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3305_, 4, v_diag_3280_);
                    v___x_3301_ = v_reuseFailAlloc_3305_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_3302_ = lean_st_ref_set(v___y_3273_, v___x_3301_);
                v___x_3303_ = crate::leanh::lean_box(0);
                v___x_3304_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3304_, 0, v___x_3303_);
                return v___x_3304_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__3___redArg___boxed(
    mut v_mvarId_3309_: *mut crate::leanh::LeanObject,
    mut v_val_3310_: *mut crate::leanh::LeanObject,
    mut v___y_3311_: *mut crate::leanh::LeanObject,
    mut v___y_3312_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3313_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3313_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__3___redArg(
        v_mvarId_3309_,
        v_val_3310_,
        v___y_3311_,
    );
    crate::leanh::lean_dec(v___y_3311_);
    return v_res_3313_;
}
pub unsafe fn l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__9___redArg___lam__0(
    mut v_x1_3314_: *mut crate::leanh::LeanObject,
    mut v_x2_3315_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v_fst_3316_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_3317_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3318_: u8 = 0;
    v_fst_3316_ = crate::leanh::lean_ctor_get(v_x1_3314_, 0);
    v_fst_3317_ = crate::leanh::lean_ctor_get(v_x2_3315_, 0);
    v___x_3318_ = lean_nat_dec_lt(v_fst_3316_, v_fst_3317_);
    return v___x_3318_;
}
pub unsafe fn l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__9___redArg___lam__0___boxed(
    mut v_x1_3319_: *mut crate::leanh::LeanObject,
    mut v_x2_3320_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3321_: u8 = 0;
    let mut v_r_3322_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3321_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__9___redArg___lam__0(v_x1_3319_, v_x2_3320_);
    crate::leanh::lean_dec_ref(v_x2_3320_);
    crate::leanh::lean_dec_ref(v_x1_3319_);
    v_r_3322_ = crate::leanh::lean_box((v_res_3321_) as usize);
    return v_r_3322_;
}
pub unsafe fn l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__9_spec__13___redArg(
    mut v_hi_3323_: *mut crate::leanh::LeanObject,
    mut v_pivot_3324_: *mut crate::leanh::LeanObject,
    mut v_as_3325_: *mut crate::leanh::LeanObject,
    mut v_i_3326_: *mut crate::leanh::LeanObject,
    mut v_k_3327_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3328_: u8 = 0;
    let mut v___x_3329_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3330_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3331_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_3332_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_3333_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3334_: u8 = 0;
    let mut v___x_3335_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3336_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3338_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3339_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3340_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3341_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3328_ = lean_nat_dec_lt(v_k_3327_, v_hi_3323_);
                if v___x_3328_ == 0 {
                    crate::leanh::lean_dec(v_k_3327_);
                    v___x_3329_ = lean_array_fswap(v_as_3325_, v_i_3326_, v_hi_3323_);
                    v___x_3330_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3330_, 0, v_i_3326_);
                    crate::leanh::lean_ctor_set(v___x_3330_, 1, v___x_3329_);
                    return v___x_3330_;
                } else {
                    v___x_3331_ = lean_array_fget_borrowed(v_as_3325_, v_k_3327_);
                    v_fst_3332_ = crate::leanh::lean_ctor_get(v___x_3331_, 0);
                    v_fst_3333_ = crate::leanh::lean_ctor_get(v_pivot_3324_, 0);
                    v___x_3334_ = lean_nat_dec_lt(v_fst_3332_, v_fst_3333_);
                    if v___x_3334_ == 0 {
                        v___x_3335_ = crate::leanh::lean_unsigned_to_nat(1);
                        v___x_3336_ = lean_nat_add(v_k_3327_, v___x_3335_);
                        crate::leanh::lean_dec(v_k_3327_);
                        v_k_3327_ = v___x_3336_;
                        state = 0;
                        continue;
                    } else {
                        v___x_3338_ = lean_array_fswap(v_as_3325_, v_i_3326_, v_k_3327_);
                        v___x_3339_ = crate::leanh::lean_unsigned_to_nat(1);
                        v___x_3340_ = lean_nat_add(v_i_3326_, v___x_3339_);
                        crate::leanh::lean_dec(v_i_3326_);
                        v___x_3341_ = lean_nat_add(v_k_3327_, v___x_3339_);
                        crate::leanh::lean_dec(v_k_3327_);
                        v_as_3325_ = v___x_3338_;
                        v_i_3326_ = v___x_3340_;
                        v_k_3327_ = v___x_3341_;
                        state = 0;
                        continue;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__9_spec__13___redArg___boxed(
    mut v_hi_3343_: *mut crate::leanh::LeanObject,
    mut v_pivot_3344_: *mut crate::leanh::LeanObject,
    mut v_as_3345_: *mut crate::leanh::LeanObject,
    mut v_i_3346_: *mut crate::leanh::LeanObject,
    mut v_k_3347_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3348_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3348_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__9_spec__13___redArg(v_hi_3343_, v_pivot_3344_, v_as_3345_, v_i_3346_, v_k_3347_);
    crate::leanh::lean_dec_ref(v_pivot_3344_);
    crate::leanh::lean_dec(v_hi_3343_);
    return v_res_3348_;
}
pub unsafe fn l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__9___redArg(
    mut v_n_3349_: *mut crate::leanh::LeanObject,
    mut v_as_3350_: *mut crate::leanh::LeanObject,
    mut v_lo_3351_: *mut crate::leanh::LeanObject,
    mut v_hi_3352_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_3354_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_pivot_3355_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3356_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_3357_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3358_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3359_: u8 = 0;
    let mut v___x_3360_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3361_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3362_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3364_: u8 = 0;
    let mut v___x_3365_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3366_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mid_3367_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3369_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3370_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3371_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3372_: u8 = 0;
    let mut v___x_3373_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3375_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3376_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3377_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3378_: u8 = 0;
    let mut v___x_3379_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3380_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3381_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3382_: u8 = 0;
    let mut v___x_3383_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3364_ = lean_nat_dec_lt(v_lo_3351_, v_hi_3352_);
                if v___x_3364_ == 0 {
                    crate::leanh::lean_dec(v_lo_3351_);
                    return v_as_3350_;
                } else {
                    v___x_3365_ = lean_nat_add(v_lo_3351_, v_hi_3352_);
                    v___x_3366_ = crate::leanh::lean_unsigned_to_nat(1);
                    v_mid_3367_ = lean_nat_shiftr(v___x_3365_, v___x_3366_);
                    crate::leanh::lean_dec(v___x_3365_);
                    v___x_3380_ = lean_array_fget_borrowed(v_as_3350_, v_mid_3367_);
                    v___x_3381_ = lean_array_fget_borrowed(v_as_3350_, v_lo_3351_);
                    v___x_3382_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__9___redArg___lam__0(v___x_3380_, v___x_3381_);
                    if v___x_3382_ == 0 {
                        v___y_3375_ = v_as_3350_;
                        state = 3;
                        continue;
                    } else {
                        v___x_3383_ = lean_array_fswap(v_as_3350_, v_lo_3351_, v_mid_3367_);
                        v___y_3375_ = v___x_3383_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v_pivot_3355_ = lean_array_fget(v___y_3354_, v_hi_3352_);
                crate::leanh::lean_inc_n(v_lo_3351_, 2);
                v___x_3356_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__9_spec__13___redArg(v_hi_3352_, v_pivot_3355_, v___y_3354_, v_lo_3351_, v_lo_3351_);
                crate::leanh::lean_dec(v_pivot_3355_);
                v_fst_3357_ = crate::leanh::lean_ctor_get(v___x_3356_, 0);
                crate::leanh::lean_inc(v_fst_3357_);
                v_snd_3358_ = crate::leanh::lean_ctor_get(v___x_3356_, 1);
                crate::leanh::lean_inc(v_snd_3358_);
                crate::leanh::lean_dec_ref(v___x_3356_);
                v___x_3359_ = lean_nat_dec_le(v_hi_3352_, v_fst_3357_);
                if v___x_3359_ == 0 {
                    v___x_3360_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__9___redArg(v_n_3349_, v_snd_3358_, v_lo_3351_, v_fst_3357_);
                    v___x_3361_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_3362_ = lean_nat_add(v_fst_3357_, v___x_3361_);
                    crate::leanh::lean_dec(v_fst_3357_);
                    v_as_3350_ = v___x_3360_;
                    v_lo_3351_ = v___x_3362_;
                    state = 0;
                    continue;
                } else {
                    crate::leanh::lean_dec(v_fst_3357_);
                    crate::leanh::lean_dec(v_lo_3351_);
                    return v_snd_3358_;
                }
            }
            2 => {
                v___x_3370_ = lean_array_fget_borrowed(v___y_3369_, v_mid_3367_);
                v___x_3371_ = lean_array_fget_borrowed(v___y_3369_, v_hi_3352_);
                v___x_3372_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__9___redArg___lam__0(v___x_3370_, v___x_3371_);
                if v___x_3372_ == 0 {
                    crate::leanh::lean_dec(v_mid_3367_);
                    v___y_3354_ = v___y_3369_;
                    state = 1;
                    continue;
                } else {
                    v___x_3373_ = lean_array_fswap(v___y_3369_, v_mid_3367_, v_hi_3352_);
                    crate::leanh::lean_dec(v_mid_3367_);
                    v___y_3354_ = v___x_3373_;
                    state = 1;
                    continue;
                }
            }
            3 => {
                v___x_3376_ = lean_array_fget_borrowed(v___y_3375_, v_hi_3352_);
                v___x_3377_ = lean_array_fget_borrowed(v___y_3375_, v_lo_3351_);
                v___x_3378_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__9___redArg___lam__0(v___x_3376_, v___x_3377_);
                if v___x_3378_ == 0 {
                    v___y_3369_ = v___y_3375_;
                    state = 2;
                    continue;
                } else {
                    v___x_3379_ = lean_array_fswap(v___y_3375_, v_lo_3351_, v_hi_3352_);
                    v___y_3369_ = v___x_3379_;
                    state = 2;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__9___redArg___boxed(
    mut v_n_3384_: *mut crate::leanh::LeanObject,
    mut v_as_3385_: *mut crate::leanh::LeanObject,
    mut v_lo_3386_: *mut crate::leanh::LeanObject,
    mut v_hi_3387_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3388_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3388_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__9___redArg(v_n_3384_, v_as_3385_, v_lo_3386_, v_hi_3387_);
    crate::leanh::lean_dec(v_hi_3387_);
    crate::leanh::lean_dec(v_n_3384_);
    return v_res_3388_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__1___redArg(
    mut v_ref_3389_: *mut crate::leanh::LeanObject,
    mut v_msg_3390_: *mut crate::leanh::LeanObject,
    mut v___y_3391_: *mut crate::leanh::LeanObject,
    mut v___y_3392_: *mut crate::leanh::LeanObject,
    mut v___y_3393_: *mut crate::leanh::LeanObject,
    mut v___y_3394_: *mut crate::leanh::LeanObject,
    mut v___y_3395_: *mut crate::leanh::LeanObject,
    mut v___y_3396_: *mut crate::leanh::LeanObject,
    mut v___y_3397_: *mut crate::leanh::LeanObject,
    mut v___y_3398_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_fileName_3400_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fileMap_3401_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_3402_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_currRecDepth_3403_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_maxRecDepth_3404_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_3405_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_currNamespace_3406_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_openDecls_3407_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_initHeartbeats_3408_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_maxHeartbeats_3409_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_quotContext_3410_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_currMacroScope_3411_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_diag_3412_: u8 = 0;
    let mut v_cancelTk_x3f_3413_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_suppressElabErrors_3414_: u8 = 0;
    let mut v_inheritedTraceOptions_3415_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_3416_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3417_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3418_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_fileName_3400_ = crate::leanh::lean_ctor_get(v___y_3397_, 0);
    v_fileMap_3401_ = crate::leanh::lean_ctor_get(v___y_3397_, 1);
    v_options_3402_ = crate::leanh::lean_ctor_get(v___y_3397_, 2);
    v_currRecDepth_3403_ = crate::leanh::lean_ctor_get(v___y_3397_, 3);
    v_maxRecDepth_3404_ = crate::leanh::lean_ctor_get(v___y_3397_, 4);
    v_ref_3405_ = crate::leanh::lean_ctor_get(v___y_3397_, 5);
    v_currNamespace_3406_ = crate::leanh::lean_ctor_get(v___y_3397_, 6);
    v_openDecls_3407_ = crate::leanh::lean_ctor_get(v___y_3397_, 7);
    v_initHeartbeats_3408_ = crate::leanh::lean_ctor_get(v___y_3397_, 8);
    v_maxHeartbeats_3409_ = crate::leanh::lean_ctor_get(v___y_3397_, 9);
    v_quotContext_3410_ = crate::leanh::lean_ctor_get(v___y_3397_, 10);
    v_currMacroScope_3411_ = crate::leanh::lean_ctor_get(v___y_3397_, 11);
    v_diag_3412_ = crate::leanh::lean_ctor_get_uint8(
        v___y_3397_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 14) as u32,
    );
    v_cancelTk_x3f_3413_ = crate::leanh::lean_ctor_get(v___y_3397_, 12);
    v_suppressElabErrors_3414_ = crate::leanh::lean_ctor_get_uint8(
        v___y_3397_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 14 + 1) as u32,
    );
    v_inheritedTraceOptions_3415_ = crate::leanh::lean_ctor_get(v___y_3397_, 13);
    v_ref_3416_ = l_Lean_replaceRef(v_ref_3389_, v_ref_3405_);
    crate::leanh::lean_inc_ref(v_inheritedTraceOptions_3415_);
    crate::leanh::lean_inc(v_cancelTk_x3f_3413_);
    crate::leanh::lean_inc(v_currMacroScope_3411_);
    crate::leanh::lean_inc(v_quotContext_3410_);
    crate::leanh::lean_inc(v_maxHeartbeats_3409_);
    crate::leanh::lean_inc(v_initHeartbeats_3408_);
    crate::leanh::lean_inc(v_openDecls_3407_);
    crate::leanh::lean_inc(v_currNamespace_3406_);
    crate::leanh::lean_inc(v_maxRecDepth_3404_);
    crate::leanh::lean_inc(v_currRecDepth_3403_);
    crate::leanh::lean_inc_ref(v_options_3402_);
    crate::leanh::lean_inc_ref(v_fileMap_3401_);
    crate::leanh::lean_inc_ref(v_fileName_3400_);
    v___x_3417_ = crate::leanh::lean_alloc_ctor(0, 14, (2) as u32);
    crate::leanh::lean_ctor_set(v___x_3417_, 0, v_fileName_3400_);
    crate::leanh::lean_ctor_set(v___x_3417_, 1, v_fileMap_3401_);
    crate::leanh::lean_ctor_set(v___x_3417_, 2, v_options_3402_);
    crate::leanh::lean_ctor_set(v___x_3417_, 3, v_currRecDepth_3403_);
    crate::leanh::lean_ctor_set(v___x_3417_, 4, v_maxRecDepth_3404_);
    crate::leanh::lean_ctor_set(v___x_3417_, 5, v_ref_3416_);
    crate::leanh::lean_ctor_set(v___x_3417_, 6, v_currNamespace_3406_);
    crate::leanh::lean_ctor_set(v___x_3417_, 7, v_openDecls_3407_);
    crate::leanh::lean_ctor_set(v___x_3417_, 8, v_initHeartbeats_3408_);
    crate::leanh::lean_ctor_set(v___x_3417_, 9, v_maxHeartbeats_3409_);
    crate::leanh::lean_ctor_set(v___x_3417_, 10, v_quotContext_3410_);
    crate::leanh::lean_ctor_set(v___x_3417_, 11, v_currMacroScope_3411_);
    crate::leanh::lean_ctor_set(v___x_3417_, 12, v_cancelTk_x3f_3413_);
    crate::leanh::lean_ctor_set(v___x_3417_, 13, v_inheritedTraceOptions_3415_);
    crate::leanh::lean_ctor_set_uint8(
        v___x_3417_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 14) as u32,
        v_diag_3412_,
    );
    crate::leanh::lean_ctor_set_uint8(
        v___x_3417_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 14 + 1) as u32,
        v_suppressElabErrors_3414_,
    );
    v___x_3418_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__4___redArg(
        v_msg_3390_,
        v___y_3395_,
        v___y_3396_,
        v___x_3417_,
        v___y_3398_,
    );
    crate::leanh::lean_dec_ref_known(v___x_3417_, 14);
    return v___x_3418_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__1___redArg___boxed(
    mut v_ref_3419_: *mut crate::leanh::LeanObject,
    mut v_msg_3420_: *mut crate::leanh::LeanObject,
    mut v___y_3421_: *mut crate::leanh::LeanObject,
    mut v___y_3422_: *mut crate::leanh::LeanObject,
    mut v___y_3423_: *mut crate::leanh::LeanObject,
    mut v___y_3424_: *mut crate::leanh::LeanObject,
    mut v___y_3425_: *mut crate::leanh::LeanObject,
    mut v___y_3426_: *mut crate::leanh::LeanObject,
    mut v___y_3427_: *mut crate::leanh::LeanObject,
    mut v___y_3428_: *mut crate::leanh::LeanObject,
    mut v___y_3429_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3430_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3430_ = l_Lean_throwErrorAt___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__1___redArg(
        v_ref_3419_,
        v_msg_3420_,
        v___y_3421_,
        v___y_3422_,
        v___y_3423_,
        v___y_3424_,
        v___y_3425_,
        v___y_3426_,
        v___y_3427_,
        v___y_3428_,
    );
    crate::leanh::lean_dec(v___y_3428_);
    crate::leanh::lean_dec_ref(v___y_3427_);
    crate::leanh::lean_dec(v___y_3426_);
    crate::leanh::lean_dec_ref(v___y_3425_);
    crate::leanh::lean_dec(v___y_3424_);
    crate::leanh::lean_dec_ref(v___y_3423_);
    crate::leanh::lean_dec(v___y_3422_);
    crate::leanh::lean_dec_ref(v___y_3421_);
    crate::leanh::lean_dec(v_ref_3419_);
    return v_res_3430_;
}
pub unsafe fn _init_l_Array_mapFinIdxM_map___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__7___redArg___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3432_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3433_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3432_ = l_Array_mapFinIdxM_map___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__7___redArg___closed__0;
    v___x_3433_ = l_Lean_stringToMessageData(v___x_3432_);
    return v___x_3433_;
}
pub unsafe fn l_Array_mapFinIdxM_map___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__7___redArg(
    mut v_as_3434_: *mut crate::leanh::LeanObject,
    mut v_i_3435_: *mut crate::leanh::LeanObject,
    mut v_j_3436_: *mut crate::leanh::LeanObject,
    mut v_bs_3437_: *mut crate::leanh::LeanObject,
    mut v___y_3438_: *mut crate::leanh::LeanObject,
    mut v___y_3439_: *mut crate::leanh::LeanObject,
    mut v___y_3440_: *mut crate::leanh::LeanObject,
    mut v___y_3441_: *mut crate::leanh::LeanObject,
    mut v___y_3442_: *mut crate::leanh::LeanObject,
    mut v___y_3443_: *mut crate::leanh::LeanObject,
    mut v___y_3444_: *mut crate::leanh::LeanObject,
    mut v___y_3445_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_zero_3447_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isZero_3448_: u8 = 0;
    let mut v___x_3449_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_one_3450_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_n_3451_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3453_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3454_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3455_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3457_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3458_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isZero_3459_: u8 = 0;
    let mut v___x_3460_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3461_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3462_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3464_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3465_: u8 = 0;
    let mut v___x_3467_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3468_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3469_: u8 = 0;
    let mut v_n_3470_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3471_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_zero_3447_ = crate::leanh::lean_unsigned_to_nat(0);
                v_isZero_3448_ = lean_nat_dec_eq(v_i_3435_, v_zero_3447_);
                if v_isZero_3448_ == 1 {
                    crate::leanh::lean_dec(v_j_3436_);
                    crate::leanh::lean_dec(v_i_3435_);
                    v___x_3449_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3449_, 0, v_bs_3437_);
                    return v___x_3449_;
                } else {
                    v_one_3450_ = crate::leanh::lean_unsigned_to_nat(1);
                    v_n_3451_ = lean_nat_sub(v_i_3435_, v_one_3450_);
                    crate::leanh::lean_dec(v_i_3435_);
                    v___x_3457_ = lean_array_fget_borrowed(v_as_3434_, v_j_3436_);
                    v___x_3458_ = l_Lean_TSyntax_getNat(v___x_3457_);
                    v_isZero_3459_ = lean_nat_dec_eq(v___x_3458_, v_zero_3447_);
                    if v_isZero_3459_ == 1 {
                        crate::leanh::lean_dec(v___x_3458_);
                        crate::leanh::lean_dec(v_n_3451_);
                        crate::leanh::lean_dec_ref(v_bs_3437_);
                        crate::leanh::lean_dec(v_j_3436_);
                        v___x_3460_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Array_mapFinIdxM_map___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__7___redArg___closed__1), core::ptr::addr_of_mut!(l_Array_mapFinIdxM_map___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__7___redArg___closed__1_once), _init_l_Array_mapFinIdxM_map___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__7___redArg___closed__1);
                        v___x_3461_ = l_Lean_throwErrorAt___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__1___redArg(v___x_3457_, v___x_3460_, v___y_3438_, v___y_3439_, v___y_3440_, v___y_3441_, v___y_3442_, v___y_3443_, v___y_3444_, v___y_3445_);
                        v_a_3462_ = crate::leanh::lean_ctor_get(v___x_3461_, 0);
                        v_isSharedCheck_3469_ =
                            (!crate::leanh::lean_is_exclusive(v___x_3461_)) as u8;
                        if v_isSharedCheck_3469_ == 0 {
                            v___x_3464_ = v___x_3461_;
                            v_isShared_3465_ = v_isSharedCheck_3469_;
                            state = 2;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_3462_);
                            crate::leanh::lean_dec(v___x_3461_);
                            v___x_3464_ = crate::leanh::lean_box(0);
                            v_isShared_3465_ = v_isSharedCheck_3469_;
                            state = 2;
                            continue;
                        }
                    } else {
                        v_n_3470_ = lean_nat_sub(v___x_3458_, v_one_3450_);
                        crate::leanh::lean_dec(v___x_3458_);
                        crate::leanh::lean_inc(v_j_3436_);
                        v___x_3471_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_3471_, 0, v_n_3470_);
                        crate::leanh::lean_ctor_set(v___x_3471_, 1, v_j_3436_);
                        v_a_3453_ = v___x_3471_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_3454_ = lean_nat_add(v_j_3436_, v_one_3450_);
                crate::leanh::lean_dec(v_j_3436_);
                v___x_3455_ = lean_array_push(v_bs_3437_, v_a_3453_);
                v_i_3435_ = v_n_3451_;
                v_j_3436_ = v___x_3454_;
                v_bs_3437_ = v___x_3455_;
                state = 0;
                continue;
            }
            2 => {
                if v_isShared_3465_ == 0 {
                    v___x_3467_ = v___x_3464_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_3468_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3468_, 0, v_a_3462_);
                    v___x_3467_ = v_reuseFailAlloc_3468_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_3467_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Array_mapFinIdxM_map___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__7___redArg___boxed(
    mut v_as_3472_: *mut crate::leanh::LeanObject,
    mut v_i_3473_: *mut crate::leanh::LeanObject,
    mut v_j_3474_: *mut crate::leanh::LeanObject,
    mut v_bs_3475_: *mut crate::leanh::LeanObject,
    mut v___y_3476_: *mut crate::leanh::LeanObject,
    mut v___y_3477_: *mut crate::leanh::LeanObject,
    mut v___y_3478_: *mut crate::leanh::LeanObject,
    mut v___y_3479_: *mut crate::leanh::LeanObject,
    mut v___y_3480_: *mut crate::leanh::LeanObject,
    mut v___y_3481_: *mut crate::leanh::LeanObject,
    mut v___y_3482_: *mut crate::leanh::LeanObject,
    mut v___y_3483_: *mut crate::leanh::LeanObject,
    mut v___y_3484_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3485_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3485_ =
        l_Array_mapFinIdxM_map___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__7___redArg(
            v_as_3472_,
            v_i_3473_,
            v_j_3474_,
            v_bs_3475_,
            v___y_3476_,
            v___y_3477_,
            v___y_3478_,
            v___y_3479_,
            v___y_3480_,
            v___y_3481_,
            v___y_3482_,
            v___y_3483_,
        );
    crate::leanh::lean_dec(v___y_3483_);
    crate::leanh::lean_dec_ref(v___y_3482_);
    crate::leanh::lean_dec(v___y_3481_);
    crate::leanh::lean_dec_ref(v___y_3480_);
    crate::leanh::lean_dec(v___y_3479_);
    crate::leanh::lean_dec_ref(v___y_3478_);
    crate::leanh::lean_dec(v___y_3477_);
    crate::leanh::lean_dec_ref(v___y_3476_);
    crate::leanh::lean_dec_ref(v_as_3472_);
    return v_res_3485_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_allDiffAuxAux___at___00__private_Init_Data_Array_Basic_0__Array_allDiffAux___at___00Array_allDiff___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__8_spec__11_spec__13___redArg(
    mut v_as_3486_: *mut crate::leanh::LeanObject,
    mut v_a_3487_: *mut crate::leanh::LeanObject,
    mut v_x_3488_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v_zero_3489_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isZero_3490_: u8 = 0;
    let mut v_fst_3491_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_one_3492_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_n_3493_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3494_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_3495_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3496_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_zero_3489_ = crate::leanh::lean_unsigned_to_nat(0);
                v_isZero_3490_ = lean_nat_dec_eq(v_x_3488_, v_zero_3489_);
                if v_isZero_3490_ == 1 {
                    crate::leanh::lean_dec(v_x_3488_);
                    return v_isZero_3490_;
                } else {
                    v_fst_3491_ = crate::leanh::lean_ctor_get(v_a_3487_, 0);
                    v_one_3492_ = crate::leanh::lean_unsigned_to_nat(1);
                    v_n_3493_ = lean_nat_sub(v_x_3488_, v_one_3492_);
                    crate::leanh::lean_dec(v_x_3488_);
                    v___x_3494_ = lean_array_fget_borrowed(v_as_3486_, v_n_3493_);
                    v_fst_3495_ = crate::leanh::lean_ctor_get(v___x_3494_, 0);
                    v___x_3496_ = lean_nat_dec_eq(v_fst_3491_, v_fst_3495_);
                    if v___x_3496_ == 0 {
                        v_x_3488_ = v_n_3493_;
                        state = 0;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v_n_3493_);
                        return v_isZero_3490_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_allDiffAuxAux___at___00__private_Init_Data_Array_Basic_0__Array_allDiffAux___at___00Array_allDiff___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__8_spec__11_spec__13___redArg___boxed(
    mut v_as_3498_: *mut crate::leanh::LeanObject,
    mut v_a_3499_: *mut crate::leanh::LeanObject,
    mut v_x_3500_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3501_: u8 = 0;
    let mut v_r_3502_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3501_ = l___private_Init_Data_Array_Basic_0__Array_allDiffAuxAux___at___00__private_Init_Data_Array_Basic_0__Array_allDiffAux___at___00Array_allDiff___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__8_spec__11_spec__13___redArg(v_as_3498_, v_a_3499_, v_x_3500_);
    crate::leanh::lean_dec_ref(v_a_3499_);
    crate::leanh::lean_dec_ref(v_as_3498_);
    v_r_3502_ = crate::leanh::lean_box((v_res_3501_) as usize);
    return v_r_3502_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_allDiffAux___at___00Array_allDiff___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__8_spec__11(
    mut v_as_3503_: *mut crate::leanh::LeanObject,
    mut v_i_3504_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_3505_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3506_: u8 = 0;
    let mut v___x_3507_: u8 = 0;
    let mut v___x_3508_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3509_: u8 = 0;
    let mut v___x_3510_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3511_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3505_ = lean_array_get_size(v_as_3503_);
                v___x_3506_ = lean_nat_dec_lt(v_i_3504_, v___x_3505_);
                if v___x_3506_ == 0 {
                    crate::leanh::lean_dec(v_i_3504_);
                    v___x_3507_ = 1;
                    return v___x_3507_;
                } else {
                    v___x_3508_ = lean_array_fget_borrowed(v_as_3503_, v_i_3504_);
                    crate::leanh::lean_inc(v_i_3504_);
                    v___x_3509_ = l___private_Init_Data_Array_Basic_0__Array_allDiffAuxAux___at___00__private_Init_Data_Array_Basic_0__Array_allDiffAux___at___00Array_allDiff___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__8_spec__11_spec__13___redArg(v_as_3503_, v___x_3508_, v_i_3504_);
                    if v___x_3509_ == 0 {
                        crate::leanh::lean_dec(v_i_3504_);
                        return v___x_3509_;
                    } else {
                        v___x_3510_ = crate::leanh::lean_unsigned_to_nat(1);
                        v___x_3511_ = lean_nat_add(v_i_3504_, v___x_3510_);
                        crate::leanh::lean_dec(v_i_3504_);
                        v_i_3504_ = v___x_3511_;
                        state = 0;
                        continue;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_allDiffAux___at___00Array_allDiff___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__8_spec__11___boxed(
    mut v_as_3513_: *mut crate::leanh::LeanObject,
    mut v_i_3514_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3515_: u8 = 0;
    let mut v_r_3516_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3515_ = l___private_Init_Data_Array_Basic_0__Array_allDiffAux___at___00Array_allDiff___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__8_spec__11(v_as_3513_, v_i_3514_);
    crate::leanh::lean_dec_ref(v_as_3513_);
    v_r_3516_ = crate::leanh::lean_box((v_res_3515_) as usize);
    return v_r_3516_;
}
pub unsafe fn l_Array_allDiff___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__8(
    mut v_as_3517_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_3518_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3519_: u8 = 0;
    v___x_3518_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_3519_ = l___private_Init_Data_Array_Basic_0__Array_allDiffAux___at___00Array_allDiff___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__8_spec__11(v_as_3517_, v___x_3518_);
    return v___x_3519_;
}
pub unsafe fn l_Array_allDiff___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__8___boxed(
    mut v_as_3520_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3521_: u8 = 0;
    let mut v_r_3522_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3521_ = l_Array_allDiff___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__8(v_as_3520_);
    crate::leanh::lean_dec_ref(v_as_3520_);
    v_r_3522_ = crate::leanh::lean_box((v_res_3521_) as usize);
    return v_r_3522_;
}
pub unsafe fn _init_l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3523_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3523_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
    );
    return v___x_3523_;
}
pub unsafe fn _init_l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3524_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3525_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3524_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__0),
        core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__0_once),
        _init_l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__0,
    );
    v___x_3525_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3525_, 0, v___x_3524_);
    return v___x_3525_;
}
pub unsafe fn _init_l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__2()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3526_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3527_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3528_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3526_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_3527_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__1),
        core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__1_once),
        _init_l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__1,
    );
    v___x_3528_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3528_, 0, v___x_3527_);
    crate::leanh::lean_ctor_set(v___x_3528_, 1, v___x_3526_);
    return v___x_3528_;
}
pub unsafe fn _init_l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3529_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3530_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3531_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3529_ = crate::leanh::lean_unsigned_to_nat(32);
    v___x_3530_ = lean_mk_empty_array_with_capacity(v___x_3529_);
    v___x_3531_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3531_, 0, v___x_3530_);
    return v___x_3531_;
}
pub unsafe fn _init_l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__4()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3532_: usize = 0;
    let mut v___x_3533_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3534_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3535_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3536_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3537_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3532_ = 5usize;
    v___x_3533_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_3534_ = crate::leanh::lean_unsigned_to_nat(32);
    v___x_3535_ = lean_mk_empty_array_with_capacity(v___x_3534_);
    v___x_3536_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__3),
        core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__3_once),
        _init_l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__3,
    );
    v___x_3537_ = crate::leanh::lean_alloc_ctor(0, 4, (core::mem::size_of::<usize>() * 1) as u32);
    crate::leanh::lean_ctor_set(v___x_3537_, 0, v___x_3536_);
    crate::leanh::lean_ctor_set(v___x_3537_, 1, v___x_3535_);
    crate::leanh::lean_ctor_set(v___x_3537_, 2, v___x_3533_);
    crate::leanh::lean_ctor_set(v___x_3537_, 3, v___x_3533_);
    crate::leanh::lean_ctor_set_usize(v___x_3537_, 4, v___x_3532_);
    return v___x_3537_;
}
pub unsafe fn _init_l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__5()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3538_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3539_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3540_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3538_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__4),
        core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__4_once),
        _init_l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__4,
    );
    v___x_3539_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__1),
        core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__1_once),
        _init_l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__1,
    );
    v___x_3540_ = crate::leanh::lean_alloc_ctor(0, 4, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3540_, 0, v___x_3539_);
    crate::leanh::lean_ctor_set(v___x_3540_, 1, v___x_3539_);
    crate::leanh::lean_ctor_set(v___x_3540_, 2, v___x_3539_);
    crate::leanh::lean_ctor_set(v___x_3540_, 3, v___x_3538_);
    return v___x_3540_;
}
pub unsafe fn _init_l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__6()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3541_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3542_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3543_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3541_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__5),
        core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__5_once),
        _init_l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__5,
    );
    v___x_3542_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__2),
        core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__2_once),
        _init_l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__2,
    );
    v___x_3543_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3543_, 0, v___x_3542_);
    crate::leanh::lean_ctor_set(v___x_3543_, 1, v___x_3541_);
    return v___x_3543_;
}
pub unsafe fn _init_l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__8()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3545_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3546_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3545_ = l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__7;
    v___x_3546_ = l_Lean_stringToMessageData(v___x_3545_);
    return v___x_3546_;
}
pub unsafe fn _init_l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__10()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3548_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3549_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3548_ = l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__9;
    v___x_3549_ = l_Lean_stringToMessageData(v___x_3548_);
    return v___x_3549_;
}
pub unsafe fn _init_l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__12()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3551_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3552_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3551_ = l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__11;
    v___x_3552_ = l_Lean_stringToMessageData(v___x_3551_);
    return v___x_3552_;
}
pub unsafe fn _init_l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__14()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3554_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3555_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3554_ = l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__13;
    v___x_3555_ = l_Lean_stringToMessageData(v___x_3554_);
    return v___x_3555_;
}
pub unsafe fn _init_l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__17()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3559_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3560_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3559_ = l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__16;
    v___x_3560_ = l_Lean_stringToMessageData(v___x_3559_);
    return v___x_3560_;
}
pub unsafe fn l_Lean_Elab_Tactic_Conv_evalPattern___lam__6(
    mut v___x_3581_: u8,
    mut v___f_3582_: *mut crate::leanh::LeanObject,
    mut v___x_3583_: u8,
    mut v_stx_3584_: *mut crate::leanh::LeanObject,
    mut v___x_3585_: *mut crate::leanh::LeanObject,
    mut v___x_3586_: *mut crate::leanh::LeanObject,
    mut v___x_3587_: *mut crate::leanh::LeanObject,
    mut v___x_3588_: *mut crate::leanh::LeanObject,
    mut v___y_3589_: *mut crate::leanh::LeanObject,
    mut v___y_3590_: *mut crate::leanh::LeanObject,
    mut v___y_3591_: *mut crate::leanh::LeanObject,
    mut v___y_3592_: *mut crate::leanh::LeanObject,
    mut v___y_3593_: *mut crate::leanh::LeanObject,
    mut v___y_3594_: *mut crate::leanh::LeanObject,
    mut v___y_3595_: *mut crate::leanh::LeanObject,
    mut v___y_3596_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_3599_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_subgoals_3600_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3601_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3602_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3603_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3604_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3605_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3606_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3607_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3608_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3609_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3610_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_expr_3611_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3612_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3613_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3614_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3615_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3616_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3617_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3618_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3619_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3620_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3621_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3623_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3624_: u8 = 0;
    let mut v___x_3626_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3627_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3628_: u8 = 0;
    let mut v_a_3629_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3631_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3632_: u8 = 0;
    let mut v___x_3634_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3635_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3636_: u8 = 0;
    let mut v_a_3637_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3639_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3640_: u8 = 0;
    let mut v___x_3642_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3643_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3644_: u8 = 0;
    let mut v___y_3646_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3647_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3648_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3649_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3650_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3651_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3652_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3653_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3654_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3655_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_3656_: usize = 0;
    let mut v___x_3657_: usize = 0;
    let mut v___x_3658_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3660_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3661_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3662_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3663_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3664_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3665_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3666_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3667_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3668_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3669_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3670_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3671_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3672_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3673_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3675_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3676_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3677_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3678_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3679_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3680_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3681_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3682_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3683_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3684_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3685_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3686_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3687_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3688_: u8 = 0;
    let mut v___x_3689_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3690_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3691_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3693_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3694_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3695_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3696_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3697_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3698_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3699_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3700_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3701_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3702_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3703_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3704_: u8 = 0;
    let mut v___x_3705_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3706_: u8 = 0;
    let mut v___y_3708_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3709_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3710_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3711_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3712_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3713_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3714_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3715_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3716_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3717_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3718_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3719_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3720_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3721_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3722_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3723_: u8 = 0;
    let mut v___x_3724_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3725_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3726_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3727_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3728_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3729_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_3730_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3732_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3733_: u8 = 0;
    let mut v___x_3734_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_subgoals_3735_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3736_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3737_: u8 = 0;
    let mut v_expr_3738_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3739_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3740_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3742_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3743_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3744_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3746_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3747_: u8 = 0;
    let mut v___x_3749_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3750_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3751_: u8 = 0;
    let mut v_reuseFailAlloc_3752_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_subgoals_3753_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_idx_3754_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_remaining_3755_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3756_: u8 = 0;
    let mut v___x_3757_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3758_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3760_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3761_: u8 = 0;
    let mut v_fst_3762_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3764_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3765_: u8 = 0;
    let mut v___x_3766_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3767_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3769_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3770_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3772_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3773_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3775_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3776_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3777_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3778_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3779_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3780_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3781_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3782_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3783_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3784_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3785_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3786_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3787_: u8 = 0;
    let mut v_unused_3788_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3789_: u8 = 0;
    let mut v_expr_3790_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3791_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3792_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3794_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3795_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3796_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3798_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3799_: u8 = 0;
    let mut v___x_3801_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3802_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3803_: u8 = 0;
    let mut v_reuseFailAlloc_3804_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3805_: u8 = 0;
    let mut v_unused_3806_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3807_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3809_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3810_: u8 = 0;
    let mut v___x_3812_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3813_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3814_: u8 = 0;
    let mut v___y_3816_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3817_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3818_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3819_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3820_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_occs_3821_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3822_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3823_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3824_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3825_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3826_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3827_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3828_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3829_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3830_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3831_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3832_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3833_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3834_: u8 = 0;
    let mut v_a_3835_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3837_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3838_: u8 = 0;
    let mut v___x_3840_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3841_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3842_: u8 = 0;
    let mut v___y_3844_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3845_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3846_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3847_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3848_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3849_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3850_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3851_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3852_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3853_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3854_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3855_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3856_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3857_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3858_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3859_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3860_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3862_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3863_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3864_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3865_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3866_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3867_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3868_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3869_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3870_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3871_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3872_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3873_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3874_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3875_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3876_: u8 = 0;
    let mut v___x_3877_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3878_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3880_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3881_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3882_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3883_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3884_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3885_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3886_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3887_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3888_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3889_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3890_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3891_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3892_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3893_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3894_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3895_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3896_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3897_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3899_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3900_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3901_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3902_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3903_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3904_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3905_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3906_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3907_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3908_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3909_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3910_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3911_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3912_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3913_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3914_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3915_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3916_: u8 = 0;
    let mut v_occs_3918_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3919_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3920_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3921_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3922_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3923_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3924_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3925_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3926_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_declName_x3f_3927_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_macroStack_3928_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mayPostpone_3929_: u8 = 0;
    let mut v_errToSorry_3930_: u8 = 0;
    let mut v_autoBoundImplicitContext_3931_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_autoBoundImplicitForbidden_3932_: *mut crate::leanh::LeanObject =
        core::ptr::null_mut();
    let mut v_sectionVars_3933_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sectionFVars_3934_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_implicitLambda_3935_: u8 = 0;
    let mut v_heedElabAsElim_3936_: u8 = 0;
    let mut v_isNoncomputableSection_3937_: u8 = 0;
    let mut v_isMetaSection_3938_: u8 = 0;
    let mut v_inPattern_3939_: u8 = 0;
    let mut v_tacSnap_x3f_3940_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_saveRecAppSyntax_3941_: u8 = 0;
    let mut v_holesAsSyntheticOpaque_3942_: u8 = 0;
    let mut v_checkDeprecated_3943_: u8 = 0;
    let mut v_fixedTermElabs_3944_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3945_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3946_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3947_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3948_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3949_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3950_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3951_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3952_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3953_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3954_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3955_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3956_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3957_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3958_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3959_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3960_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3961_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3962_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3963_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3964_: u8 = 0;
    let mut v___x_3965_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3966_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3967_: u8 = 0;
    let mut v___x_3968_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3969_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3971_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3972_: u8 = 0;
    let mut v___x_3974_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3975_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3976_: u8 = 0;
    let mut v___x_3977_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3978_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3979_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3980_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3981_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3982_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3983_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3984_: u8 = 0;
    let mut v___x_3985_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3986_: u8 = 0;
    let mut v_a_3987_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3989_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3990_: u8 = 0;
    let mut v___x_3992_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3993_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3994_: u8 = 0;
    let mut v___x_3995_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3996_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3998_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3999_: u8 = 0;
    let mut v___x_4001_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4002_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4003_: u8 = 0;
    let mut v_a_4004_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4006_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4007_: u8 = 0;
    let mut v___x_4009_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4010_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4011_: u8 = 0;
    let mut v___x_4012_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4013_: u8 = 0;
    let mut v___x_4014_: u8 = 0;
    let mut v___x_4015_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4016_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4017_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4018_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4019_: u8 = 0;
    let mut v___x_4020_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4021_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_occs_4022_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4023_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4024_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if v___x_3581_ == 0 {
                    crate::leanh::lean_dec_ref(v___x_3588_);
                    crate::leanh::lean_dec_ref(v___x_3587_);
                    crate::leanh::lean_dec_ref(v___x_3586_);
                    crate::leanh::lean_dec_ref(v___x_3585_);
                    crate::leanh::lean_dec_ref(v___f_3582_);
                    v___x_3689_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__0___redArg();
                    return v___x_3689_;
                } else {
                    v___x_3690_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___x_3691_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_4012_ = l_Lean_Syntax_getArg(v_stx_3584_, v___x_3691_);
                    v___x_4013_ = l_Lean_Syntax_isNone(v___x_4012_);
                    if v___x_4013_ == 0 {
                        crate::leanh::lean_inc(v___x_4012_);
                        v___x_4014_ = l_Lean_Syntax_matchesNull(v___x_4012_, v___x_3691_);
                        if v___x_4014_ == 0 {
                            crate::leanh::lean_dec(v___x_4012_);
                            crate::leanh::lean_dec_ref(v___x_3588_);
                            crate::leanh::lean_dec_ref(v___x_3587_);
                            crate::leanh::lean_dec_ref(v___x_3586_);
                            crate::leanh::lean_dec_ref(v___x_3585_);
                            crate::leanh::lean_dec_ref(v___f_3582_);
                            v___x_4015_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__0___redArg();
                            return v___x_4015_;
                        } else {
                            v___x_4016_ = l_Lean_Syntax_getArg(v___x_4012_, v___x_3690_);
                            crate::leanh::lean_dec(v___x_4012_);
                            v___x_4017_ = l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__27;
                            crate::leanh::lean_inc_ref(v___x_3588_);
                            crate::leanh::lean_inc_ref(v___x_3587_);
                            crate::leanh::lean_inc_ref(v___x_3586_);
                            crate::leanh::lean_inc_ref(v___x_3585_);
                            v___x_4018_ = l_Lean_Name_mkStr5(
                                v___x_3585_,
                                v___x_3586_,
                                v___x_3587_,
                                v___x_3588_,
                                v___x_4017_,
                            );
                            crate::leanh::lean_inc(v___x_4016_);
                            v___x_4019_ = l_Lean_Syntax_isOfKind(v___x_4016_, v___x_4018_);
                            crate::leanh::lean_dec(v___x_4018_);
                            if v___x_4019_ == 0 {
                                crate::leanh::lean_dec(v___x_4016_);
                                crate::leanh::lean_dec_ref(v___x_3588_);
                                crate::leanh::lean_dec_ref(v___x_3587_);
                                crate::leanh::lean_dec_ref(v___x_3586_);
                                crate::leanh::lean_dec_ref(v___x_3585_);
                                crate::leanh::lean_dec_ref(v___f_3582_);
                                v___x_4020_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__0___redArg();
                                return v___x_4020_;
                            } else {
                                v___x_4021_ = crate::leanh::lean_unsigned_to_nat(3);
                                v_occs_4022_ = l_Lean_Syntax_getArg(v___x_4016_, v___x_4021_);
                                crate::leanh::lean_dec(v___x_4016_);
                                v___x_4023_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                                crate::leanh::lean_ctor_set(v___x_4023_, 0, v_occs_4022_);
                                v_occs_3918_ = v___x_4023_;
                                v___y_3919_ = v___y_3589_;
                                v___y_3920_ = v___y_3590_;
                                v___y_3921_ = v___y_3591_;
                                v___y_3922_ = v___y_3592_;
                                v___y_3923_ = v___y_3593_;
                                v___y_3924_ = v___y_3594_;
                                v___y_3925_ = v___y_3595_;
                                v___y_3926_ = v___y_3596_;
                                state = 34;
                                continue;
                            }
                        }
                    } else {
                        crate::leanh::lean_dec(v___x_4012_);
                        v___x_4024_ = crate::leanh::lean_box(0);
                        v_occs_3918_ = v___x_4024_;
                        v___y_3919_ = v___y_3589_;
                        v___y_3920_ = v___y_3590_;
                        v___y_3921_ = v___y_3591_;
                        v___y_3922_ = v___y_3592_;
                        v___y_3923_ = v___y_3593_;
                        v___y_3924_ = v___y_3594_;
                        v___y_3925_ = v___y_3595_;
                        v___y_3926_ = v___y_3596_;
                        state = 34;
                        continue;
                    }
                }
            }
            1 => {
                v___x_3609_ = l_Lean_Elab_Tactic_Conv_getRhs___redArg(
                    v___y_3602_,
                    v___y_3605_,
                    v___y_3606_,
                    v___y_3607_,
                    v___y_3608_,
                );
                if crate::leanh::lean_obj_tag(v___x_3609_) == 0 {
                    v_a_3610_ = crate::leanh::lean_ctor_get(v___x_3609_, 0);
                    crate::leanh::lean_inc(v_a_3610_);
                    crate::leanh::lean_dec_ref_known(v___x_3609_, 1);
                    v_expr_3611_ = crate::leanh::lean_ctor_get(v___y_3599_, 0);
                    v___x_3612_ = l_Lean_Expr_mvarId_x21(v_a_3610_);
                    crate::leanh::lean_dec(v_a_3610_);
                    crate::leanh::lean_inc_ref(v_expr_3611_);
                    v___x_3613_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__3___redArg(v___x_3612_, v_expr_3611_, v___y_3606_);
                    crate::leanh::lean_dec_ref(v___x_3613_);
                    v___x_3614_ = l_Lean_Elab_Tactic_getMainGoal___redArg(
                        v___y_3602_,
                        v___y_3605_,
                        v___y_3606_,
                        v___y_3607_,
                        v___y_3608_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_3614_) == 0 {
                        v_a_3615_ = crate::leanh::lean_ctor_get(v___x_3614_, 0);
                        crate::leanh::lean_inc(v_a_3615_);
                        crate::leanh::lean_dec_ref_known(v___x_3614_, 1);
                        v___x_3616_ = l_Lean_Meta_Simp_Result_getProof(
                            v___y_3599_,
                            v___y_3605_,
                            v___y_3606_,
                            v___y_3607_,
                            v___y_3608_,
                        );
                        if crate::leanh::lean_obj_tag(v___x_3616_) == 0 {
                            v_a_3617_ = crate::leanh::lean_ctor_get(v___x_3616_, 0);
                            crate::leanh::lean_inc(v_a_3617_);
                            crate::leanh::lean_dec_ref_known(v___x_3616_, 1);
                            v___x_3618_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__3___redArg(v_a_3615_, v_a_3617_, v___y_3606_);
                            crate::leanh::lean_dec_ref(v___x_3618_);
                            v___x_3619_ = lean_array_to_list(v_subgoals_3600_);
                            v___x_3620_ = l_Lean_Elab_Tactic_replaceMainGoal___redArg(
                                v___x_3619_,
                                v___y_3602_,
                                v___y_3605_,
                                v___y_3606_,
                                v___y_3607_,
                                v___y_3608_,
                            );
                            return v___x_3620_;
                        } else {
                            crate::leanh::lean_dec(v_a_3615_);
                            crate::leanh::lean_dec_ref(v_subgoals_3600_);
                            v_a_3621_ = crate::leanh::lean_ctor_get(v___x_3616_, 0);
                            v_isSharedCheck_3628_ =
                                (!crate::leanh::lean_is_exclusive(v___x_3616_)) as u8;
                            if v_isSharedCheck_3628_ == 0 {
                                v___x_3623_ = v___x_3616_;
                                v_isShared_3624_ = v_isSharedCheck_3628_;
                                state = 2;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_3621_);
                                crate::leanh::lean_dec(v___x_3616_);
                                v___x_3623_ = crate::leanh::lean_box(0);
                                v_isShared_3624_ = v_isSharedCheck_3628_;
                                state = 2;
                                continue;
                            }
                        }
                    } else {
                        crate::leanh::lean_dec_ref(v_subgoals_3600_);
                        crate::leanh::lean_dec_ref(v___y_3599_);
                        v_a_3629_ = crate::leanh::lean_ctor_get(v___x_3614_, 0);
                        v_isSharedCheck_3636_ =
                            (!crate::leanh::lean_is_exclusive(v___x_3614_)) as u8;
                        if v_isSharedCheck_3636_ == 0 {
                            v___x_3631_ = v___x_3614_;
                            v_isShared_3632_ = v_isSharedCheck_3636_;
                            state = 4;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_3629_);
                            crate::leanh::lean_dec(v___x_3614_);
                            v___x_3631_ = crate::leanh::lean_box(0);
                            v_isShared_3632_ = v_isSharedCheck_3636_;
                            state = 4;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_subgoals_3600_);
                    crate::leanh::lean_dec_ref(v___y_3599_);
                    v_a_3637_ = crate::leanh::lean_ctor_get(v___x_3609_, 0);
                    v_isSharedCheck_3644_ = (!crate::leanh::lean_is_exclusive(v___x_3609_)) as u8;
                    if v_isSharedCheck_3644_ == 0 {
                        v___x_3639_ = v___x_3609_;
                        v_isShared_3640_ = v_isSharedCheck_3644_;
                        state = 6;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3637_);
                        crate::leanh::lean_dec(v___x_3609_);
                        v___x_3639_ = crate::leanh::lean_box(0);
                        v_isShared_3640_ = v_isSharedCheck_3644_;
                        state = 6;
                        continue;
                    }
                }
            }
            2 => {
                if v_isShared_3624_ == 0 {
                    v___x_3626_ = v___x_3623_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_3627_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3627_, 0, v_a_3621_);
                    v___x_3626_ = v_reuseFailAlloc_3627_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_3626_;
            }
            4 => {
                if v_isShared_3632_ == 0 {
                    v___x_3634_ = v___x_3631_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_3635_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3635_, 0, v_a_3629_);
                    v___x_3634_ = v_reuseFailAlloc_3635_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_3634_;
            }
            6 => {
                if v_isShared_3640_ == 0 {
                    v___x_3642_ = v___x_3639_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_3643_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3643_, 0, v_a_3637_);
                    v___x_3642_ = v_reuseFailAlloc_3643_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_3642_;
            }
            8 => {
                v_sz_3656_ = lean_array_size(v___y_3655_);
                v___x_3657_ = 0usize;
                v___x_3658_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__5(v_sz_3656_, v___x_3657_, v___y_3655_);
                v___y_3599_ = v___y_3654_;
                v_subgoals_3600_ = v___x_3658_;
                v___y_3601_ = v___y_3647_;
                v___y_3602_ = v___y_3650_;
                v___y_3603_ = v___y_3652_;
                v___y_3604_ = v___y_3651_;
                v___y_3605_ = v___y_3646_;
                v___y_3606_ = v___y_3648_;
                v___y_3607_ = v___y_3649_;
                v___y_3608_ = v___y_3653_;
                state = 1;
                continue;
            }
            9 => {
                v___x_3673_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__6___redArg(v___y_3669_, v___y_3661_, v___y_3660_, v___y_3672_);
                crate::leanh::lean_dec(v___y_3672_);
                crate::leanh::lean_dec(v___y_3669_);
                v___y_3646_ = v___y_3667_;
                v___y_3647_ = v___y_3668_;
                v___y_3648_ = v___y_3662_;
                v___y_3649_ = v___y_3670_;
                v___y_3650_ = v___y_3671_;
                v___y_3651_ = v___y_3663_;
                v___y_3652_ = v___y_3664_;
                v___y_3653_ = v___y_3665_;
                v___y_3654_ = v___y_3666_;
                v___y_3655_ = v___x_3673_;
                state = 8;
                continue;
            }
            10 => {
                v___x_3688_ = lean_nat_dec_le(v___y_3687_, v___y_3677_);
                if v___x_3688_ == 0 {
                    crate::leanh::lean_dec(v___y_3677_);
                    crate::leanh::lean_inc(v___y_3687_);
                    v___y_3660_ = v___y_3687_;
                    v___y_3661_ = v___y_3675_;
                    v___y_3662_ = v___y_3676_;
                    v___y_3663_ = v___y_3678_;
                    v___y_3664_ = v___y_3679_;
                    v___y_3665_ = v___y_3680_;
                    v___y_3666_ = v___y_3681_;
                    v___y_3667_ = v___y_3682_;
                    v___y_3668_ = v___y_3683_;
                    v___y_3669_ = v___y_3684_;
                    v___y_3670_ = v___y_3685_;
                    v___y_3671_ = v___y_3686_;
                    v___y_3672_ = v___y_3687_;
                    state = 9;
                    continue;
                } else {
                    v___y_3660_ = v___y_3687_;
                    v___y_3661_ = v___y_3675_;
                    v___y_3662_ = v___y_3676_;
                    v___y_3663_ = v___y_3678_;
                    v___y_3664_ = v___y_3679_;
                    v___y_3665_ = v___y_3680_;
                    v___y_3666_ = v___y_3681_;
                    v___y_3667_ = v___y_3682_;
                    v___y_3668_ = v___y_3683_;
                    v___y_3669_ = v___y_3684_;
                    v___y_3670_ = v___y_3685_;
                    v___y_3671_ = v___y_3686_;
                    v___y_3672_ = v___y_3677_;
                    state = 9;
                    continue;
                }
            }
            11 => {
                v___x_3703_ = lean_array_get_size(v___y_3693_);
                v___x_3704_ = lean_nat_dec_eq(v___x_3703_, v___x_3690_);
                if v___x_3704_ == 0 {
                    v___x_3705_ = lean_nat_sub(v___x_3703_, v___x_3691_);
                    v___x_3706_ = lean_nat_dec_le(v___x_3690_, v___x_3705_);
                    if v___x_3706_ == 0 {
                        crate::leanh::lean_inc(v___x_3705_);
                        v___y_3675_ = v___y_3693_;
                        v___y_3676_ = v___y_3700_;
                        v___y_3677_ = v___x_3705_;
                        v___y_3678_ = v___y_3698_;
                        v___y_3679_ = v___y_3697_;
                        v___y_3680_ = v___y_3702_;
                        v___y_3681_ = v___y_3694_;
                        v___y_3682_ = v___y_3699_;
                        v___y_3683_ = v___y_3695_;
                        v___y_3684_ = v___x_3703_;
                        v___y_3685_ = v___y_3701_;
                        v___y_3686_ = v___y_3696_;
                        v___y_3687_ = v___x_3705_;
                        state = 10;
                        continue;
                    } else {
                        v___y_3675_ = v___y_3693_;
                        v___y_3676_ = v___y_3700_;
                        v___y_3677_ = v___x_3705_;
                        v___y_3678_ = v___y_3698_;
                        v___y_3679_ = v___y_3697_;
                        v___y_3680_ = v___y_3702_;
                        v___y_3681_ = v___y_3694_;
                        v___y_3682_ = v___y_3699_;
                        v___y_3683_ = v___y_3695_;
                        v___y_3684_ = v___x_3703_;
                        v___y_3685_ = v___y_3701_;
                        v___y_3686_ = v___y_3696_;
                        v___y_3687_ = v___x_3690_;
                        state = 10;
                        continue;
                    }
                } else {
                    v___y_3646_ = v___y_3699_;
                    v___y_3647_ = v___y_3695_;
                    v___y_3648_ = v___y_3700_;
                    v___y_3649_ = v___y_3701_;
                    v___y_3650_ = v___y_3696_;
                    v___y_3651_ = v___y_3698_;
                    v___y_3652_ = v___y_3697_;
                    v___y_3653_ = v___y_3702_;
                    v___y_3654_ = v___y_3694_;
                    v___y_3655_ = v___y_3693_;
                    state = 8;
                    continue;
                }
            }
            12 => {
                v___x_3724_ = l_Lean_Meta_Simp_Context_setMemoize(v___y_3721_, v___y_3723_);
                v___x_3725_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__6
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__6_once
                    ),
                    _init_l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__6,
                );
                crate::leanh::lean_inc(v___y_3713_);
                crate::leanh::lean_inc_ref(v___y_3722_);
                v___x_3726_ = crate::leanh::lean_alloc_closure(
                    l___private_Lean_Elab_Tactic_Conv_Pattern_0__Lean_Elab_Tactic_Conv_pre___boxed
                        as *mut core::ffi::c_void,
                    11,
                    2,
                );
                crate::leanh::lean_closure_set(v___x_3726_, 0, v___y_3722_);
                crate::leanh::lean_closure_set(v___x_3726_, 1, v___y_3713_);
                crate::leanh::lean_inc_ref(v___y_3712_);
                crate::leanh::lean_inc_ref(v___y_3720_);
                v___x_3727_ = crate::leanh::lean_alloc_ctor(0, 5, (1) as u32);
                crate::leanh::lean_ctor_set(v___x_3727_, 0, v___x_3726_);
                crate::leanh::lean_ctor_set(v___x_3727_, 1, v___y_3715_);
                crate::leanh::lean_ctor_set(v___x_3727_, 2, v___y_3720_);
                crate::leanh::lean_ctor_set(v___x_3727_, 3, v___f_3582_);
                crate::leanh::lean_ctor_set(v___x_3727_, 4, v___y_3712_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_3727_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 5) as u32,
                    v___x_3583_,
                );
                v___x_3728_ = l_Lean_Meta_Simp_main(
                    v___y_3711_,
                    v___x_3724_,
                    v___x_3725_,
                    v___x_3727_,
                    v___y_3708_,
                    v___y_3709_,
                    v___y_3710_,
                    v___y_3717_,
                );
                if crate::leanh::lean_obj_tag(v___x_3728_) == 0 {
                    v_a_3729_ = crate::leanh::lean_ctor_get(v___x_3728_, 0);
                    crate::leanh::lean_inc(v_a_3729_);
                    crate::leanh::lean_dec_ref_known(v___x_3728_, 1);
                    v_fst_3730_ = crate::leanh::lean_ctor_get(v_a_3729_, 0);
                    v_isSharedCheck_3805_ = (!crate::leanh::lean_is_exclusive(v_a_3729_)) as u8;
                    if v_isSharedCheck_3805_ == 0 {
                        v_unused_3806_ = crate::leanh::lean_ctor_get(v_a_3729_, 1);
                        crate::leanh::lean_dec(v_unused_3806_);
                        v___x_3732_ = v_a_3729_;
                        v_isShared_3733_ = v_isSharedCheck_3805_;
                        state = 13;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_fst_3730_);
                        crate::leanh::lean_dec(v_a_3729_);
                        v___x_3732_ = crate::leanh::lean_box(0);
                        v_isShared_3733_ = v_isSharedCheck_3805_;
                        state = 13;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v___y_3722_);
                    crate::leanh::lean_dec(v___y_3713_);
                    v_a_3807_ = crate::leanh::lean_ctor_get(v___x_3728_, 0);
                    v_isSharedCheck_3814_ = (!crate::leanh::lean_is_exclusive(v___x_3728_)) as u8;
                    if v_isSharedCheck_3814_ == 0 {
                        v___x_3809_ = v___x_3728_;
                        v_isShared_3810_ = v_isSharedCheck_3814_;
                        state = 25;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3807_);
                        crate::leanh::lean_dec(v___x_3728_);
                        v___x_3809_ = crate::leanh::lean_box(0);
                        v_isShared_3810_ = v_isSharedCheck_3814_;
                        state = 25;
                        continue;
                    }
                }
            }
            13 => {
                v___x_3734_ = lean_st_ref_get(v___y_3713_);
                crate::leanh::lean_dec(v___y_3713_);
                if crate::leanh::lean_obj_tag(v___x_3734_) == 0 {
                    v_subgoals_3735_ = crate::leanh::lean_ctor_get(v___x_3734_, 0);
                    crate::leanh::lean_inc_ref(v_subgoals_3735_);
                    crate::leanh::lean_dec_ref_known(v___x_3734_, 1);
                    v___x_3736_ = lean_array_get_size(v_subgoals_3735_);
                    v___x_3737_ = lean_nat_dec_eq(v___x_3736_, v___x_3690_);
                    if v___x_3737_ == 0 {
                        crate::leanh::lean_del_object(v___x_3732_);
                        crate::leanh::lean_dec_ref(v___y_3722_);
                        v___y_3599_ = v_fst_3730_;
                        v_subgoals_3600_ = v_subgoals_3735_;
                        v___y_3601_ = v___y_3718_;
                        v___y_3602_ = v___y_3719_;
                        v___y_3603_ = v___y_3716_;
                        v___y_3604_ = v___y_3714_;
                        v___y_3605_ = v___y_3708_;
                        v___y_3606_ = v___y_3709_;
                        v___y_3607_ = v___y_3710_;
                        v___y_3608_ = v___y_3717_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_dec_ref(v_subgoals_3735_);
                        crate::leanh::lean_dec(v_fst_3730_);
                        v_expr_3738_ = crate::leanh::lean_ctor_get(v___y_3722_, 2);
                        crate::leanh::lean_inc_ref(v_expr_3738_);
                        crate::leanh::lean_dec_ref(v___y_3722_);
                        v___x_3739_ = crate::leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(
                                l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__8
                            ),
                            core::ptr::addr_of_mut!(
                                l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__8_once
                            ),
                            _init_l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__8,
                        );
                        v___x_3740_ = l_Lean_indentExpr(v_expr_3738_);
                        if v_isShared_3733_ == 0 {
                            crate::leanh::lean_ctor_set_tag(v___x_3732_, 7);
                            crate::leanh::lean_ctor_set(v___x_3732_, 1, v___x_3740_);
                            crate::leanh::lean_ctor_set(v___x_3732_, 0, v___x_3739_);
                            v___x_3742_ = v___x_3732_;
                            state = 14;
                            continue;
                        } else {
                            v_reuseFailAlloc_3752_ =
                                crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_3752_, 0, v___x_3739_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_3752_, 1, v___x_3740_);
                            v___x_3742_ = v_reuseFailAlloc_3752_;
                            state = 14;
                            continue;
                        }
                    }
                } else {
                    v_subgoals_3753_ = crate::leanh::lean_ctor_get(v___x_3734_, 0);
                    crate::leanh::lean_inc_ref(v_subgoals_3753_);
                    v_idx_3754_ = crate::leanh::lean_ctor_get(v___x_3734_, 1);
                    crate::leanh::lean_inc(v_idx_3754_);
                    v_remaining_3755_ = crate::leanh::lean_ctor_get(v___x_3734_, 2);
                    crate::leanh::lean_inc(v_remaining_3755_);
                    crate::leanh::lean_dec_ref_known(v___x_3734_, 3);
                    v___x_3756_ = lean_nat_dec_eq(v_idx_3754_, v___x_3690_);
                    if v___x_3756_ == 0 {
                        crate::leanh::lean_dec_ref(v___y_3722_);
                        v___x_3757_ = l_List_getLast_x3f___redArg(v_remaining_3755_);
                        crate::leanh::lean_dec(v_remaining_3755_);
                        if crate::leanh::lean_obj_tag(v___x_3757_) == 1 {
                            crate::leanh::lean_dec_ref(v_subgoals_3753_);
                            crate::leanh::lean_dec(v_fst_3730_);
                            v_val_3758_ = crate::leanh::lean_ctor_get(v___x_3757_, 0);
                            v_isSharedCheck_3789_ =
                                (!crate::leanh::lean_is_exclusive(v___x_3757_)) as u8;
                            if v_isSharedCheck_3789_ == 0 {
                                v___x_3760_ = v___x_3757_;
                                v_isShared_3761_ = v_isSharedCheck_3789_;
                                state = 17;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_val_3758_);
                                crate::leanh::lean_dec(v___x_3757_);
                                v___x_3760_ = crate::leanh::lean_box(0);
                                v_isShared_3761_ = v_isSharedCheck_3789_;
                                state = 17;
                                continue;
                            }
                        } else {
                            crate::leanh::lean_dec(v___x_3757_);
                            crate::leanh::lean_dec(v_idx_3754_);
                            crate::leanh::lean_del_object(v___x_3732_);
                            v___y_3693_ = v_subgoals_3753_;
                            v___y_3694_ = v_fst_3730_;
                            v___y_3695_ = v___y_3718_;
                            v___y_3696_ = v___y_3719_;
                            v___y_3697_ = v___y_3716_;
                            v___y_3698_ = v___y_3714_;
                            v___y_3699_ = v___y_3708_;
                            v___y_3700_ = v___y_3709_;
                            v___y_3701_ = v___y_3710_;
                            v___y_3702_ = v___y_3717_;
                            state = 11;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec(v_remaining_3755_);
                        crate::leanh::lean_dec(v_idx_3754_);
                        crate::leanh::lean_dec_ref(v_subgoals_3753_);
                        crate::leanh::lean_dec(v_fst_3730_);
                        v_expr_3790_ = crate::leanh::lean_ctor_get(v___y_3722_, 2);
                        crate::leanh::lean_inc_ref(v_expr_3790_);
                        crate::leanh::lean_dec_ref(v___y_3722_);
                        v___x_3791_ = crate::leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(
                                l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__8
                            ),
                            core::ptr::addr_of_mut!(
                                l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__8_once
                            ),
                            _init_l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__8,
                        );
                        v___x_3792_ = l_Lean_indentExpr(v_expr_3790_);
                        if v_isShared_3733_ == 0 {
                            crate::leanh::lean_ctor_set_tag(v___x_3732_, 7);
                            crate::leanh::lean_ctor_set(v___x_3732_, 1, v___x_3792_);
                            crate::leanh::lean_ctor_set(v___x_3732_, 0, v___x_3791_);
                            v___x_3794_ = v___x_3732_;
                            state = 22;
                            continue;
                        } else {
                            v_reuseFailAlloc_3804_ =
                                crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_3804_, 0, v___x_3791_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_3804_, 1, v___x_3792_);
                            v___x_3794_ = v_reuseFailAlloc_3804_;
                            state = 22;
                            continue;
                        }
                    }
                }
            }
            14 => {
                v___x_3743_ =
                    l_Lean_throwError___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__4___redArg(
                        v___x_3742_,
                        v___y_3708_,
                        v___y_3709_,
                        v___y_3710_,
                        v___y_3717_,
                    );
                v_a_3744_ = crate::leanh::lean_ctor_get(v___x_3743_, 0);
                v_isSharedCheck_3751_ = (!crate::leanh::lean_is_exclusive(v___x_3743_)) as u8;
                if v_isSharedCheck_3751_ == 0 {
                    v___x_3746_ = v___x_3743_;
                    v_isShared_3747_ = v_isSharedCheck_3751_;
                    state = 15;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_a_3744_);
                    crate::leanh::lean_dec(v___x_3743_);
                    v___x_3746_ = crate::leanh::lean_box(0);
                    v_isShared_3747_ = v_isSharedCheck_3751_;
                    state = 15;
                    continue;
                }
            }
            15 => {
                if v_isShared_3747_ == 0 {
                    v___x_3749_ = v___x_3746_;
                    state = 16;
                    continue;
                } else {
                    v_reuseFailAlloc_3750_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3750_, 0, v_a_3744_);
                    v___x_3749_ = v_reuseFailAlloc_3750_;
                    state = 16;
                    continue;
                }
            }
            16 => {
                return v___x_3749_;
            }
            17 => {
                v_fst_3762_ = crate::leanh::lean_ctor_get(v_val_3758_, 0);
                v_isSharedCheck_3787_ = (!crate::leanh::lean_is_exclusive(v_val_3758_)) as u8;
                if v_isSharedCheck_3787_ == 0 {
                    v_unused_3788_ = crate::leanh::lean_ctor_get(v_val_3758_, 1);
                    crate::leanh::lean_dec(v_unused_3788_);
                    v___x_3764_ = v_val_3758_;
                    v_isShared_3765_ = v_isSharedCheck_3787_;
                    state = 18;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_fst_3762_);
                    crate::leanh::lean_dec(v_val_3758_);
                    v___x_3764_ = crate::leanh::lean_box(0);
                    v_isShared_3765_ = v_isSharedCheck_3787_;
                    state = 18;
                    continue;
                }
            }
            18 => {
                v___x_3766_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__10
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__10_once
                    ),
                    _init_l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__10,
                );
                v___x_3767_ = l_Nat_reprFast(v_idx_3754_);
                if v_isShared_3761_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_3760_, 3);
                    crate::leanh::lean_ctor_set(v___x_3760_, 0, v___x_3767_);
                    v___x_3769_ = v___x_3760_;
                    state = 19;
                    continue;
                } else {
                    v_reuseFailAlloc_3786_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3786_, 0, v___x_3767_);
                    v___x_3769_ = v_reuseFailAlloc_3786_;
                    state = 19;
                    continue;
                }
            }
            19 => {
                v___x_3770_ = l_Lean_MessageData_ofFormat(v___x_3769_);
                if v_isShared_3765_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_3764_, 7);
                    crate::leanh::lean_ctor_set(v___x_3764_, 1, v___x_3770_);
                    crate::leanh::lean_ctor_set(v___x_3764_, 0, v___x_3766_);
                    v___x_3772_ = v___x_3764_;
                    state = 20;
                    continue;
                } else {
                    v_reuseFailAlloc_3785_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3785_, 0, v___x_3766_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3785_, 1, v___x_3770_);
                    v___x_3772_ = v_reuseFailAlloc_3785_;
                    state = 20;
                    continue;
                }
            }
            20 => {
                v___x_3773_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__12
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__12_once
                    ),
                    _init_l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__12,
                );
                if v_isShared_3733_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_3732_, 7);
                    crate::leanh::lean_ctor_set(v___x_3732_, 1, v___x_3773_);
                    crate::leanh::lean_ctor_set(v___x_3732_, 0, v___x_3772_);
                    v___x_3775_ = v___x_3732_;
                    state = 21;
                    continue;
                } else {
                    v_reuseFailAlloc_3784_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3784_, 0, v___x_3772_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3784_, 1, v___x_3773_);
                    v___x_3775_ = v_reuseFailAlloc_3784_;
                    state = 21;
                    continue;
                }
            }
            21 => {
                v___x_3776_ = lean_nat_add(v_fst_3762_, v___x_3691_);
                crate::leanh::lean_dec(v_fst_3762_);
                v___x_3777_ = l_Nat_reprFast(v___x_3776_);
                v___x_3778_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3778_, 0, v___x_3777_);
                v___x_3779_ = l_Lean_MessageData_ofFormat(v___x_3778_);
                v___x_3780_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3780_, 0, v___x_3775_);
                crate::leanh::lean_ctor_set(v___x_3780_, 1, v___x_3779_);
                v___x_3781_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__14
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__14_once
                    ),
                    _init_l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__14,
                );
                v___x_3782_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3782_, 0, v___x_3780_);
                crate::leanh::lean_ctor_set(v___x_3782_, 1, v___x_3781_);
                v___x_3783_ =
                    l_Lean_throwError___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__4___redArg(
                        v___x_3782_,
                        v___y_3708_,
                        v___y_3709_,
                        v___y_3710_,
                        v___y_3717_,
                    );
                return v___x_3783_;
            }
            22 => {
                v___x_3795_ =
                    l_Lean_throwError___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__4___redArg(
                        v___x_3794_,
                        v___y_3708_,
                        v___y_3709_,
                        v___y_3710_,
                        v___y_3717_,
                    );
                v_a_3796_ = crate::leanh::lean_ctor_get(v___x_3795_, 0);
                v_isSharedCheck_3803_ = (!crate::leanh::lean_is_exclusive(v___x_3795_)) as u8;
                if v_isSharedCheck_3803_ == 0 {
                    v___x_3798_ = v___x_3795_;
                    v_isShared_3799_ = v_isSharedCheck_3803_;
                    state = 23;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_a_3796_);
                    crate::leanh::lean_dec(v___x_3795_);
                    v___x_3798_ = crate::leanh::lean_box(0);
                    v_isShared_3799_ = v_isSharedCheck_3803_;
                    state = 23;
                    continue;
                }
            }
            23 => {
                if v_isShared_3799_ == 0 {
                    v___x_3801_ = v___x_3798_;
                    state = 24;
                    continue;
                } else {
                    v_reuseFailAlloc_3802_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3802_, 0, v_a_3796_);
                    v___x_3801_ = v_reuseFailAlloc_3802_;
                    state = 24;
                    continue;
                }
            }
            24 => {
                return v___x_3801_;
            }
            25 => {
                if v_isShared_3810_ == 0 {
                    v___x_3812_ = v___x_3809_;
                    state = 26;
                    continue;
                } else {
                    v_reuseFailAlloc_3813_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3813_, 0, v_a_3807_);
                    v___x_3812_ = v_reuseFailAlloc_3813_;
                    state = 26;
                    continue;
                }
            }
            26 => {
                return v___x_3812_;
            }
            27 => {
                crate::leanh::lean_inc_ref(v_occs_3821_);
                v___x_3830_ = lean_st_mk_ref(v_occs_3821_);
                v___x_3831_ = l___private_Lean_Elab_Tactic_Conv_Pattern_0__Lean_Elab_Tactic_Conv_getContext___redArg(v___y_3826_, v___y_3828_, v___y_3829_);
                if crate::leanh::lean_obj_tag(v___x_3831_) == 0 {
                    if crate::leanh::lean_obj_tag(v_occs_3821_) == 0 {
                        crate::leanh::lean_dec_ref_known(v_occs_3821_, 1);
                        v_a_3832_ = crate::leanh::lean_ctor_get(v___x_3831_, 0);
                        crate::leanh::lean_inc(v_a_3832_);
                        crate::leanh::lean_dec_ref_known(v___x_3831_, 1);
                        v___y_3708_ = v___y_3826_;
                        v___y_3709_ = v___y_3827_;
                        v___y_3710_ = v___y_3828_;
                        v___y_3711_ = v___y_3816_;
                        v___y_3712_ = v___y_3818_;
                        v___y_3713_ = v___x_3830_;
                        v___y_3714_ = v___y_3825_;
                        v___y_3715_ = v___y_3819_;
                        v___y_3716_ = v___y_3824_;
                        v___y_3717_ = v___y_3829_;
                        v___y_3718_ = v___y_3822_;
                        v___y_3719_ = v___y_3823_;
                        v___y_3720_ = v___y_3817_;
                        v___y_3721_ = v_a_3832_;
                        v___y_3722_ = v___y_3820_;
                        v___y_3723_ = v___x_3583_;
                        state = 12;
                        continue;
                    } else {
                        crate::leanh::lean_dec_ref(v_occs_3821_);
                        v_a_3833_ = crate::leanh::lean_ctor_get(v___x_3831_, 0);
                        crate::leanh::lean_inc(v_a_3833_);
                        crate::leanh::lean_dec_ref_known(v___x_3831_, 1);
                        v___x_3834_ = 0;
                        v___y_3708_ = v___y_3826_;
                        v___y_3709_ = v___y_3827_;
                        v___y_3710_ = v___y_3828_;
                        v___y_3711_ = v___y_3816_;
                        v___y_3712_ = v___y_3818_;
                        v___y_3713_ = v___x_3830_;
                        v___y_3714_ = v___y_3825_;
                        v___y_3715_ = v___y_3819_;
                        v___y_3716_ = v___y_3824_;
                        v___y_3717_ = v___y_3829_;
                        v___y_3718_ = v___y_3822_;
                        v___y_3719_ = v___y_3823_;
                        v___y_3720_ = v___y_3817_;
                        v___y_3721_ = v_a_3833_;
                        v___y_3722_ = v___y_3820_;
                        v___y_3723_ = v___x_3834_;
                        state = 12;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v___x_3830_);
                    crate::leanh::lean_dec_ref(v_occs_3821_);
                    crate::leanh::lean_dec_ref(v___y_3820_);
                    crate::leanh::lean_dec_ref(v___y_3819_);
                    crate::leanh::lean_dec_ref(v___y_3816_);
                    crate::leanh::lean_dec_ref(v___f_3582_);
                    v_a_3835_ = crate::leanh::lean_ctor_get(v___x_3831_, 0);
                    v_isSharedCheck_3842_ = (!crate::leanh::lean_is_exclusive(v___x_3831_)) as u8;
                    if v_isSharedCheck_3842_ == 0 {
                        v___x_3837_ = v___x_3831_;
                        v_isShared_3838_ = v_isSharedCheck_3842_;
                        state = 28;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3835_);
                        crate::leanh::lean_dec(v___x_3831_);
                        v___x_3837_ = crate::leanh::lean_box(0);
                        v_isShared_3838_ = v_isSharedCheck_3842_;
                        state = 28;
                        continue;
                    }
                }
            }
            28 => {
                if v_isShared_3838_ == 0 {
                    v___x_3840_ = v___x_3837_;
                    state = 29;
                    continue;
                } else {
                    v_reuseFailAlloc_3841_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3841_, 0, v_a_3835_);
                    v___x_3840_ = v_reuseFailAlloc_3841_;
                    state = 29;
                    continue;
                }
            }
            29 => {
                return v___x_3840_;
            }
            30 => {
                v___x_3858_ = l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__15;
                v___x_3859_ = lean_array_to_list(v___y_3846_);
                v___x_3860_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3860_, 0, v___x_3858_);
                crate::leanh::lean_ctor_set(v___x_3860_, 1, v___x_3690_);
                crate::leanh::lean_ctor_set(v___x_3860_, 2, v___x_3859_);
                v___y_3816_ = v___y_3844_;
                v___y_3817_ = v___y_3845_;
                v___y_3818_ = v___y_3847_;
                v___y_3819_ = v___y_3848_;
                v___y_3820_ = v___y_3849_;
                v_occs_3821_ = v___x_3860_;
                v___y_3822_ = v___y_3850_;
                v___y_3823_ = v___y_3851_;
                v___y_3824_ = v___y_3852_;
                v___y_3825_ = v___y_3853_;
                v___y_3826_ = v___y_3854_;
                v___y_3827_ = v___y_3855_;
                v___y_3828_ = v___y_3856_;
                v___y_3829_ = v___y_3857_;
                state = 27;
                continue;
            }
            31 => {
                v___x_3876_ =
                    l_Array_allDiff___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__8(v___y_3875_);
                if v___x_3876_ == 0 {
                    crate::leanh::lean_dec_ref(v___y_3875_);
                    crate::leanh::lean_dec_ref(v___y_3872_);
                    crate::leanh::lean_dec_ref(v___y_3864_);
                    crate::leanh::lean_dec_ref(v___y_3862_);
                    crate::leanh::lean_dec_ref(v___f_3582_);
                    v___x_3877_ = crate::leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(
                            l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__17
                        ),
                        core::ptr::addr_of_mut!(
                            l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__17_once
                        ),
                        _init_l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__17,
                    );
                    v___x_3878_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__4___redArg(v___x_3877_, v___y_3870_, v___y_3867_, v___y_3866_, v___y_3868_);
                    return v___x_3878_;
                } else {
                    v___y_3844_ = v___y_3862_;
                    v___y_3845_ = v___y_3869_;
                    v___y_3846_ = v___y_3875_;
                    v___y_3847_ = v___y_3863_;
                    v___y_3848_ = v___y_3864_;
                    v___y_3849_ = v___y_3872_;
                    v___y_3850_ = v___y_3865_;
                    v___y_3851_ = v___y_3874_;
                    v___y_3852_ = v___y_3871_;
                    v___y_3853_ = v___y_3873_;
                    v___y_3854_ = v___y_3870_;
                    v___y_3855_ = v___y_3867_;
                    v___y_3856_ = v___y_3866_;
                    v___y_3857_ = v___y_3868_;
                    state = 30;
                    continue;
                }
            }
            32 => {
                v___x_3897_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__9___redArg(v___y_3887_, v___y_3880_, v___y_3883_, v___y_3896_);
                crate::leanh::lean_dec(v___y_3896_);
                crate::leanh::lean_dec(v___y_3887_);
                v___y_3862_ = v___y_3881_;
                v___y_3863_ = v___y_3882_;
                v___y_3864_ = v___y_3884_;
                v___y_3865_ = v___y_3885_;
                v___y_3866_ = v___y_3886_;
                v___y_3867_ = v___y_3888_;
                v___y_3868_ = v___y_3889_;
                v___y_3869_ = v___y_3890_;
                v___y_3870_ = v___y_3891_;
                v___y_3871_ = v___y_3892_;
                v___y_3872_ = v___y_3894_;
                v___y_3873_ = v___y_3893_;
                v___y_3874_ = v___y_3895_;
                v___y_3875_ = v___x_3897_;
                state = 31;
                continue;
            }
            33 => {
                v___x_3916_ = lean_nat_dec_le(v___y_3915_, v___y_3901_);
                if v___x_3916_ == 0 {
                    crate::leanh::lean_dec(v___y_3901_);
                    crate::leanh::lean_inc(v___y_3915_);
                    v___y_3880_ = v___y_3899_;
                    v___y_3881_ = v___y_3900_;
                    v___y_3882_ = v___y_3902_;
                    v___y_3883_ = v___y_3915_;
                    v___y_3884_ = v___y_3903_;
                    v___y_3885_ = v___y_3904_;
                    v___y_3886_ = v___y_3905_;
                    v___y_3887_ = v___y_3906_;
                    v___y_3888_ = v___y_3907_;
                    v___y_3889_ = v___y_3908_;
                    v___y_3890_ = v___y_3909_;
                    v___y_3891_ = v___y_3910_;
                    v___y_3892_ = v___y_3911_;
                    v___y_3893_ = v___y_3913_;
                    v___y_3894_ = v___y_3912_;
                    v___y_3895_ = v___y_3914_;
                    v___y_3896_ = v___y_3915_;
                    state = 32;
                    continue;
                } else {
                    v___y_3880_ = v___y_3899_;
                    v___y_3881_ = v___y_3900_;
                    v___y_3882_ = v___y_3902_;
                    v___y_3883_ = v___y_3915_;
                    v___y_3884_ = v___y_3903_;
                    v___y_3885_ = v___y_3904_;
                    v___y_3886_ = v___y_3905_;
                    v___y_3887_ = v___y_3906_;
                    v___y_3888_ = v___y_3907_;
                    v___y_3889_ = v___y_3908_;
                    v___y_3890_ = v___y_3909_;
                    v___y_3891_ = v___y_3910_;
                    v___y_3892_ = v___y_3911_;
                    v___y_3893_ = v___y_3913_;
                    v___y_3894_ = v___y_3912_;
                    v___y_3895_ = v___y_3914_;
                    v___y_3896_ = v___y_3901_;
                    state = 32;
                    continue;
                }
            }
            34 => {
                v_declName_x3f_3927_ = crate::leanh::lean_ctor_get(v___y_3921_, 0);
                v_macroStack_3928_ = crate::leanh::lean_ctor_get(v___y_3921_, 1);
                v_mayPostpone_3929_ = crate::leanh::lean_ctor_get_uint8(
                    v___y_3921_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 8) as u32,
                );
                v_errToSorry_3930_ = crate::leanh::lean_ctor_get_uint8(
                    v___y_3921_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 8 + 1) as u32,
                );
                v_autoBoundImplicitContext_3931_ = crate::leanh::lean_ctor_get(v___y_3921_, 2);
                v_autoBoundImplicitForbidden_3932_ = crate::leanh::lean_ctor_get(v___y_3921_, 3);
                v_sectionVars_3933_ = crate::leanh::lean_ctor_get(v___y_3921_, 4);
                v_sectionFVars_3934_ = crate::leanh::lean_ctor_get(v___y_3921_, 5);
                v_implicitLambda_3935_ = crate::leanh::lean_ctor_get_uint8(
                    v___y_3921_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 8 + 2) as u32,
                );
                v_heedElabAsElim_3936_ = crate::leanh::lean_ctor_get_uint8(
                    v___y_3921_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 8 + 3) as u32,
                );
                v_isNoncomputableSection_3937_ = crate::leanh::lean_ctor_get_uint8(
                    v___y_3921_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 8 + 4) as u32,
                );
                v_isMetaSection_3938_ = crate::leanh::lean_ctor_get_uint8(
                    v___y_3921_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 8 + 5) as u32,
                );
                v_inPattern_3939_ = crate::leanh::lean_ctor_get_uint8(
                    v___y_3921_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 8 + 7) as u32,
                );
                v_tacSnap_x3f_3940_ = crate::leanh::lean_ctor_get(v___y_3921_, 6);
                v_saveRecAppSyntax_3941_ = crate::leanh::lean_ctor_get_uint8(
                    v___y_3921_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 8 + 8) as u32,
                );
                v_holesAsSyntheticOpaque_3942_ = crate::leanh::lean_ctor_get_uint8(
                    v___y_3921_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 8 + 9) as u32,
                );
                v_checkDeprecated_3943_ = crate::leanh::lean_ctor_get_uint8(
                    v___y_3921_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 8 + 10) as u32,
                );
                v_fixedTermElabs_3944_ = crate::leanh::lean_ctor_get(v___y_3921_, 7);
                v___x_3945_ = crate::leanh::lean_unsigned_to_nat(2);
                v___x_3946_ = l_Lean_Syntax_getArg(v_stx_3584_, v___x_3945_);
                v___x_3947_ = crate::leanh::lean_box(0);
                v___x_3948_ = crate::leanh::lean_box((v___x_3583_) as usize);
                crate::leanh::lean_inc(v___x_3946_);
                v___f_3949_ = crate::leanh::lean_alloc_closure(
                    l_Lean_Elab_Tactic_Conv_evalPattern___lam__1___boxed as *mut core::ffi::c_void,
                    10,
                    3,
                );
                crate::leanh::lean_closure_set(v___f_3949_, 0, v___x_3946_);
                crate::leanh::lean_closure_set(v___f_3949_, 1, v___x_3947_);
                crate::leanh::lean_closure_set(v___f_3949_, 2, v___x_3948_);
                v___f_3950_ = crate::leanh::lean_alloc_closure(
                    l_Lean_Elab_Tactic_Conv_evalPattern___lam__2___boxed as *mut core::ffi::c_void,
                    9,
                    2,
                );
                crate::leanh::lean_closure_set(v___f_3950_, 0, v___x_3946_);
                crate::leanh::lean_closure_set(v___f_3950_, 1, v___f_3949_);
                crate::leanh::lean_inc_ref(v_fixedTermElabs_3944_);
                crate::leanh::lean_inc(v_tacSnap_x3f_3940_);
                crate::leanh::lean_inc(v_sectionFVars_3934_);
                crate::leanh::lean_inc(v_sectionVars_3933_);
                crate::leanh::lean_inc_ref(v_autoBoundImplicitForbidden_3932_);
                crate::leanh::lean_inc(v_autoBoundImplicitContext_3931_);
                crate::leanh::lean_inc(v_macroStack_3928_);
                crate::leanh::lean_inc(v_declName_x3f_3927_);
                v___x_3951_ = crate::leanh::lean_alloc_ctor(0, 8, (11) as u32);
                crate::leanh::lean_ctor_set(v___x_3951_, 0, v_declName_x3f_3927_);
                crate::leanh::lean_ctor_set(v___x_3951_, 1, v_macroStack_3928_);
                crate::leanh::lean_ctor_set(v___x_3951_, 2, v_autoBoundImplicitContext_3931_);
                crate::leanh::lean_ctor_set(v___x_3951_, 3, v_autoBoundImplicitForbidden_3932_);
                crate::leanh::lean_ctor_set(v___x_3951_, 4, v_sectionVars_3933_);
                crate::leanh::lean_ctor_set(v___x_3951_, 5, v_sectionFVars_3934_);
                crate::leanh::lean_ctor_set(v___x_3951_, 6, v_tacSnap_x3f_3940_);
                crate::leanh::lean_ctor_set(v___x_3951_, 7, v_fixedTermElabs_3944_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_3951_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 8) as u32,
                    v_mayPostpone_3929_,
                );
                crate::leanh::lean_ctor_set_uint8(
                    v___x_3951_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 8 + 1) as u32,
                    v_errToSorry_3930_,
                );
                crate::leanh::lean_ctor_set_uint8(
                    v___x_3951_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 8 + 2) as u32,
                    v_implicitLambda_3935_,
                );
                crate::leanh::lean_ctor_set_uint8(
                    v___x_3951_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 8 + 3) as u32,
                    v_heedElabAsElim_3936_,
                );
                crate::leanh::lean_ctor_set_uint8(
                    v___x_3951_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 8 + 4) as u32,
                    v_isNoncomputableSection_3937_,
                );
                crate::leanh::lean_ctor_set_uint8(
                    v___x_3951_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 8 + 5) as u32,
                    v_isMetaSection_3938_,
                );
                crate::leanh::lean_ctor_set_uint8(
                    v___x_3951_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 8 + 6) as u32,
                    v___x_3583_,
                );
                crate::leanh::lean_ctor_set_uint8(
                    v___x_3951_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 8 + 7) as u32,
                    v_inPattern_3939_,
                );
                crate::leanh::lean_ctor_set_uint8(
                    v___x_3951_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 8 + 8) as u32,
                    v_saveRecAppSyntax_3941_,
                );
                crate::leanh::lean_ctor_set_uint8(
                    v___x_3951_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 8 + 9) as u32,
                    v_holesAsSyntheticOpaque_3942_,
                );
                crate::leanh::lean_ctor_set_uint8(
                    v___x_3951_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 8 + 10) as u32,
                    v_checkDeprecated_3943_,
                );
                v___x_3952_ = l_Lean_Elab_Term_withoutModifyingElabMetaStateWithInfo___redArg(
                    v___f_3950_,
                    v___x_3951_,
                    v___y_3922_,
                    v___y_3923_,
                    v___y_3924_,
                    v___y_3925_,
                    v___y_3926_,
                );
                crate::leanh::lean_dec_ref_known(v___x_3951_, 8);
                if crate::leanh::lean_obj_tag(v___x_3952_) == 0 {
                    v_a_3953_ = crate::leanh::lean_ctor_get(v___x_3952_, 0);
                    crate::leanh::lean_inc(v_a_3953_);
                    crate::leanh::lean_dec_ref_known(v___x_3952_, 1);
                    v___x_3954_ = l_Lean_Elab_Tactic_Conv_getLhs___redArg(
                        v___y_3920_,
                        v___y_3923_,
                        v___y_3924_,
                        v___y_3925_,
                        v___y_3926_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_3954_) == 0 {
                        v_a_3955_ = crate::leanh::lean_ctor_get(v___x_3954_, 0);
                        crate::leanh::lean_inc(v_a_3955_);
                        crate::leanh::lean_dec_ref_known(v___x_3954_, 1);
                        v___x_3956_ = crate::leanh::lean_box((v___x_3583_) as usize);
                        v___f_3957_ = crate::leanh::lean_alloc_closure(
                            l_Lean_Elab_Tactic_Conv_evalPattern___lam__3___boxed
                                as *mut core::ffi::c_void,
                            11,
                            2,
                        );
                        crate::leanh::lean_closure_set(v___f_3957_, 0, v___x_3947_);
                        crate::leanh::lean_closure_set(v___f_3957_, 1, v___x_3956_);
                        v___f_3958_ = l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__18;
                        v___f_3959_ = l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__19;
                        if crate::leanh::lean_obj_tag(v_occs_3918_) == 0 {
                            crate::leanh::lean_dec_ref(v___x_3588_);
                            crate::leanh::lean_dec_ref(v___x_3587_);
                            crate::leanh::lean_dec_ref(v___x_3586_);
                            crate::leanh::lean_dec_ref(v___x_3585_);
                            v___x_3960_ = l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__22;
                            v___y_3816_ = v_a_3955_;
                            v___y_3817_ = v___f_3958_;
                            v___y_3818_ = v___f_3959_;
                            v___y_3819_ = v___f_3957_;
                            v___y_3820_ = v_a_3953_;
                            v_occs_3821_ = v___x_3960_;
                            v___y_3822_ = v___y_3919_;
                            v___y_3823_ = v___y_3920_;
                            v___y_3824_ = v___y_3921_;
                            v___y_3825_ = v___y_3922_;
                            v___y_3826_ = v___y_3923_;
                            v___y_3827_ = v___y_3924_;
                            v___y_3828_ = v___y_3925_;
                            v___y_3829_ = v___y_3926_;
                            state = 27;
                            continue;
                        } else {
                            v_val_3961_ = crate::leanh::lean_ctor_get(v_occs_3918_, 0);
                            crate::leanh::lean_inc_n(v_val_3961_, 2);
                            crate::leanh::lean_dec_ref_known(v_occs_3918_, 1);
                            v___x_3962_ = l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__23;
                            crate::leanh::lean_inc_ref(v___x_3588_);
                            crate::leanh::lean_inc_ref(v___x_3587_);
                            crate::leanh::lean_inc_ref(v___x_3586_);
                            crate::leanh::lean_inc_ref(v___x_3585_);
                            v___x_3963_ = l_Lean_Name_mkStr5(
                                v___x_3585_,
                                v___x_3586_,
                                v___x_3587_,
                                v___x_3588_,
                                v___x_3962_,
                            );
                            v___x_3964_ = l_Lean_Syntax_isOfKind(v_val_3961_, v___x_3963_);
                            crate::leanh::lean_dec(v___x_3963_);
                            if v___x_3964_ == 0 {
                                v___x_3965_ =
                                    l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__24;
                                v___x_3966_ = l_Lean_Name_mkStr5(
                                    v___x_3585_,
                                    v___x_3586_,
                                    v___x_3587_,
                                    v___x_3588_,
                                    v___x_3965_,
                                );
                                crate::leanh::lean_inc(v_val_3961_);
                                v___x_3967_ = l_Lean_Syntax_isOfKind(v_val_3961_, v___x_3966_);
                                crate::leanh::lean_dec(v___x_3966_);
                                if v___x_3967_ == 0 {
                                    crate::leanh::lean_dec(v_val_3961_);
                                    crate::leanh::lean_dec_ref(v___f_3957_);
                                    crate::leanh::lean_dec(v_a_3955_);
                                    crate::leanh::lean_dec(v_a_3953_);
                                    crate::leanh::lean_dec_ref(v___f_3582_);
                                    v___x_3968_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__0___redArg();
                                    v_a_3969_ = crate::leanh::lean_ctor_get(v___x_3968_, 0);
                                    v_isSharedCheck_3976_ =
                                        (!crate::leanh::lean_is_exclusive(v___x_3968_)) as u8;
                                    if v_isSharedCheck_3976_ == 0 {
                                        v___x_3971_ = v___x_3968_;
                                        v_isShared_3972_ = v_isSharedCheck_3976_;
                                        state = 35;
                                        continue;
                                    } else {
                                        crate::leanh::lean_inc(v_a_3969_);
                                        crate::leanh::lean_dec(v___x_3968_);
                                        v___x_3971_ = crate::leanh::lean_box(0);
                                        v_isShared_3972_ = v_isSharedCheck_3976_;
                                        state = 35;
                                        continue;
                                    }
                                } else {
                                    v___x_3977_ = l_Lean_Syntax_getArg(v_val_3961_, v___x_3690_);
                                    crate::leanh::lean_dec(v_val_3961_);
                                    v___x_3978_ = l_Lean_Syntax_getArgs(v___x_3977_);
                                    crate::leanh::lean_dec(v___x_3977_);
                                    v___x_3979_ = lean_array_get_size(v___x_3978_);
                                    v___x_3980_ = lean_mk_empty_array_with_capacity(v___x_3979_);
                                    v___x_3981_ = l_Array_mapFinIdxM_map___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__7___redArg(v___x_3978_, v___x_3979_, v___x_3690_, v___x_3980_, v___y_3919_, v___y_3920_, v___y_3921_, v___y_3922_, v___y_3923_, v___y_3924_, v___y_3925_, v___y_3926_);
                                    crate::leanh::lean_dec_ref(v___x_3978_);
                                    if crate::leanh::lean_obj_tag(v___x_3981_) == 0 {
                                        v_a_3982_ = crate::leanh::lean_ctor_get(v___x_3981_, 0);
                                        crate::leanh::lean_inc(v_a_3982_);
                                        crate::leanh::lean_dec_ref_known(v___x_3981_, 1);
                                        v___x_3983_ = lean_array_get_size(v_a_3982_);
                                        v___x_3984_ = lean_nat_dec_eq(v___x_3983_, v___x_3690_);
                                        if v___x_3984_ == 0 {
                                            v___x_3985_ = lean_nat_sub(v___x_3983_, v___x_3691_);
                                            v___x_3986_ = lean_nat_dec_le(v___x_3690_, v___x_3985_);
                                            if v___x_3986_ == 0 {
                                                crate::leanh::lean_inc(v___x_3985_);
                                                v___y_3899_ = v_a_3982_;
                                                v___y_3900_ = v_a_3955_;
                                                v___y_3901_ = v___x_3985_;
                                                v___y_3902_ = v___f_3959_;
                                                v___y_3903_ = v___f_3957_;
                                                v___y_3904_ = v___y_3919_;
                                                v___y_3905_ = v___y_3925_;
                                                v___y_3906_ = v___x_3983_;
                                                v___y_3907_ = v___y_3924_;
                                                v___y_3908_ = v___y_3926_;
                                                v___y_3909_ = v___f_3958_;
                                                v___y_3910_ = v___y_3923_;
                                                v___y_3911_ = v___y_3921_;
                                                v___y_3912_ = v_a_3953_;
                                                v___y_3913_ = v___y_3922_;
                                                v___y_3914_ = v___y_3920_;
                                                v___y_3915_ = v___x_3985_;
                                                state = 33;
                                                continue;
                                            } else {
                                                v___y_3899_ = v_a_3982_;
                                                v___y_3900_ = v_a_3955_;
                                                v___y_3901_ = v___x_3985_;
                                                v___y_3902_ = v___f_3959_;
                                                v___y_3903_ = v___f_3957_;
                                                v___y_3904_ = v___y_3919_;
                                                v___y_3905_ = v___y_3925_;
                                                v___y_3906_ = v___x_3983_;
                                                v___y_3907_ = v___y_3924_;
                                                v___y_3908_ = v___y_3926_;
                                                v___y_3909_ = v___f_3958_;
                                                v___y_3910_ = v___y_3923_;
                                                v___y_3911_ = v___y_3921_;
                                                v___y_3912_ = v_a_3953_;
                                                v___y_3913_ = v___y_3922_;
                                                v___y_3914_ = v___y_3920_;
                                                v___y_3915_ = v___x_3690_;
                                                state = 33;
                                                continue;
                                            }
                                        } else {
                                            v___y_3862_ = v_a_3955_;
                                            v___y_3863_ = v___f_3959_;
                                            v___y_3864_ = v___f_3957_;
                                            v___y_3865_ = v___y_3919_;
                                            v___y_3866_ = v___y_3925_;
                                            v___y_3867_ = v___y_3924_;
                                            v___y_3868_ = v___y_3926_;
                                            v___y_3869_ = v___f_3958_;
                                            v___y_3870_ = v___y_3923_;
                                            v___y_3871_ = v___y_3921_;
                                            v___y_3872_ = v_a_3953_;
                                            v___y_3873_ = v___y_3922_;
                                            v___y_3874_ = v___y_3920_;
                                            v___y_3875_ = v_a_3982_;
                                            state = 31;
                                            continue;
                                        }
                                    } else {
                                        crate::leanh::lean_dec_ref(v___f_3957_);
                                        crate::leanh::lean_dec(v_a_3955_);
                                        crate::leanh::lean_dec(v_a_3953_);
                                        crate::leanh::lean_dec_ref(v___f_3582_);
                                        v_a_3987_ = crate::leanh::lean_ctor_get(v___x_3981_, 0);
                                        v_isSharedCheck_3994_ =
                                            (!crate::leanh::lean_is_exclusive(v___x_3981_)) as u8;
                                        if v_isSharedCheck_3994_ == 0 {
                                            v___x_3989_ = v___x_3981_;
                                            v_isShared_3990_ = v_isSharedCheck_3994_;
                                            state = 37;
                                            continue;
                                        } else {
                                            crate::leanh::lean_inc(v_a_3987_);
                                            crate::leanh::lean_dec(v___x_3981_);
                                            v___x_3989_ = crate::leanh::lean_box(0);
                                            v_isShared_3990_ = v_isSharedCheck_3994_;
                                            state = 37;
                                            continue;
                                        }
                                    }
                                }
                            } else {
                                crate::leanh::lean_dec(v_val_3961_);
                                crate::leanh::lean_dec_ref(v___x_3588_);
                                crate::leanh::lean_dec_ref(v___x_3587_);
                                crate::leanh::lean_dec_ref(v___x_3586_);
                                crate::leanh::lean_dec_ref(v___x_3585_);
                                v___x_3995_ =
                                    l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__26;
                                v___y_3816_ = v_a_3955_;
                                v___y_3817_ = v___f_3958_;
                                v___y_3818_ = v___f_3959_;
                                v___y_3819_ = v___f_3957_;
                                v___y_3820_ = v_a_3953_;
                                v_occs_3821_ = v___x_3995_;
                                v___y_3822_ = v___y_3919_;
                                v___y_3823_ = v___y_3920_;
                                v___y_3824_ = v___y_3921_;
                                v___y_3825_ = v___y_3922_;
                                v___y_3826_ = v___y_3923_;
                                v___y_3827_ = v___y_3924_;
                                v___y_3828_ = v___y_3925_;
                                v___y_3829_ = v___y_3926_;
                                state = 27;
                                continue;
                            }
                        }
                    } else {
                        crate::leanh::lean_dec(v_a_3953_);
                        crate::leanh::lean_dec(v_occs_3918_);
                        crate::leanh::lean_dec_ref(v___x_3588_);
                        crate::leanh::lean_dec_ref(v___x_3587_);
                        crate::leanh::lean_dec_ref(v___x_3586_);
                        crate::leanh::lean_dec_ref(v___x_3585_);
                        crate::leanh::lean_dec_ref(v___f_3582_);
                        v_a_3996_ = crate::leanh::lean_ctor_get(v___x_3954_, 0);
                        v_isSharedCheck_4003_ =
                            (!crate::leanh::lean_is_exclusive(v___x_3954_)) as u8;
                        if v_isSharedCheck_4003_ == 0 {
                            v___x_3998_ = v___x_3954_;
                            v_isShared_3999_ = v_isSharedCheck_4003_;
                            state = 39;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_3996_);
                            crate::leanh::lean_dec(v___x_3954_);
                            v___x_3998_ = crate::leanh::lean_box(0);
                            v_isShared_3999_ = v_isSharedCheck_4003_;
                            state = 39;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec(v_occs_3918_);
                    crate::leanh::lean_dec_ref(v___x_3588_);
                    crate::leanh::lean_dec_ref(v___x_3587_);
                    crate::leanh::lean_dec_ref(v___x_3586_);
                    crate::leanh::lean_dec_ref(v___x_3585_);
                    crate::leanh::lean_dec_ref(v___f_3582_);
                    v_a_4004_ = crate::leanh::lean_ctor_get(v___x_3952_, 0);
                    v_isSharedCheck_4011_ = (!crate::leanh::lean_is_exclusive(v___x_3952_)) as u8;
                    if v_isSharedCheck_4011_ == 0 {
                        v___x_4006_ = v___x_3952_;
                        v_isShared_4007_ = v_isSharedCheck_4011_;
                        state = 41;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4004_);
                        crate::leanh::lean_dec(v___x_3952_);
                        v___x_4006_ = crate::leanh::lean_box(0);
                        v_isShared_4007_ = v_isSharedCheck_4011_;
                        state = 41;
                        continue;
                    }
                }
            }
            35 => {
                if v_isShared_3972_ == 0 {
                    v___x_3974_ = v___x_3971_;
                    state = 36;
                    continue;
                } else {
                    v_reuseFailAlloc_3975_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3975_, 0, v_a_3969_);
                    v___x_3974_ = v_reuseFailAlloc_3975_;
                    state = 36;
                    continue;
                }
            }
            36 => {
                return v___x_3974_;
            }
            37 => {
                if v_isShared_3990_ == 0 {
                    v___x_3992_ = v___x_3989_;
                    state = 38;
                    continue;
                } else {
                    v_reuseFailAlloc_3993_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3993_, 0, v_a_3987_);
                    v___x_3992_ = v_reuseFailAlloc_3993_;
                    state = 38;
                    continue;
                }
            }
            38 => {
                return v___x_3992_;
            }
            39 => {
                if v_isShared_3999_ == 0 {
                    v___x_4001_ = v___x_3998_;
                    state = 40;
                    continue;
                } else {
                    v_reuseFailAlloc_4002_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4002_, 0, v_a_3996_);
                    v___x_4001_ = v_reuseFailAlloc_4002_;
                    state = 40;
                    continue;
                }
            }
            40 => {
                return v___x_4001_;
            }
            41 => {
                if v_isShared_4007_ == 0 {
                    v___x_4009_ = v___x_4006_;
                    state = 42;
                    continue;
                } else {
                    v_reuseFailAlloc_4010_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4010_, 0, v_a_4004_);
                    v___x_4009_ = v_reuseFailAlloc_4010_;
                    state = 42;
                    continue;
                }
            }
            42 => {
                return v___x_4009_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___boxed(
    _args: *mut *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4025_: *mut crate::leanh::LeanObject = *_args.add(0);
    let mut v___f_4026_: *mut crate::leanh::LeanObject = *_args.add(1);
    let mut v___x_4027_: *mut crate::leanh::LeanObject = *_args.add(2);
    let mut v_stx_4028_: *mut crate::leanh::LeanObject = *_args.add(3);
    let mut v___x_4029_: *mut crate::leanh::LeanObject = *_args.add(4);
    let mut v___x_4030_: *mut crate::leanh::LeanObject = *_args.add(5);
    let mut v___x_4031_: *mut crate::leanh::LeanObject = *_args.add(6);
    let mut v___x_4032_: *mut crate::leanh::LeanObject = *_args.add(7);
    let mut v___y_4033_: *mut crate::leanh::LeanObject = *_args.add(8);
    let mut v___y_4034_: *mut crate::leanh::LeanObject = *_args.add(9);
    let mut v___y_4035_: *mut crate::leanh::LeanObject = *_args.add(10);
    let mut v___y_4036_: *mut crate::leanh::LeanObject = *_args.add(11);
    let mut v___y_4037_: *mut crate::leanh::LeanObject = *_args.add(12);
    let mut v___y_4038_: *mut crate::leanh::LeanObject = *_args.add(13);
    let mut v___y_4039_: *mut crate::leanh::LeanObject = *_args.add(14);
    let mut v___y_4040_: *mut crate::leanh::LeanObject = *_args.add(15);
    let mut v___y_4041_: *mut crate::leanh::LeanObject = *_args.add(16);
    let mut v___x_19478__boxed_4042_: u8 = 0;
    let mut v___x_19480__boxed_4043_: u8 = 0;
    let mut v_res_4044_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_19478__boxed_4042_ = (crate::leanh::lean_unbox(v___x_4025_) as u8);
    v___x_19480__boxed_4043_ = (crate::leanh::lean_unbox(v___x_4027_) as u8);
    v_res_4044_ = l_Lean_Elab_Tactic_Conv_evalPattern___lam__6(
        v___x_19478__boxed_4042_,
        v___f_4026_,
        v___x_19480__boxed_4043_,
        v_stx_4028_,
        v___x_4029_,
        v___x_4030_,
        v___x_4031_,
        v___x_4032_,
        v___y_4033_,
        v___y_4034_,
        v___y_4035_,
        v___y_4036_,
        v___y_4037_,
        v___y_4038_,
        v___y_4039_,
        v___y_4040_,
    );
    crate::leanh::lean_dec(v___y_4040_);
    crate::leanh::lean_dec_ref(v___y_4039_);
    crate::leanh::lean_dec(v___y_4038_);
    crate::leanh::lean_dec_ref(v___y_4037_);
    crate::leanh::lean_dec(v___y_4036_);
    crate::leanh::lean_dec_ref(v___y_4035_);
    crate::leanh::lean_dec(v___y_4034_);
    crate::leanh::lean_dec_ref(v___y_4033_);
    crate::leanh::lean_dec(v_stx_4028_);
    return v_res_4044_;
}
pub unsafe fn l_Lean_Elab_Tactic_Conv_evalPattern(
    mut v_stx_4057_: *mut crate::leanh::LeanObject,
    mut v_a_4058_: *mut crate::leanh::LeanObject,
    mut v_a_4059_: *mut crate::leanh::LeanObject,
    mut v_a_4060_: *mut crate::leanh::LeanObject,
    mut v_a_4061_: *mut crate::leanh::LeanObject,
    mut v_a_4062_: *mut crate::leanh::LeanObject,
    mut v_a_4063_: *mut crate::leanh::LeanObject,
    mut v_a_4064_: *mut crate::leanh::LeanObject,
    mut v_a_4065_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_4067_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4068_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4069_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4070_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4071_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4072_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4073_: u8 = 0;
    let mut v___x_4074_: u8 = 0;
    let mut v___x_4075_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4076_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4077_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4078_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_4067_ = l_Lean_Elab_Tactic_Conv_evalPattern___closed__0;
    v___x_4068_ = l_Lean_Elab_Tactic_Conv_evalPattern___closed__1;
    v___x_4069_ = l_Lean_Elab_Tactic_Conv_evalPattern___closed__2;
    v___x_4070_ = l_Lean_Elab_Tactic_Conv_evalPattern___closed__3;
    v___x_4071_ = l_Lean_Elab_Tactic_Conv_evalPattern___closed__4;
    v___x_4072_ = l_Lean_Elab_Tactic_Conv_evalPattern___closed__6;
    crate::leanh::lean_inc(v_stx_4057_);
    v___x_4073_ = l_Lean_Syntax_isOfKind(v_stx_4057_, v___x_4072_);
    v___x_4074_ = 1;
    v___x_4075_ = crate::leanh::lean_box((v___x_4073_) as usize);
    v___x_4076_ = crate::leanh::lean_box((v___x_4074_) as usize);
    v___y_4077_ = crate::leanh::lean_alloc_closure(
        l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___boxed as *mut core::ffi::c_void,
        17,
        8,
    );
    crate::leanh::lean_closure_set(v___y_4077_, 0, v___x_4075_);
    crate::leanh::lean_closure_set(v___y_4077_, 1, v___f_4067_);
    crate::leanh::lean_closure_set(v___y_4077_, 2, v___x_4076_);
    crate::leanh::lean_closure_set(v___y_4077_, 3, v_stx_4057_);
    crate::leanh::lean_closure_set(v___y_4077_, 4, v___x_4068_);
    crate::leanh::lean_closure_set(v___y_4077_, 5, v___x_4069_);
    crate::leanh::lean_closure_set(v___y_4077_, 6, v___x_4070_);
    crate::leanh::lean_closure_set(v___y_4077_, 7, v___x_4071_);
    v___x_4078_ = l_Lean_Elab_Tactic_withMainContext___redArg(
        v___y_4077_,
        v_a_4058_,
        v_a_4059_,
        v_a_4060_,
        v_a_4061_,
        v_a_4062_,
        v_a_4063_,
        v_a_4064_,
        v_a_4065_,
    );
    return v___x_4078_;
}
pub unsafe fn l_Lean_Elab_Tactic_Conv_evalPattern___boxed(
    mut v_stx_4079_: *mut crate::leanh::LeanObject,
    mut v_a_4080_: *mut crate::leanh::LeanObject,
    mut v_a_4081_: *mut crate::leanh::LeanObject,
    mut v_a_4082_: *mut crate::leanh::LeanObject,
    mut v_a_4083_: *mut crate::leanh::LeanObject,
    mut v_a_4084_: *mut crate::leanh::LeanObject,
    mut v_a_4085_: *mut crate::leanh::LeanObject,
    mut v_a_4086_: *mut crate::leanh::LeanObject,
    mut v_a_4087_: *mut crate::leanh::LeanObject,
    mut v_a_4088_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4089_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4089_ = l_Lean_Elab_Tactic_Conv_evalPattern(
        v_stx_4079_,
        v_a_4080_,
        v_a_4081_,
        v_a_4082_,
        v_a_4083_,
        v_a_4084_,
        v_a_4085_,
        v_a_4086_,
        v_a_4087_,
    );
    crate::leanh::lean_dec(v_a_4087_);
    crate::leanh::lean_dec_ref(v_a_4086_);
    crate::leanh::lean_dec(v_a_4085_);
    crate::leanh::lean_dec_ref(v_a_4084_);
    crate::leanh::lean_dec(v_a_4083_);
    crate::leanh::lean_dec_ref(v_a_4082_);
    crate::leanh::lean_dec(v_a_4081_);
    crate::leanh::lean_dec_ref(v_a_4080_);
    return v_res_4089_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__1(
    mut v_00_u03b1_4090_: *mut crate::leanh::LeanObject,
    mut v_ref_4091_: *mut crate::leanh::LeanObject,
    mut v_msg_4092_: *mut crate::leanh::LeanObject,
    mut v___y_4093_: *mut crate::leanh::LeanObject,
    mut v___y_4094_: *mut crate::leanh::LeanObject,
    mut v___y_4095_: *mut crate::leanh::LeanObject,
    mut v___y_4096_: *mut crate::leanh::LeanObject,
    mut v___y_4097_: *mut crate::leanh::LeanObject,
    mut v___y_4098_: *mut crate::leanh::LeanObject,
    mut v___y_4099_: *mut crate::leanh::LeanObject,
    mut v___y_4100_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4102_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4102_ = l_Lean_throwErrorAt___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__1___redArg(
        v_ref_4091_,
        v_msg_4092_,
        v___y_4093_,
        v___y_4094_,
        v___y_4095_,
        v___y_4096_,
        v___y_4097_,
        v___y_4098_,
        v___y_4099_,
        v___y_4100_,
    );
    return v___x_4102_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__1___boxed(
    mut v_00_u03b1_4103_: *mut crate::leanh::LeanObject,
    mut v_ref_4104_: *mut crate::leanh::LeanObject,
    mut v_msg_4105_: *mut crate::leanh::LeanObject,
    mut v___y_4106_: *mut crate::leanh::LeanObject,
    mut v___y_4107_: *mut crate::leanh::LeanObject,
    mut v___y_4108_: *mut crate::leanh::LeanObject,
    mut v___y_4109_: *mut crate::leanh::LeanObject,
    mut v___y_4110_: *mut crate::leanh::LeanObject,
    mut v___y_4111_: *mut crate::leanh::LeanObject,
    mut v___y_4112_: *mut crate::leanh::LeanObject,
    mut v___y_4113_: *mut crate::leanh::LeanObject,
    mut v___y_4114_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4115_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4115_ = l_Lean_throwErrorAt___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__1(
        v_00_u03b1_4103_,
        v_ref_4104_,
        v_msg_4105_,
        v___y_4106_,
        v___y_4107_,
        v___y_4108_,
        v___y_4109_,
        v___y_4110_,
        v___y_4111_,
        v___y_4112_,
        v___y_4113_,
    );
    crate::leanh::lean_dec(v___y_4113_);
    crate::leanh::lean_dec_ref(v___y_4112_);
    crate::leanh::lean_dec(v___y_4111_);
    crate::leanh::lean_dec_ref(v___y_4110_);
    crate::leanh::lean_dec(v___y_4109_);
    crate::leanh::lean_dec_ref(v___y_4108_);
    crate::leanh::lean_dec(v___y_4107_);
    crate::leanh::lean_dec_ref(v___y_4106_);
    crate::leanh::lean_dec(v_ref_4104_);
    return v_res_4115_;
}
pub unsafe fn l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__3(
    mut v_mvarId_4116_: *mut crate::leanh::LeanObject,
    mut v_val_4117_: *mut crate::leanh::LeanObject,
    mut v___y_4118_: *mut crate::leanh::LeanObject,
    mut v___y_4119_: *mut crate::leanh::LeanObject,
    mut v___y_4120_: *mut crate::leanh::LeanObject,
    mut v___y_4121_: *mut crate::leanh::LeanObject,
    mut v___y_4122_: *mut crate::leanh::LeanObject,
    mut v___y_4123_: *mut crate::leanh::LeanObject,
    mut v___y_4124_: *mut crate::leanh::LeanObject,
    mut v___y_4125_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4127_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4127_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__3___redArg(
        v_mvarId_4116_,
        v_val_4117_,
        v___y_4123_,
    );
    return v___x_4127_;
}
pub unsafe fn l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__3___boxed(
    mut v_mvarId_4128_: *mut crate::leanh::LeanObject,
    mut v_val_4129_: *mut crate::leanh::LeanObject,
    mut v___y_4130_: *mut crate::leanh::LeanObject,
    mut v___y_4131_: *mut crate::leanh::LeanObject,
    mut v___y_4132_: *mut crate::leanh::LeanObject,
    mut v___y_4133_: *mut crate::leanh::LeanObject,
    mut v___y_4134_: *mut crate::leanh::LeanObject,
    mut v___y_4135_: *mut crate::leanh::LeanObject,
    mut v___y_4136_: *mut crate::leanh::LeanObject,
    mut v___y_4137_: *mut crate::leanh::LeanObject,
    mut v___y_4138_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4139_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4139_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__3(
        v_mvarId_4128_,
        v_val_4129_,
        v___y_4130_,
        v___y_4131_,
        v___y_4132_,
        v___y_4133_,
        v___y_4134_,
        v___y_4135_,
        v___y_4136_,
        v___y_4137_,
    );
    crate::leanh::lean_dec(v___y_4137_);
    crate::leanh::lean_dec_ref(v___y_4136_);
    crate::leanh::lean_dec(v___y_4135_);
    crate::leanh::lean_dec_ref(v___y_4134_);
    crate::leanh::lean_dec(v___y_4133_);
    crate::leanh::lean_dec_ref(v___y_4132_);
    crate::leanh::lean_dec(v___y_4131_);
    crate::leanh::lean_dec_ref(v___y_4130_);
    return v_res_4139_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__4(
    mut v_00_u03b1_4140_: *mut crate::leanh::LeanObject,
    mut v_msg_4141_: *mut crate::leanh::LeanObject,
    mut v___y_4142_: *mut crate::leanh::LeanObject,
    mut v___y_4143_: *mut crate::leanh::LeanObject,
    mut v___y_4144_: *mut crate::leanh::LeanObject,
    mut v___y_4145_: *mut crate::leanh::LeanObject,
    mut v___y_4146_: *mut crate::leanh::LeanObject,
    mut v___y_4147_: *mut crate::leanh::LeanObject,
    mut v___y_4148_: *mut crate::leanh::LeanObject,
    mut v___y_4149_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4151_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4151_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__4___redArg(
        v_msg_4141_,
        v___y_4146_,
        v___y_4147_,
        v___y_4148_,
        v___y_4149_,
    );
    return v___x_4151_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__4___boxed(
    mut v_00_u03b1_4152_: *mut crate::leanh::LeanObject,
    mut v_msg_4153_: *mut crate::leanh::LeanObject,
    mut v___y_4154_: *mut crate::leanh::LeanObject,
    mut v___y_4155_: *mut crate::leanh::LeanObject,
    mut v___y_4156_: *mut crate::leanh::LeanObject,
    mut v___y_4157_: *mut crate::leanh::LeanObject,
    mut v___y_4158_: *mut crate::leanh::LeanObject,
    mut v___y_4159_: *mut crate::leanh::LeanObject,
    mut v___y_4160_: *mut crate::leanh::LeanObject,
    mut v___y_4161_: *mut crate::leanh::LeanObject,
    mut v___y_4162_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4163_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4163_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__4(
        v_00_u03b1_4152_,
        v_msg_4153_,
        v___y_4154_,
        v___y_4155_,
        v___y_4156_,
        v___y_4157_,
        v___y_4158_,
        v___y_4159_,
        v___y_4160_,
        v___y_4161_,
    );
    crate::leanh::lean_dec(v___y_4161_);
    crate::leanh::lean_dec_ref(v___y_4160_);
    crate::leanh::lean_dec(v___y_4159_);
    crate::leanh::lean_dec_ref(v___y_4158_);
    crate::leanh::lean_dec(v___y_4157_);
    crate::leanh::lean_dec_ref(v___y_4156_);
    crate::leanh::lean_dec(v___y_4155_);
    crate::leanh::lean_dec_ref(v___y_4154_);
    return v_res_4163_;
}
pub unsafe fn l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__6(
    mut v_n_4164_: *mut crate::leanh::LeanObject,
    mut v_as_4165_: *mut crate::leanh::LeanObject,
    mut v_lo_4166_: *mut crate::leanh::LeanObject,
    mut v_hi_4167_: *mut crate::leanh::LeanObject,
    mut v_w_4168_: *mut crate::leanh::LeanObject,
    mut v_hlo_4169_: *mut crate::leanh::LeanObject,
    mut v_hhi_4170_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4171_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4171_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__6___redArg(v_n_4164_, v_as_4165_, v_lo_4166_, v_hi_4167_);
    return v___x_4171_;
}
pub unsafe fn l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__6___boxed(
    mut v_n_4172_: *mut crate::leanh::LeanObject,
    mut v_as_4173_: *mut crate::leanh::LeanObject,
    mut v_lo_4174_: *mut crate::leanh::LeanObject,
    mut v_hi_4175_: *mut crate::leanh::LeanObject,
    mut v_w_4176_: *mut crate::leanh::LeanObject,
    mut v_hlo_4177_: *mut crate::leanh::LeanObject,
    mut v_hhi_4178_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4179_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4179_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__6(v_n_4172_, v_as_4173_, v_lo_4174_, v_hi_4175_, v_w_4176_, v_hlo_4177_, v_hhi_4178_);
    crate::leanh::lean_dec(v_hi_4175_);
    crate::leanh::lean_dec(v_n_4172_);
    return v_res_4179_;
}
pub unsafe fn l_Array_mapFinIdxM_map___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__7(
    mut v_as_4180_: *mut crate::leanh::LeanObject,
    mut v_i_4181_: *mut crate::leanh::LeanObject,
    mut v_j_4182_: *mut crate::leanh::LeanObject,
    mut v_inv_4183_: *mut crate::leanh::LeanObject,
    mut v_bs_4184_: *mut crate::leanh::LeanObject,
    mut v___y_4185_: *mut crate::leanh::LeanObject,
    mut v___y_4186_: *mut crate::leanh::LeanObject,
    mut v___y_4187_: *mut crate::leanh::LeanObject,
    mut v___y_4188_: *mut crate::leanh::LeanObject,
    mut v___y_4189_: *mut crate::leanh::LeanObject,
    mut v___y_4190_: *mut crate::leanh::LeanObject,
    mut v___y_4191_: *mut crate::leanh::LeanObject,
    mut v___y_4192_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4194_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4194_ =
        l_Array_mapFinIdxM_map___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__7___redArg(
            v_as_4180_,
            v_i_4181_,
            v_j_4182_,
            v_bs_4184_,
            v___y_4185_,
            v___y_4186_,
            v___y_4187_,
            v___y_4188_,
            v___y_4189_,
            v___y_4190_,
            v___y_4191_,
            v___y_4192_,
        );
    return v___x_4194_;
}
pub unsafe fn l_Array_mapFinIdxM_map___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__7___boxed(
    mut v_as_4195_: *mut crate::leanh::LeanObject,
    mut v_i_4196_: *mut crate::leanh::LeanObject,
    mut v_j_4197_: *mut crate::leanh::LeanObject,
    mut v_inv_4198_: *mut crate::leanh::LeanObject,
    mut v_bs_4199_: *mut crate::leanh::LeanObject,
    mut v___y_4200_: *mut crate::leanh::LeanObject,
    mut v___y_4201_: *mut crate::leanh::LeanObject,
    mut v___y_4202_: *mut crate::leanh::LeanObject,
    mut v___y_4203_: *mut crate::leanh::LeanObject,
    mut v___y_4204_: *mut crate::leanh::LeanObject,
    mut v___y_4205_: *mut crate::leanh::LeanObject,
    mut v___y_4206_: *mut crate::leanh::LeanObject,
    mut v___y_4207_: *mut crate::leanh::LeanObject,
    mut v___y_4208_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4209_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4209_ = l_Array_mapFinIdxM_map___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__7(
        v_as_4195_,
        v_i_4196_,
        v_j_4197_,
        v_inv_4198_,
        v_bs_4199_,
        v___y_4200_,
        v___y_4201_,
        v___y_4202_,
        v___y_4203_,
        v___y_4204_,
        v___y_4205_,
        v___y_4206_,
        v___y_4207_,
    );
    crate::leanh::lean_dec(v___y_4207_);
    crate::leanh::lean_dec_ref(v___y_4206_);
    crate::leanh::lean_dec(v___y_4205_);
    crate::leanh::lean_dec_ref(v___y_4204_);
    crate::leanh::lean_dec(v___y_4203_);
    crate::leanh::lean_dec_ref(v___y_4202_);
    crate::leanh::lean_dec(v___y_4201_);
    crate::leanh::lean_dec_ref(v___y_4200_);
    crate::leanh::lean_dec_ref(v_as_4195_);
    return v_res_4209_;
}
pub unsafe fn l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__9(
    mut v_n_4210_: *mut crate::leanh::LeanObject,
    mut v_as_4211_: *mut crate::leanh::LeanObject,
    mut v_lo_4212_: *mut crate::leanh::LeanObject,
    mut v_hi_4213_: *mut crate::leanh::LeanObject,
    mut v_w_4214_: *mut crate::leanh::LeanObject,
    mut v_hlo_4215_: *mut crate::leanh::LeanObject,
    mut v_hhi_4216_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4217_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4217_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__9___redArg(v_n_4210_, v_as_4211_, v_lo_4212_, v_hi_4213_);
    return v___x_4217_;
}
pub unsafe fn l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__9___boxed(
    mut v_n_4218_: *mut crate::leanh::LeanObject,
    mut v_as_4219_: *mut crate::leanh::LeanObject,
    mut v_lo_4220_: *mut crate::leanh::LeanObject,
    mut v_hi_4221_: *mut crate::leanh::LeanObject,
    mut v_w_4222_: *mut crate::leanh::LeanObject,
    mut v_hlo_4223_: *mut crate::leanh::LeanObject,
    mut v_hhi_4224_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4225_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4225_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__9(v_n_4218_, v_as_4219_, v_lo_4220_, v_hi_4221_, v_w_4222_, v_hlo_4223_, v_hhi_4224_);
    crate::leanh::lean_dec(v_hi_4221_);
    crate::leanh::lean_dec(v_n_4218_);
    return v_res_4225_;
}
pub unsafe fn l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__3_spec__3(
    mut v_00_u03b2_4226_: *mut crate::leanh::LeanObject,
    mut v_x_4227_: *mut crate::leanh::LeanObject,
    mut v_x_4228_: *mut crate::leanh::LeanObject,
    mut v_x_4229_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4230_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4230_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__3_spec__3___redArg(v_x_4227_, v_x_4228_, v_x_4229_);
    return v___x_4230_;
}
pub unsafe fn l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__6_spec__8(
    mut v_n_4231_: *mut crate::leanh::LeanObject,
    mut v_lo_4232_: *mut crate::leanh::LeanObject,
    mut v_hi_4233_: *mut crate::leanh::LeanObject,
    mut v_hhi_4234_: *mut crate::leanh::LeanObject,
    mut v_pivot_4235_: *mut crate::leanh::LeanObject,
    mut v_as_4236_: *mut crate::leanh::LeanObject,
    mut v_i_4237_: *mut crate::leanh::LeanObject,
    mut v_k_4238_: *mut crate::leanh::LeanObject,
    mut v_ilo_4239_: *mut crate::leanh::LeanObject,
    mut v_ik_4240_: *mut crate::leanh::LeanObject,
    mut v_w_4241_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4242_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4242_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__6_spec__8___redArg(v_hi_4233_, v_pivot_4235_, v_as_4236_, v_i_4237_, v_k_4238_);
    return v___x_4242_;
}
pub unsafe fn l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__6_spec__8___boxed(
    mut v_n_4243_: *mut crate::leanh::LeanObject,
    mut v_lo_4244_: *mut crate::leanh::LeanObject,
    mut v_hi_4245_: *mut crate::leanh::LeanObject,
    mut v_hhi_4246_: *mut crate::leanh::LeanObject,
    mut v_pivot_4247_: *mut crate::leanh::LeanObject,
    mut v_as_4248_: *mut crate::leanh::LeanObject,
    mut v_i_4249_: *mut crate::leanh::LeanObject,
    mut v_k_4250_: *mut crate::leanh::LeanObject,
    mut v_ilo_4251_: *mut crate::leanh::LeanObject,
    mut v_ik_4252_: *mut crate::leanh::LeanObject,
    mut v_w_4253_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4254_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4254_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__6_spec__8(v_n_4243_, v_lo_4244_, v_hi_4245_, v_hhi_4246_, v_pivot_4247_, v_as_4248_, v_i_4249_, v_k_4250_, v_ilo_4251_, v_ik_4252_, v_w_4253_);
    crate::leanh::lean_dec_ref(v_pivot_4247_);
    crate::leanh::lean_dec(v_hi_4245_);
    crate::leanh::lean_dec(v_lo_4244_);
    crate::leanh::lean_dec(v_n_4243_);
    return v_res_4254_;
}
pub unsafe fn l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__9_spec__13(
    mut v_n_4255_: *mut crate::leanh::LeanObject,
    mut v_lo_4256_: *mut crate::leanh::LeanObject,
    mut v_hi_4257_: *mut crate::leanh::LeanObject,
    mut v_hhi_4258_: *mut crate::leanh::LeanObject,
    mut v_pivot_4259_: *mut crate::leanh::LeanObject,
    mut v_as_4260_: *mut crate::leanh::LeanObject,
    mut v_i_4261_: *mut crate::leanh::LeanObject,
    mut v_k_4262_: *mut crate::leanh::LeanObject,
    mut v_ilo_4263_: *mut crate::leanh::LeanObject,
    mut v_ik_4264_: *mut crate::leanh::LeanObject,
    mut v_w_4265_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4266_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4266_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__9_spec__13___redArg(v_hi_4257_, v_pivot_4259_, v_as_4260_, v_i_4261_, v_k_4262_);
    return v___x_4266_;
}
pub unsafe fn l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__9_spec__13___boxed(
    mut v_n_4267_: *mut crate::leanh::LeanObject,
    mut v_lo_4268_: *mut crate::leanh::LeanObject,
    mut v_hi_4269_: *mut crate::leanh::LeanObject,
    mut v_hhi_4270_: *mut crate::leanh::LeanObject,
    mut v_pivot_4271_: *mut crate::leanh::LeanObject,
    mut v_as_4272_: *mut crate::leanh::LeanObject,
    mut v_i_4273_: *mut crate::leanh::LeanObject,
    mut v_k_4274_: *mut crate::leanh::LeanObject,
    mut v_ilo_4275_: *mut crate::leanh::LeanObject,
    mut v_ik_4276_: *mut crate::leanh::LeanObject,
    mut v_w_4277_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4278_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4278_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__9_spec__13(v_n_4267_, v_lo_4268_, v_hi_4269_, v_hhi_4270_, v_pivot_4271_, v_as_4272_, v_i_4273_, v_k_4274_, v_ilo_4275_, v_ik_4276_, v_w_4277_);
    crate::leanh::lean_dec_ref(v_pivot_4271_);
    crate::leanh::lean_dec(v_hi_4269_);
    crate::leanh::lean_dec(v_lo_4268_);
    crate::leanh::lean_dec(v_n_4267_);
    return v_res_4278_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__3_spec__3_spec__4(
    mut v_00_u03b2_4279_: *mut crate::leanh::LeanObject,
    mut v_x_4280_: *mut crate::leanh::LeanObject,
    mut v_x_4281_: usize,
    mut v_x_4282_: usize,
    mut v_x_4283_: *mut crate::leanh::LeanObject,
    mut v_x_4284_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4285_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4285_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__3_spec__3_spec__4___redArg(v_x_4280_, v_x_4281_, v_x_4282_, v_x_4283_, v_x_4284_);
    return v___x_4285_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__3_spec__3_spec__4___boxed(
    mut v_00_u03b2_4286_: *mut crate::leanh::LeanObject,
    mut v_x_4287_: *mut crate::leanh::LeanObject,
    mut v_x_4288_: *mut crate::leanh::LeanObject,
    mut v_x_4289_: *mut crate::leanh::LeanObject,
    mut v_x_4290_: *mut crate::leanh::LeanObject,
    mut v_x_4291_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_20596__boxed_4292_: usize = 0;
    let mut v_x_20597__boxed_4293_: usize = 0;
    let mut v_res_4294_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_20596__boxed_4292_ = crate::leanh::lean_unbox_usize(v_x_4288_);
    crate::leanh::lean_dec(v_x_4288_);
    v_x_20597__boxed_4293_ = crate::leanh::lean_unbox_usize(v_x_4289_);
    crate::leanh::lean_dec(v_x_4289_);
    v_res_4294_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__3_spec__3_spec__4(v_00_u03b2_4286_, v_x_4287_, v_x_20596__boxed_4292_, v_x_20597__boxed_4293_, v_x_4290_, v_x_4291_);
    return v_res_4294_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_allDiffAuxAux___at___00__private_Init_Data_Array_Basic_0__Array_allDiffAux___at___00Array_allDiff___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__8_spec__11_spec__13(
    mut v_as_4295_: *mut crate::leanh::LeanObject,
    mut v_a_4296_: *mut crate::leanh::LeanObject,
    mut v_x_4297_: *mut crate::leanh::LeanObject,
    mut v_x_4298_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_4299_: u8 = 0;
    v___x_4299_ = l___private_Init_Data_Array_Basic_0__Array_allDiffAuxAux___at___00__private_Init_Data_Array_Basic_0__Array_allDiffAux___at___00Array_allDiff___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__8_spec__11_spec__13___redArg(v_as_4295_, v_a_4296_, v_x_4297_);
    return v___x_4299_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_allDiffAuxAux___at___00__private_Init_Data_Array_Basic_0__Array_allDiffAux___at___00Array_allDiff___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__8_spec__11_spec__13___boxed(
    mut v_as_4300_: *mut crate::leanh::LeanObject,
    mut v_a_4301_: *mut crate::leanh::LeanObject,
    mut v_x_4302_: *mut crate::leanh::LeanObject,
    mut v_x_4303_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4304_: u8 = 0;
    let mut v_r_4305_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4304_ = l___private_Init_Data_Array_Basic_0__Array_allDiffAuxAux___at___00__private_Init_Data_Array_Basic_0__Array_allDiffAux___at___00Array_allDiff___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__8_spec__11_spec__13(v_as_4300_, v_a_4301_, v_x_4302_, v_x_4303_);
    crate::leanh::lean_dec_ref(v_a_4301_);
    crate::leanh::lean_dec_ref(v_as_4300_);
    v_r_4305_ = crate::leanh::lean_box((v_res_4304_) as usize);
    return v_r_4305_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__3_spec__3_spec__4_spec__12(
    mut v_00_u03b2_4306_: *mut crate::leanh::LeanObject,
    mut v_n_4307_: *mut crate::leanh::LeanObject,
    mut v_k_4308_: *mut crate::leanh::LeanObject,
    mut v_v_4309_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4310_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4310_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__3_spec__3_spec__4_spec__12___redArg(v_n_4307_, v_k_4308_, v_v_4309_);
    return v___x_4310_;
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__3_spec__3_spec__4_spec__13(
    mut v_00_u03b2_4311_: *mut crate::leanh::LeanObject,
    mut v_depth_4312_: usize,
    mut v_keys_4313_: *mut crate::leanh::LeanObject,
    mut v_vals_4314_: *mut crate::leanh::LeanObject,
    mut v_heq_4315_: *mut crate::leanh::LeanObject,
    mut v_i_4316_: *mut crate::leanh::LeanObject,
    mut v_entries_4317_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4318_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4318_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__3_spec__3_spec__4_spec__13___redArg(v_depth_4312_, v_keys_4313_, v_vals_4314_, v_i_4316_, v_entries_4317_);
    return v___x_4318_;
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__3_spec__3_spec__4_spec__13___boxed(
    mut v_00_u03b2_4319_: *mut crate::leanh::LeanObject,
    mut v_depth_4320_: *mut crate::leanh::LeanObject,
    mut v_keys_4321_: *mut crate::leanh::LeanObject,
    mut v_vals_4322_: *mut crate::leanh::LeanObject,
    mut v_heq_4323_: *mut crate::leanh::LeanObject,
    mut v_i_4324_: *mut crate::leanh::LeanObject,
    mut v_entries_4325_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_depth_boxed_4326_: usize = 0;
    let mut v_res_4327_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_depth_boxed_4326_ = crate::leanh::lean_unbox_usize(v_depth_4320_);
    crate::leanh::lean_dec(v_depth_4320_);
    v_res_4327_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__3_spec__3_spec__4_spec__13(v_00_u03b2_4319_, v_depth_boxed_4326_, v_keys_4321_, v_vals_4322_, v_heq_4323_, v_i_4324_, v_entries_4325_);
    crate::leanh::lean_dec_ref(v_vals_4322_);
    crate::leanh::lean_dec_ref(v_keys_4321_);
    return v_res_4327_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__3_spec__3_spec__4_spec__12_spec__16(
    mut v_00_u03b2_4328_: *mut crate::leanh::LeanObject,
    mut v_x_4329_: *mut crate::leanh::LeanObject,
    mut v_x_4330_: *mut crate::leanh::LeanObject,
    mut v_x_4331_: *mut crate::leanh::LeanObject,
    mut v_x_4332_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4333_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4333_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__3_spec__3_spec__4_spec__12_spec__16___redArg(v_x_4329_, v_x_4330_, v_x_4331_, v_x_4332_);
    return v___x_4333_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Conv_Pattern_0__Lean_Elab_Tactic_Conv_evalPattern___regBuiltin_Lean_Elab_Tactic_Conv_evalPattern__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4343_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4344_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4345_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4346_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4347_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4343_ = l_Lean_Elab_Tactic_tacticElabAttribute;
    v___x_4344_ = l_Lean_Elab_Tactic_Conv_evalPattern___closed__6;
    v___x_4345_ = l___private_Lean_Elab_Tactic_Conv_Pattern_0__Lean_Elab_Tactic_Conv_evalPattern___regBuiltin_Lean_Elab_Tactic_Conv_evalPattern__1___closed__2;
    v___x_4346_ = crate::leanh::lean_alloc_closure(
        l_Lean_Elab_Tactic_Conv_evalPattern___boxed as *mut core::ffi::c_void,
        10,
        0,
    );
    v___x_4347_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(
        v___x_4343_,
        v___x_4344_,
        v___x_4345_,
        v___x_4346_,
    );
    return v___x_4347_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Conv_Pattern_0__Lean_Elab_Tactic_Conv_evalPattern___regBuiltin_Lean_Elab_Tactic_Conv_evalPattern__1___boxed(
    mut v_a_4348_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4349_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4349_ = l___private_Lean_Elab_Tactic_Conv_Pattern_0__Lean_Elab_Tactic_Conv_evalPattern___regBuiltin_Lean_Elab_Tactic_Conv_evalPattern__1();
    return v_res_4349_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Conv_Pattern_0__Lean_Elab_Tactic_Conv_evalPattern___regBuiltin_Lean_Elab_Tactic_Conv_evalPattern_declRange__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4376_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4377_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4378_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4376_ = l___private_Lean_Elab_Tactic_Conv_Pattern_0__Lean_Elab_Tactic_Conv_evalPattern___regBuiltin_Lean_Elab_Tactic_Conv_evalPattern__1___closed__2;
    v___x_4377_ = l___private_Lean_Elab_Tactic_Conv_Pattern_0__Lean_Elab_Tactic_Conv_evalPattern___regBuiltin_Lean_Elab_Tactic_Conv_evalPattern_declRange__3___closed__6;
    v___x_4378_ = l_Lean_addBuiltinDeclarationRanges(v___x_4376_, v___x_4377_);
    return v___x_4378_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Conv_Pattern_0__Lean_Elab_Tactic_Conv_evalPattern___regBuiltin_Lean_Elab_Tactic_Conv_evalPattern_declRange__3___boxed(
    mut v_a_4379_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4380_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4380_ = l___private_Lean_Elab_Tactic_Conv_Pattern_0__Lean_Elab_Tactic_Conv_evalPattern___regBuiltin_Lean_Elab_Tactic_Conv_evalPattern_declRange__3();
    return v_res_4380_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Elab_Tactic_Conv_Pattern(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Elab_Tactic_Simp(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_Tactic_Conv_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = l___private_Lean_Elab_Tactic_Conv_Pattern_0__Lean_Elab_Tactic_Conv_evalPattern___regBuiltin_Lean_Elab_Tactic_Conv_evalPattern__1();
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = l___private_Lean_Elab_Tactic_Conv_Pattern_0__Lean_Elab_Tactic_Conv_evalPattern___regBuiltin_Lean_Elab_Tactic_Conv_evalPattern_declRange__3();
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Elab_Tactic_Conv_Pattern(
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
pub unsafe fn initialize_Lean_Elab_Tactic_Conv_Pattern(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Elab_Tactic_Simp(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Elab_Tactic_Conv_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_Tactic_Conv_Pattern(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Elab_Tactic_Conv_Pattern(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Lean_Elab_Tactic_Conv_Pattern(builtin);
}
