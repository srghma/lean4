// Lean compiler output
// Module: Lean.Elab.Tactic.Conv.Pattern
// Imports: Lean.Elab.Tactic.Simp Lean.Elab.Tactic.Conv.Basic
use crate::ffi::{
    lean_array_fget, lean_array_fget_borrowed, lean_array_fset, lean_array_fswap,
    lean_array_get_size, lean_array_push, lean_array_size, lean_array_to_list,
    lean_array_uget_borrowed, lean_array_uset, lean_mk_empty_array_with_capacity, lean_nat_add,
    lean_nat_dec_eq, lean_nat_dec_le, lean_nat_dec_lt, lean_nat_shiftr, lean_nat_sub,
    lean_st_mk_ref, lean_st_ref_get, lean_st_ref_set, lean_st_ref_take, lean_uint64_lor,
    lean_uint64_shift_left, lean_uint64_shift_right, lean_uint64_to_usize, lean_usize_add,
    lean_usize_dec_le, lean_usize_dec_lt, lean_usize_land, lean_usize_mul, lean_usize_shift_left,
    lean_usize_shift_right, lean_usize_sub, lean_usize_to_nat,
};
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
pub static l___private_Lean_Elab_Tactic_Conv_Pattern_0__Lean_Elab_Tactic_Conv_getContext___redArg___closed__0_value: leanh::LeanArrayObject<0> = leanh::LeanArrayObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut leanh::LeanObject>()*0) as u16, other: 0, tag: 246 }, m_size: 0, m_capacity: 0, m_data: [] };
static mut l___private_Lean_Elab_Tactic_Conv_Pattern_0__Lean_Elab_Tactic_Conv_getContext___redArg___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Pattern_0__Lean_Elab_Tactic_Conv_getContext___redArg___closed__0_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Conv_Pattern_0__Lean_Elab_Tactic_Conv_matchPattern_x3f_go_x3f___closed__0_value: leanh::LeanArrayObject<0> = leanh::LeanArrayObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut leanh::LeanObject>()*0) as u16, other: 0, tag: 246 }, m_size: 0, m_capacity: 0, m_data: [] };
static mut l___private_Lean_Elab_Tactic_Conv_Pattern_0__Lean_Elab_Tactic_Conv_matchPattern_x3f_go_x3f___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Pattern_0__Lean_Elab_Tactic_Conv_matchPattern_x3f_go_x3f___closed__0_value) as *mut leanh::LeanObject;
static mut l_Lean_Elab_Tactic_Conv_matchPattern_x3f___lam__0___closed__0_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_Tactic_Conv_matchPattern_x3f___lam__0___closed__0: u64 = 0;
pub static l___private_Lean_Elab_Tactic_Conv_Pattern_0__Lean_Elab_Tactic_Conv_pre___closed__0_value: leanh::LeanCtorObject<1> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 2 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_Conv_Pattern_0__Lean_Elab_Tactic_Conv_pre___closed__0:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Elab_Tactic_Conv_Pattern_0__Lean_Elab_Tactic_Conv_pre___closed__0_value
) as *mut leanh::LeanObject;
static mut l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__0___redArg___closed__0_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__0___redArg___closed__0: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__3_spec__3_spec__4___redArg___closed__0_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__3_spec__3_spec__4___redArg___closed__0: usize = 0;
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__3_spec__3_spec__4___redArg___closed__1_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__3_spec__3_spec__4___redArg___closed__1: usize = 0;
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__3_spec__3_spec__4___redArg___closed__2_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__3_spec__3_spec__4___redArg___closed__2: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Array_mapFinIdxM_map___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__7___redArg___closed__0_value: leanh::LeanStringObject<26> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 26, m_capacity: 26, m_length: 25, m_data: [112, 111, 115, 105, 116, 105, 118, 101, 32, 105, 110, 116, 101, 103, 101, 114, 32, 101, 120, 112, 101, 99, 116, 101, 100, 0]};
static mut l_Array_mapFinIdxM_map___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__7___redArg___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l_Array_mapFinIdxM_map___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__7___redArg___closed__0_value) as *mut leanh::LeanObject;
static mut l_Array_mapFinIdxM_map___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__7___redArg___closed__1_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Array_mapFinIdxM_map___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__7___redArg___closed__1: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__0_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__0: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__1_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__1: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__2_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__2: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__3_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__3: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__4_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__4: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__5_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__5: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__6_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__6: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__7_value:
    leanh::LeanStringObject<52> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
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
static mut l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__7: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__7_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__8_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__8: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__9_value:
    leanh::LeanStringObject<54> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
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
static mut l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__9: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__9_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__10_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__10:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__11_value:
    leanh::LeanStringObject<12> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
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
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__11_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__12_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__12:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__13_value:
    leanh::LeanStringObject<10> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
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
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__13_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__14_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__14:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__15_value:
    leanh::LeanArrayObject<0> = leanh::LeanArrayObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<usize>() * 2
            + core::mem::size_of::<*mut leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 246,
    },
    m_size: 0,
    m_capacity: 0,
    m_data: [],
};
static mut l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__15:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__15_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__16_value:
    leanh::LeanStringObject<32> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
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
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__16_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__17_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__17:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__18_value:
    leanh::LeanClosureObject<1> = leanh::LeanClosureObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_Elab_Tactic_Conv_evalPattern___lam__4___boxed as *const core::ffi::c_void,
    m_arity: 10,
    m_num_fixed: 1,
    m_objs: [(((0 as usize) << 1) | 1) as *mut leanh::LeanObject],
};
static mut l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__18:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__18_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__19_value:
    leanh::LeanClosureObject<1> = leanh::LeanClosureObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_Elab_Tactic_Conv_evalPattern___lam__5___boxed as *const core::ffi::c_void,
    m_arity: 10,
    m_num_fixed: 1,
    m_objs: [(((0 as usize) << 1) | 1) as *mut leanh::LeanObject],
};
static mut l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__19:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__19_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__20_value:
    leanh::LeanCtorObject<2> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 0,
    },
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
        (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__20:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__20_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__21_value:
    leanh::LeanCtorObject<2> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__20_value)
            as *mut leanh::LeanObject,
        (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__21:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__21_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__22_value:
    leanh::LeanCtorObject<3> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__15_value)
            as *mut leanh::LeanObject,
        (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__21_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__22:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__22_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__23_value:
    leanh::LeanStringObject<13> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
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
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__23_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__24_value:
    leanh::LeanStringObject<12> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
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
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__24_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__25_value:
    leanh::LeanArrayObject<0> = leanh::LeanArrayObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<usize>() * 2
            + core::mem::size_of::<*mut leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 246,
    },
    m_size: 0,
    m_capacity: 0,
    m_data: [],
};
static mut l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__25:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__25_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__26_value:
    leanh::LeanCtorObject<1> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 0,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__25_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__26:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__26_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__27_value:
    leanh::LeanStringObject<5> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
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
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__27_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_Tactic_Conv_evalPattern___closed__0_value: leanh::LeanClosureObject<
    0,
> = leanh::LeanClosureObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_Elab_Tactic_Conv_evalPattern___lam__0___boxed as *const core::ffi::c_void,
    m_arity: 9,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Elab_Tactic_Conv_evalPattern___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Conv_evalPattern___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_Tactic_Conv_evalPattern___closed__1_value: leanh::LeanStringObject<
    5,
> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
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
static mut l_Lean_Elab_Tactic_Conv_evalPattern___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Conv_evalPattern___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_Tactic_Conv_evalPattern___closed__2_value: leanh::LeanStringObject<
    7,
> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
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
static mut l_Lean_Elab_Tactic_Conv_evalPattern___closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Conv_evalPattern___closed__2_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_Tactic_Conv_evalPattern___closed__3_value: leanh::LeanStringObject<
    7,
> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
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
static mut l_Lean_Elab_Tactic_Conv_evalPattern___closed__3: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Conv_evalPattern___closed__3_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_Tactic_Conv_evalPattern___closed__4_value: leanh::LeanStringObject<
    5,
> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
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
static mut l_Lean_Elab_Tactic_Conv_evalPattern___closed__4: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Conv_evalPattern___closed__4_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_Tactic_Conv_evalPattern___closed__5_value: leanh::LeanStringObject<
    8,
> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
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
static mut l_Lean_Elab_Tactic_Conv_evalPattern___closed__5: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Conv_evalPattern___closed__5_value)
        as *mut leanh::LeanObject;
static l_Lean_Elab_Tactic_Conv_evalPattern___closed__6_value_aux_0: leanh::LeanCtorObject<
    3,
> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Conv_evalPattern___closed__1_value)
            as *mut leanh::LeanObject,
        11948124481539785030 as *mut leanh::LeanObject,
    ],
};
static l_Lean_Elab_Tactic_Conv_evalPattern___closed__6_value_aux_1: leanh::LeanCtorObject<
    3,
> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Conv_evalPattern___closed__6_value_aux_0)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Conv_evalPattern___closed__2_value)
            as *mut leanh::LeanObject,
        8018486133748762727 as *mut leanh::LeanObject,
    ],
};
static l_Lean_Elab_Tactic_Conv_evalPattern___closed__6_value_aux_2: leanh::LeanCtorObject<
    3,
> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Conv_evalPattern___closed__6_value_aux_1)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Conv_evalPattern___closed__3_value)
            as *mut leanh::LeanObject,
        18344149449936419494 as *mut leanh::LeanObject,
    ],
};
static l_Lean_Elab_Tactic_Conv_evalPattern___closed__6_value_aux_3: leanh::LeanCtorObject<
    3,
> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Conv_evalPattern___closed__6_value_aux_2)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Conv_evalPattern___closed__4_value)
            as *mut leanh::LeanObject,
        2622230176999461939 as *mut leanh::LeanObject,
    ],
};
pub static l_Lean_Elab_Tactic_Conv_evalPattern___closed__6_value: leanh::LeanCtorObject<3> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Elab_Tactic_Conv_evalPattern___closed__6_value_aux_3)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Tactic_Conv_evalPattern___closed__5_value)
                as *mut leanh::LeanObject,
            3861856325106436923 as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_Elab_Tactic_Conv_evalPattern___closed__6: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Conv_evalPattern___closed__6_value)
        as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Conv_Pattern_0__Lean_Elab_Tactic_Conv_evalPattern___regBuiltin_Lean_Elab_Tactic_Conv_evalPattern__1___closed__0_value: leanh::LeanStringObject<5> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [69, 108, 97, 98, 0]};
static mut l___private_Lean_Elab_Tactic_Conv_Pattern_0__Lean_Elab_Tactic_Conv_evalPattern___regBuiltin_Lean_Elab_Tactic_Conv_evalPattern__1___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Pattern_0__Lean_Elab_Tactic_Conv_evalPattern___regBuiltin_Lean_Elab_Tactic_Conv_evalPattern__1___closed__0_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Conv_Pattern_0__Lean_Elab_Tactic_Conv_evalPattern___regBuiltin_Lean_Elab_Tactic_Conv_evalPattern__1___closed__1_value: leanh::LeanStringObject<12> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 12, m_capacity: 12, m_length: 11, m_data: [101, 118, 97, 108, 80, 97, 116, 116, 101, 114, 110, 0]};
static mut l___private_Lean_Elab_Tactic_Conv_Pattern_0__Lean_Elab_Tactic_Conv_evalPattern___regBuiltin_Lean_Elab_Tactic_Conv_evalPattern__1___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Pattern_0__Lean_Elab_Tactic_Conv_evalPattern___regBuiltin_Lean_Elab_Tactic_Conv_evalPattern__1___closed__1_value) as *mut leanh::LeanObject;
static l___private_Lean_Elab_Tactic_Conv_Pattern_0__Lean_Elab_Tactic_Conv_evalPattern___regBuiltin_Lean_Elab_Tactic_Conv_evalPattern__1___closed__2_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Elab_Tactic_Conv_evalPattern___closed__1_value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l___private_Lean_Elab_Tactic_Conv_Pattern_0__Lean_Elab_Tactic_Conv_evalPattern___regBuiltin_Lean_Elab_Tactic_Conv_evalPattern__1___closed__2_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Pattern_0__Lean_Elab_Tactic_Conv_evalPattern___regBuiltin_Lean_Elab_Tactic_Conv_evalPattern__1___closed__2_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Pattern_0__Lean_Elab_Tactic_Conv_evalPattern___regBuiltin_Lean_Elab_Tactic_Conv_evalPattern__1___closed__0_value) as *mut leanh::LeanObject,11510100434945111860 as *mut leanh::LeanObject] };
static l___private_Lean_Elab_Tactic_Conv_Pattern_0__Lean_Elab_Tactic_Conv_evalPattern___regBuiltin_Lean_Elab_Tactic_Conv_evalPattern__1___closed__2_value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Pattern_0__Lean_Elab_Tactic_Conv_evalPattern___regBuiltin_Lean_Elab_Tactic_Conv_evalPattern__1___closed__2_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Elab_Tactic_Conv_evalPattern___closed__3_value) as *mut leanh::LeanObject,12733524109236233889 as *mut leanh::LeanObject] };
static l___private_Lean_Elab_Tactic_Conv_Pattern_0__Lean_Elab_Tactic_Conv_evalPattern___regBuiltin_Lean_Elab_Tactic_Conv_evalPattern__1___closed__2_value_aux_3: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Pattern_0__Lean_Elab_Tactic_Conv_evalPattern___regBuiltin_Lean_Elab_Tactic_Conv_evalPattern__1___closed__2_value_aux_2) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Elab_Tactic_Conv_evalPattern___closed__4_value) as *mut leanh::LeanObject,9299793053028177184 as *mut leanh::LeanObject] };
pub static l___private_Lean_Elab_Tactic_Conv_Pattern_0__Lean_Elab_Tactic_Conv_evalPattern___regBuiltin_Lean_Elab_Tactic_Conv_evalPattern__1___closed__2_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Pattern_0__Lean_Elab_Tactic_Conv_evalPattern___regBuiltin_Lean_Elab_Tactic_Conv_evalPattern__1___closed__2_value_aux_3) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Pattern_0__Lean_Elab_Tactic_Conv_evalPattern___regBuiltin_Lean_Elab_Tactic_Conv_evalPattern__1___closed__1_value) as *mut leanh::LeanObject,6508700515234341467 as *mut leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_Conv_Pattern_0__Lean_Elab_Tactic_Conv_evalPattern___regBuiltin_Lean_Elab_Tactic_Conv_evalPattern__1___closed__2: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Pattern_0__Lean_Elab_Tactic_Conv_evalPattern___regBuiltin_Lean_Elab_Tactic_Conv_evalPattern__1___closed__2_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Conv_Pattern_0__Lean_Elab_Tactic_Conv_evalPattern___regBuiltin_Lean_Elab_Tactic_Conv_evalPattern_declRange__3___closed__0_value: leanh::LeanCtorObject<2> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 105 as usize) << 1) | 1) as *mut leanh::LeanObject,((( 50 as usize) << 1) | 1) as *mut leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_Conv_Pattern_0__Lean_Elab_Tactic_Conv_evalPattern___regBuiltin_Lean_Elab_Tactic_Conv_evalPattern_declRange__3___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Pattern_0__Lean_Elab_Tactic_Conv_evalPattern___regBuiltin_Lean_Elab_Tactic_Conv_evalPattern_declRange__3___closed__0_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Conv_Pattern_0__Lean_Elab_Tactic_Conv_evalPattern___regBuiltin_Lean_Elab_Tactic_Conv_evalPattern_declRange__3___closed__1_value: leanh::LeanCtorObject<2> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 142 as usize) << 1) | 1) as *mut leanh::LeanObject,((( 31 as usize) << 1) | 1) as *mut leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_Conv_Pattern_0__Lean_Elab_Tactic_Conv_evalPattern___regBuiltin_Lean_Elab_Tactic_Conv_evalPattern_declRange__3___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Pattern_0__Lean_Elab_Tactic_Conv_evalPattern___regBuiltin_Lean_Elab_Tactic_Conv_evalPattern_declRange__3___closed__1_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Conv_Pattern_0__Lean_Elab_Tactic_Conv_evalPattern___regBuiltin_Lean_Elab_Tactic_Conv_evalPattern_declRange__3___closed__2_value: leanh::LeanCtorObject<4> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*4 + 0) as u16, other: 4, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Pattern_0__Lean_Elab_Tactic_Conv_evalPattern___regBuiltin_Lean_Elab_Tactic_Conv_evalPattern_declRange__3___closed__0_value) as *mut leanh::LeanObject,((( 50 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Pattern_0__Lean_Elab_Tactic_Conv_evalPattern___regBuiltin_Lean_Elab_Tactic_Conv_evalPattern_declRange__3___closed__1_value) as *mut leanh::LeanObject,((( 31 as usize) << 1) | 1) as *mut leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_Conv_Pattern_0__Lean_Elab_Tactic_Conv_evalPattern___regBuiltin_Lean_Elab_Tactic_Conv_evalPattern_declRange__3___closed__2: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Pattern_0__Lean_Elab_Tactic_Conv_evalPattern___regBuiltin_Lean_Elab_Tactic_Conv_evalPattern_declRange__3___closed__2_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Conv_Pattern_0__Lean_Elab_Tactic_Conv_evalPattern___regBuiltin_Lean_Elab_Tactic_Conv_evalPattern_declRange__3___closed__3_value: leanh::LeanCtorObject<2> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 105 as usize) << 1) | 1) as *mut leanh::LeanObject,((( 54 as usize) << 1) | 1) as *mut leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_Conv_Pattern_0__Lean_Elab_Tactic_Conv_evalPattern___regBuiltin_Lean_Elab_Tactic_Conv_evalPattern_declRange__3___closed__3: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Pattern_0__Lean_Elab_Tactic_Conv_evalPattern___regBuiltin_Lean_Elab_Tactic_Conv_evalPattern_declRange__3___closed__3_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Conv_Pattern_0__Lean_Elab_Tactic_Conv_evalPattern___regBuiltin_Lean_Elab_Tactic_Conv_evalPattern_declRange__3___closed__4_value: leanh::LeanCtorObject<2> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 105 as usize) << 1) | 1) as *mut leanh::LeanObject,((( 65 as usize) << 1) | 1) as *mut leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_Conv_Pattern_0__Lean_Elab_Tactic_Conv_evalPattern___regBuiltin_Lean_Elab_Tactic_Conv_evalPattern_declRange__3___closed__4: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Pattern_0__Lean_Elab_Tactic_Conv_evalPattern___regBuiltin_Lean_Elab_Tactic_Conv_evalPattern_declRange__3___closed__4_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Conv_Pattern_0__Lean_Elab_Tactic_Conv_evalPattern___regBuiltin_Lean_Elab_Tactic_Conv_evalPattern_declRange__3___closed__5_value: leanh::LeanCtorObject<4> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*4 + 0) as u16, other: 4, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Pattern_0__Lean_Elab_Tactic_Conv_evalPattern___regBuiltin_Lean_Elab_Tactic_Conv_evalPattern_declRange__3___closed__3_value) as *mut leanh::LeanObject,((( 54 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Pattern_0__Lean_Elab_Tactic_Conv_evalPattern___regBuiltin_Lean_Elab_Tactic_Conv_evalPattern_declRange__3___closed__4_value) as *mut leanh::LeanObject,((( 65 as usize) << 1) | 1) as *mut leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_Conv_Pattern_0__Lean_Elab_Tactic_Conv_evalPattern___regBuiltin_Lean_Elab_Tactic_Conv_evalPattern_declRange__3___closed__5: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Pattern_0__Lean_Elab_Tactic_Conv_evalPattern___regBuiltin_Lean_Elab_Tactic_Conv_evalPattern_declRange__3___closed__5_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Conv_Pattern_0__Lean_Elab_Tactic_Conv_evalPattern___regBuiltin_Lean_Elab_Tactic_Conv_evalPattern_declRange__3___closed__6_value: leanh::LeanCtorObject<2> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Pattern_0__Lean_Elab_Tactic_Conv_evalPattern___regBuiltin_Lean_Elab_Tactic_Conv_evalPattern_declRange__3___closed__2_value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Pattern_0__Lean_Elab_Tactic_Conv_evalPattern___regBuiltin_Lean_Elab_Tactic_Conv_evalPattern_declRange__3___closed__5_value) as *mut leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_Conv_Pattern_0__Lean_Elab_Tactic_Conv_evalPattern___regBuiltin_Lean_Elab_Tactic_Conv_evalPattern_declRange__3___closed__6: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Conv_Pattern_0__Lean_Elab_Tactic_Conv_evalPattern___regBuiltin_Lean_Elab_Tactic_Conv_evalPattern_declRange__3___closed__6_value) as *mut leanh::LeanObject;
pub unsafe fn l___private_Lean_Elab_Tactic_Conv_Pattern_0__Lean_Elab_Tactic_Conv_getContext___redArg(
    mut v_a_2193_: *mut leanh::LeanObject,
    mut v_a_2194_: *mut leanh::LeanObject,
    mut v_a_2195_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2197_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2198_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2199_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2200_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2201_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2202_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2203_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2205_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2206_: u8 = 0;
    let mut v___x_2208_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2209_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2210_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2197_ = l_Lean_Meta_getSimpCongrTheorems___redArg(v_a_2195_);
                if leanh::lean_obj_tag(v___x_2197_) == 0 {
                    v_a_2198_ = leanh::lean_ctor_get(v___x_2197_, 0);
                    leanh::lean_inc(v_a_2198_);
                    leanh::lean_dec_ref_known(v___x_2197_, 1);
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
                    v_a_2203_ = leanh::lean_ctor_get(v___x_2197_, 0);
                    v_isSharedCheck_2210_ = (!leanh::lean_is_exclusive(v___x_2197_)) as u8;
                    if v_isSharedCheck_2210_ == 0 {
                        v___x_2205_ = v___x_2197_;
                        v_isShared_2206_ = v_isSharedCheck_2210_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_2203_);
                        leanh::lean_dec(v___x_2197_);
                        v___x_2205_ = leanh::lean_box(0);
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
                    v_reuseFailAlloc_2209_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2209_, 0, v_a_2203_);
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
    mut v_a_2211_: *mut leanh::LeanObject,
    mut v_a_2212_: *mut leanh::LeanObject,
    mut v_a_2213_: *mut leanh::LeanObject,
    mut v_a_2214_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2215_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2215_ =
        l___private_Lean_Elab_Tactic_Conv_Pattern_0__Lean_Elab_Tactic_Conv_getContext___redArg(
            v_a_2211_, v_a_2212_, v_a_2213_,
        );
    leanh::lean_dec(v_a_2213_);
    leanh::lean_dec_ref(v_a_2212_);
    leanh::lean_dec_ref(v_a_2211_);
    return v_res_2215_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Conv_Pattern_0__Lean_Elab_Tactic_Conv_getContext(
    mut v_a_2216_: *mut leanh::LeanObject,
    mut v_a_2217_: *mut leanh::LeanObject,
    mut v_a_2218_: *mut leanh::LeanObject,
    mut v_a_2219_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2221_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2221_ =
        l___private_Lean_Elab_Tactic_Conv_Pattern_0__Lean_Elab_Tactic_Conv_getContext___redArg(
            v_a_2216_, v_a_2218_, v_a_2219_,
        );
    return v___x_2221_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Conv_Pattern_0__Lean_Elab_Tactic_Conv_getContext___boxed(
    mut v_a_2222_: *mut leanh::LeanObject,
    mut v_a_2223_: *mut leanh::LeanObject,
    mut v_a_2224_: *mut leanh::LeanObject,
    mut v_a_2225_: *mut leanh::LeanObject,
    mut v_a_2226_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2227_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2227_ = l___private_Lean_Elab_Tactic_Conv_Pattern_0__Lean_Elab_Tactic_Conv_getContext(
        v_a_2222_, v_a_2223_, v_a_2224_, v_a_2225_,
    );
    leanh::lean_dec(v_a_2225_);
    leanh::lean_dec_ref(v_a_2224_);
    leanh::lean_dec(v_a_2223_);
    leanh::lean_dec_ref(v_a_2222_);
    return v_res_2227_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Conv_Pattern_0__Lean_Elab_Tactic_Conv_matchPattern_x3f_go_x3f(
    mut v_pattern_2230_: *mut leanh::LeanObject,
    mut v_e_2231_: *mut leanh::LeanObject,
    mut v_a_2232_: *mut leanh::LeanObject,
    mut v_a_2233_: *mut leanh::LeanObject,
    mut v_a_2234_: *mut leanh::LeanObject,
    mut v_a_2235_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2237_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2238_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2239_: u8 = 0;
    let mut v___x_2240_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2241_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2242_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2243_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2245_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2246_: u8 = 0;
    let mut v___x_2247_: u8 = 0;
    let mut v___x_2248_: u8 = 0;
    let mut v___x_2249_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2251_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2252_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2253_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2254_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2255_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2257_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2258_: u8 = 0;
    let mut v_val_2259_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2261_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2262_: u8 = 0;
    let mut v_fst_2263_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2264_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2266_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2267_: u8 = 0;
    let mut v___x_2268_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2269_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2271_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2273_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2275_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2276_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2277_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2278_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2279_: u8 = 0;
    let mut v_isSharedCheck_2280_: u8 = 0;
    let mut v_isSharedCheck_2281_: u8 = 0;
    let mut v_unused_2282_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2283_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2284_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2285_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2287_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2288_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2289_: u8 = 0;
    let mut v_a_2290_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2292_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2293_: u8 = 0;
    let mut v___x_2295_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2296_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2297_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                leanh::lean_inc_ref(v_e_2231_);
                v___x_2237_ = l_Lean_Expr_toHeadIndex(v_e_2231_);
                leanh::lean_inc_ref(v_pattern_2230_);
                v___x_2238_ = l_Lean_Expr_toHeadIndex(v_pattern_2230_);
                v___x_2239_ = l_Lean_instBEqHeadIndex_beq(v___x_2237_, v___x_2238_);
                leanh::lean_dec(v___x_2238_);
                leanh::lean_dec(v___x_2237_);
                if v___x_2239_ == 0 {
                    leanh::lean_dec_ref(v_e_2231_);
                    leanh::lean_dec_ref(v_pattern_2230_);
                    v___x_2240_ = leanh::lean_box(0);
                    v___x_2241_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_2241_, 0, v___x_2240_);
                    return v___x_2241_;
                } else {
                    leanh::lean_inc_ref(v_e_2231_);
                    leanh::lean_inc_ref(v_pattern_2230_);
                    v___x_2242_ = l_Lean_Meta_isExprDefEqGuarded(
                        v_pattern_2230_,
                        v_e_2231_,
                        v_a_2232_,
                        v_a_2233_,
                        v_a_2234_,
                        v_a_2235_,
                    );
                    if leanh::lean_obj_tag(v___x_2242_) == 0 {
                        v_a_2243_ = leanh::lean_ctor_get(v___x_2242_, 0);
                        v_isSharedCheck_2289_ =
                            (!leanh::lean_is_exclusive(v___x_2242_)) as u8;
                        if v_isSharedCheck_2289_ == 0 {
                            v___x_2245_ = v___x_2242_;
                            v_isShared_2246_ = v_isSharedCheck_2289_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_2243_);
                            leanh::lean_dec(v___x_2242_);
                            v___x_2245_ = leanh::lean_box(0);
                            v_isShared_2246_ = v_isSharedCheck_2289_;
                            state = 1;
                            continue;
                        }
                    } else {
                        leanh::lean_dec_ref(v_e_2231_);
                        leanh::lean_dec_ref(v_pattern_2230_);
                        v_a_2290_ = leanh::lean_ctor_get(v___x_2242_, 0);
                        v_isSharedCheck_2297_ =
                            (!leanh::lean_is_exclusive(v___x_2242_)) as u8;
                        if v_isSharedCheck_2297_ == 0 {
                            v___x_2292_ = v___x_2242_;
                            v_isShared_2293_ = v_isSharedCheck_2297_;
                            state = 10;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_2290_);
                            leanh::lean_dec(v___x_2242_);
                            v___x_2292_ = leanh::lean_box(0);
                            v_isShared_2293_ = v_isSharedCheck_2297_;
                            state = 10;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v___x_2247_ = (leanh::lean_unbox(v_a_2243_) as u8);
                leanh::lean_dec(v_a_2243_);
                if v___x_2247_ == 0 {
                    v___x_2248_ = l_Lean_Expr_isApp(v_e_2231_);
                    if v___x_2248_ == 0 {
                        leanh::lean_dec_ref(v_e_2231_);
                        leanh::lean_dec_ref(v_pattern_2230_);
                        v___x_2249_ = leanh::lean_box(0);
                        if v_isShared_2246_ == 0 {
                            leanh::lean_ctor_set(v___x_2245_, 0, v___x_2249_);
                            v___x_2251_ = v___x_2245_;
                            state = 2;
                            continue;
                        } else {
                            v_reuseFailAlloc_2252_ =
                                leanh::lean_alloc_ctor(0, 1, (0) as u32);
                            leanh::lean_ctor_set(v_reuseFailAlloc_2252_, 0, v___x_2249_);
                            v___x_2251_ = v_reuseFailAlloc_2252_;
                            state = 2;
                            continue;
                        }
                    } else {
                        leanh::lean_del_object(v___x_2245_);
                        v___x_2253_ = l_Lean_Expr_appFn_x21(v_e_2231_);
                        v___x_2254_ = l___private_Lean_Elab_Tactic_Conv_Pattern_0__Lean_Elab_Tactic_Conv_matchPattern_x3f_go_x3f(v_pattern_2230_, v___x_2253_, v_a_2232_, v_a_2233_, v_a_2234_, v_a_2235_);
                        if leanh::lean_obj_tag(v___x_2254_) == 0 {
                            v_a_2255_ = leanh::lean_ctor_get(v___x_2254_, 0);
                            leanh::lean_inc(v_a_2255_);
                            if leanh::lean_obj_tag(v_a_2255_) == 0 {
                                leanh::lean_dec_ref(v_e_2231_);
                                return v___x_2254_;
                            } else {
                                v_isSharedCheck_2281_ =
                                    (!leanh::lean_is_exclusive(v___x_2254_)) as u8;
                                if v_isSharedCheck_2281_ == 0 {
                                    v_unused_2282_ = leanh::lean_ctor_get(v___x_2254_, 0);
                                    leanh::lean_dec(v_unused_2282_);
                                    v___x_2257_ = v___x_2254_;
                                    v_isShared_2258_ = v_isSharedCheck_2281_;
                                    state = 3;
                                    continue;
                                } else {
                                    leanh::lean_dec(v___x_2254_);
                                    v___x_2257_ = leanh::lean_box(0);
                                    v_isShared_2258_ = v_isSharedCheck_2281_;
                                    state = 3;
                                    continue;
                                }
                            }
                        } else {
                            leanh::lean_dec_ref(v_e_2231_);
                            return v___x_2254_;
                        }
                    }
                } else {
                    leanh::lean_dec_ref(v_pattern_2230_);
                    v___x_2283_ = l___private_Lean_Elab_Tactic_Conv_Pattern_0__Lean_Elab_Tactic_Conv_matchPattern_x3f_go_x3f___closed__0;
                    v___x_2284_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_2284_, 0, v_e_2231_);
                    leanh::lean_ctor_set(v___x_2284_, 1, v___x_2283_);
                    v___x_2285_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_2285_, 0, v___x_2284_);
                    if v_isShared_2246_ == 0 {
                        leanh::lean_ctor_set(v___x_2245_, 0, v___x_2285_);
                        v___x_2287_ = v___x_2245_;
                        state = 9;
                        continue;
                    } else {
                        v_reuseFailAlloc_2288_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2288_, 0, v___x_2285_);
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
                v_val_2259_ = leanh::lean_ctor_get(v_a_2255_, 0);
                v_isSharedCheck_2280_ = (!leanh::lean_is_exclusive(v_a_2255_)) as u8;
                if v_isSharedCheck_2280_ == 0 {
                    v___x_2261_ = v_a_2255_;
                    v_isShared_2262_ = v_isSharedCheck_2280_;
                    state = 4;
                    continue;
                } else {
                    leanh::lean_inc(v_val_2259_);
                    leanh::lean_dec(v_a_2255_);
                    v___x_2261_ = leanh::lean_box(0);
                    v_isShared_2262_ = v_isSharedCheck_2280_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v_fst_2263_ = leanh::lean_ctor_get(v_val_2259_, 0);
                v_snd_2264_ = leanh::lean_ctor_get(v_val_2259_, 1);
                v_isSharedCheck_2279_ = (!leanh::lean_is_exclusive(v_val_2259_)) as u8;
                if v_isSharedCheck_2279_ == 0 {
                    v___x_2266_ = v_val_2259_;
                    v_isShared_2267_ = v_isSharedCheck_2279_;
                    state = 5;
                    continue;
                } else {
                    leanh::lean_inc(v_snd_2264_);
                    leanh::lean_inc(v_fst_2263_);
                    leanh::lean_dec(v_val_2259_);
                    v___x_2266_ = leanh::lean_box(0);
                    v_isShared_2267_ = v_isSharedCheck_2279_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v___x_2268_ = l_Lean_Expr_appArg_x21(v_e_2231_);
                leanh::lean_dec_ref(v_e_2231_);
                v___x_2269_ = lean_array_push(v_snd_2264_, v___x_2268_);
                if v_isShared_2267_ == 0 {
                    leanh::lean_ctor_set(v___x_2266_, 1, v___x_2269_);
                    v___x_2271_ = v___x_2266_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_2278_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2278_, 0, v_fst_2263_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2278_, 1, v___x_2269_);
                    v___x_2271_ = v_reuseFailAlloc_2278_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                if v_isShared_2262_ == 0 {
                    leanh::lean_ctor_set(v___x_2261_, 0, v___x_2271_);
                    v___x_2273_ = v___x_2261_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_2277_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2277_, 0, v___x_2271_);
                    v___x_2273_ = v_reuseFailAlloc_2277_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                if v_isShared_2258_ == 0 {
                    leanh::lean_ctor_set(v___x_2257_, 0, v___x_2273_);
                    v___x_2275_ = v___x_2257_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_2276_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2276_, 0, v___x_2273_);
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
                    v_reuseFailAlloc_2296_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2296_, 0, v_a_2290_);
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
    mut v_pattern_2298_: *mut leanh::LeanObject,
    mut v_e_2299_: *mut leanh::LeanObject,
    mut v_a_2300_: *mut leanh::LeanObject,
    mut v_a_2301_: *mut leanh::LeanObject,
    mut v_a_2302_: *mut leanh::LeanObject,
    mut v_a_2303_: *mut leanh::LeanObject,
    mut v_a_2304_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2305_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2305_ =
        l___private_Lean_Elab_Tactic_Conv_Pattern_0__Lean_Elab_Tactic_Conv_matchPattern_x3f_go_x3f(
            v_pattern_2298_,
            v_e_2299_,
            v_a_2300_,
            v_a_2301_,
            v_a_2302_,
            v_a_2303_,
        );
    leanh::lean_dec(v_a_2303_);
    leanh::lean_dec_ref(v_a_2302_);
    leanh::lean_dec(v_a_2301_);
    leanh::lean_dec_ref(v_a_2300_);
    return v_res_2305_;
}
pub unsafe fn l_Lean_Meta_withNewMCtxDepth___at___00Lean_Elab_Tactic_Conv_matchPattern_x3f_spec__0___redArg(
    mut v_k_2306_: *mut leanh::LeanObject,
    mut v_allowLevelAssignments_2307_: u8,
    mut v___y_2308_: *mut leanh::LeanObject,
    mut v___y_2309_: *mut leanh::LeanObject,
    mut v___y_2310_: *mut leanh::LeanObject,
    mut v___y_2311_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2313_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2314_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2316_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2317_: u8 = 0;
    let mut v___x_2319_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2320_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2321_: u8 = 0;
    let mut v_a_2322_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2324_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2325_: u8 = 0;
    let mut v___x_2327_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2328_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2329_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2313_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withNewMCtxDepthImp(
                    leanh::lean_box(0),
                    v_allowLevelAssignments_2307_,
                    v_k_2306_,
                    v___y_2308_,
                    v___y_2309_,
                    v___y_2310_,
                    v___y_2311_,
                );
                if leanh::lean_obj_tag(v___x_2313_) == 0 {
                    v_a_2314_ = leanh::lean_ctor_get(v___x_2313_, 0);
                    v_isSharedCheck_2321_ = (!leanh::lean_is_exclusive(v___x_2313_)) as u8;
                    if v_isSharedCheck_2321_ == 0 {
                        v___x_2316_ = v___x_2313_;
                        v_isShared_2317_ = v_isSharedCheck_2321_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_2314_);
                        leanh::lean_dec(v___x_2313_);
                        v___x_2316_ = leanh::lean_box(0);
                        v_isShared_2317_ = v_isSharedCheck_2321_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_2322_ = leanh::lean_ctor_get(v___x_2313_, 0);
                    v_isSharedCheck_2329_ = (!leanh::lean_is_exclusive(v___x_2313_)) as u8;
                    if v_isSharedCheck_2329_ == 0 {
                        v___x_2324_ = v___x_2313_;
                        v_isShared_2325_ = v_isSharedCheck_2329_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_2322_);
                        leanh::lean_dec(v___x_2313_);
                        v___x_2324_ = leanh::lean_box(0);
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
                    v_reuseFailAlloc_2320_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2320_, 0, v_a_2314_);
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
                    v_reuseFailAlloc_2328_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2328_, 0, v_a_2322_);
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
    mut v_k_2330_: *mut leanh::LeanObject,
    mut v_allowLevelAssignments_2331_: *mut leanh::LeanObject,
    mut v___y_2332_: *mut leanh::LeanObject,
    mut v___y_2333_: *mut leanh::LeanObject,
    mut v___y_2334_: *mut leanh::LeanObject,
    mut v___y_2335_: *mut leanh::LeanObject,
    mut v___y_2336_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_allowLevelAssignments_boxed_2337_: u8 = 0;
    let mut v_res_2338_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_allowLevelAssignments_boxed_2337_ =
        (leanh::lean_unbox(v_allowLevelAssignments_2331_) as u8);
    v_res_2338_ = l_Lean_Meta_withNewMCtxDepth___at___00Lean_Elab_Tactic_Conv_matchPattern_x3f_spec__0___redArg(v_k_2330_, v_allowLevelAssignments_boxed_2337_, v___y_2332_, v___y_2333_, v___y_2334_, v___y_2335_);
    leanh::lean_dec(v___y_2335_);
    leanh::lean_dec_ref(v___y_2334_);
    leanh::lean_dec(v___y_2333_);
    leanh::lean_dec_ref(v___y_2332_);
    return v_res_2338_;
}
pub unsafe fn l_Lean_Meta_withNewMCtxDepth___at___00Lean_Elab_Tactic_Conv_matchPattern_x3f_spec__0(
    mut v_00_u03b1_2339_: *mut leanh::LeanObject,
    mut v_k_2340_: *mut leanh::LeanObject,
    mut v_allowLevelAssignments_2341_: u8,
    mut v___y_2342_: *mut leanh::LeanObject,
    mut v___y_2343_: *mut leanh::LeanObject,
    mut v___y_2344_: *mut leanh::LeanObject,
    mut v___y_2345_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2347_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2347_ = l_Lean_Meta_withNewMCtxDepth___at___00Lean_Elab_Tactic_Conv_matchPattern_x3f_spec__0___redArg(v_k_2340_, v_allowLevelAssignments_2341_, v___y_2342_, v___y_2343_, v___y_2344_, v___y_2345_);
    return v___x_2347_;
}
pub unsafe fn l_Lean_Meta_withNewMCtxDepth___at___00Lean_Elab_Tactic_Conv_matchPattern_x3f_spec__0___boxed(
    mut v_00_u03b1_2348_: *mut leanh::LeanObject,
    mut v_k_2349_: *mut leanh::LeanObject,
    mut v_allowLevelAssignments_2350_: *mut leanh::LeanObject,
    mut v___y_2351_: *mut leanh::LeanObject,
    mut v___y_2352_: *mut leanh::LeanObject,
    mut v___y_2353_: *mut leanh::LeanObject,
    mut v___y_2354_: *mut leanh::LeanObject,
    mut v___y_2355_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_allowLevelAssignments_boxed_2356_: u8 = 0;
    let mut v_res_2357_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_allowLevelAssignments_boxed_2356_ =
        (leanh::lean_unbox(v_allowLevelAssignments_2350_) as u8);
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
    leanh::lean_dec(v___y_2354_);
    leanh::lean_dec_ref(v___y_2353_);
    leanh::lean_dec(v___y_2352_);
    leanh::lean_dec_ref(v___y_2351_);
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
    mut v_pattern_2360_: *mut leanh::LeanObject,
    mut v_e_2361_: *mut leanh::LeanObject,
    mut v___y_2362_: *mut leanh::LeanObject,
    mut v___y_2363_: *mut leanh::LeanObject,
    mut v___y_2364_: *mut leanh::LeanObject,
    mut v___y_2365_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2367_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2368_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2369_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2370_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2371_: *mut leanh::LeanObject = core::ptr::null_mut();
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
    let mut v___x_2391_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2392_: u8 = 0;
    let mut v_trackZetaDelta_2393_: u8 = 0;
    let mut v_zetaDeltaSet_2394_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_lctx_2395_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_localInstances_2396_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_defEqCtx_x3f_2397_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_synthPendingDepth_2398_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_canUnfold_x3f_2399_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_univApprox_2400_: u8 = 0;
    let mut v_inTypeClassResolution_2401_: u8 = 0;
    let mut v_cacheInferType_2402_: u8 = 0;
    let mut v___x_2403_: u8 = 0;
    let mut v_config_2405_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2406_: u64 = 0;
    let mut v___x_2408_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2409_: u8 = 0;
    let mut v___x_2410_: u64 = 0;
    let mut v___x_2411_: u64 = 0;
    let mut v___x_2412_: u64 = 0;
    let mut v___x_2413_: u64 = 0;
    let mut v_key_2414_: u64 = 0;
    let mut v___x_2415_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2417_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2418_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2419_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2420_: u8 = 0;
    let mut v_unused_2421_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2422_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2423_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2424_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2425_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2426_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2427_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2428_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2429_: u8 = 0;
    let mut v_a_2430_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2432_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2433_: u8 = 0;
    let mut v___x_2435_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2436_: *mut leanh::LeanObject = core::ptr::null_mut();
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
                if leanh::lean_obj_tag(v___x_2367_) == 0 {
                    v_a_2368_ = leanh::lean_ctor_get(v___x_2367_, 0);
                    leanh::lean_inc(v_a_2368_);
                    leanh::lean_dec_ref_known(v___x_2367_, 1);
                    v_snd_2369_ = leanh::lean_ctor_get(v_a_2368_, 1);
                    leanh::lean_inc(v_snd_2369_);
                    leanh::lean_dec(v_a_2368_);
                    v_snd_2370_ = leanh::lean_ctor_get(v_snd_2369_, 1);
                    leanh::lean_inc(v_snd_2370_);
                    leanh::lean_dec(v_snd_2369_);
                    v___x_2371_ = l_Lean_Meta_Context_config(v___y_2362_);
                    v_foApprox_2372_ = leanh::lean_ctor_get_uint8(v___x_2371_, 0 as u32);
                    v_ctxApprox_2373_ = leanh::lean_ctor_get_uint8(v___x_2371_, 1 as u32);
                    v_quasiPatternApprox_2374_ =
                        leanh::lean_ctor_get_uint8(v___x_2371_, 2 as u32);
                    v_constApprox_2375_ = leanh::lean_ctor_get_uint8(v___x_2371_, 3 as u32);
                    v_isDefEqStuckEx_2376_ =
                        leanh::lean_ctor_get_uint8(v___x_2371_, 4 as u32);
                    v_unificationHints_2377_ =
                        leanh::lean_ctor_get_uint8(v___x_2371_, 5 as u32);
                    v_proofIrrelevance_2378_ =
                        leanh::lean_ctor_get_uint8(v___x_2371_, 6 as u32);
                    v_assignSyntheticOpaque_2379_ =
                        leanh::lean_ctor_get_uint8(v___x_2371_, 7 as u32);
                    v_offsetCnstrs_2380_ = leanh::lean_ctor_get_uint8(v___x_2371_, 8 as u32);
                    v_etaStruct_2381_ = leanh::lean_ctor_get_uint8(v___x_2371_, 10 as u32);
                    v_univApprox_2382_ = leanh::lean_ctor_get_uint8(v___x_2371_, 11 as u32);
                    v_iota_2383_ = leanh::lean_ctor_get_uint8(v___x_2371_, 12 as u32);
                    v_beta_2384_ = leanh::lean_ctor_get_uint8(v___x_2371_, 13 as u32);
                    v_proj_2385_ = leanh::lean_ctor_get_uint8(v___x_2371_, 14 as u32);
                    v_zeta_2386_ = leanh::lean_ctor_get_uint8(v___x_2371_, 15 as u32);
                    v_zetaDelta_2387_ = leanh::lean_ctor_get_uint8(v___x_2371_, 16 as u32);
                    v_zetaUnused_2388_ = leanh::lean_ctor_get_uint8(v___x_2371_, 17 as u32);
                    v_zetaHave_2389_ = leanh::lean_ctor_get_uint8(v___x_2371_, 18 as u32);
                    v_isSharedCheck_2429_ = (!leanh::lean_is_exclusive(v___x_2371_)) as u8;
                    if v_isSharedCheck_2429_ == 0 {
                        v___x_2391_ = v___x_2371_;
                        v_isShared_2392_ = v_isSharedCheck_2429_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_dec(v___x_2371_);
                        v___x_2391_ = leanh::lean_box(0);
                        v_isShared_2392_ = v_isSharedCheck_2429_;
                        state = 1;
                        continue;
                    }
                } else {
                    leanh::lean_dec_ref(v___y_2362_);
                    leanh::lean_dec_ref(v_e_2361_);
                    v_a_2430_ = leanh::lean_ctor_get(v___x_2367_, 0);
                    v_isSharedCheck_2437_ = (!leanh::lean_is_exclusive(v___x_2367_)) as u8;
                    if v_isSharedCheck_2437_ == 0 {
                        v___x_2432_ = v___x_2367_;
                        v_isShared_2433_ = v_isSharedCheck_2437_;
                        state = 5;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_2430_);
                        leanh::lean_dec(v___x_2367_);
                        v___x_2432_ = leanh::lean_box(0);
                        v_isShared_2433_ = v_isSharedCheck_2437_;
                        state = 5;
                        continue;
                    }
                }
            }
            1 => {
                v_trackZetaDelta_2393_ = leanh::lean_ctor_get_uint8(
                    v___y_2362_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 7) as u32,
                );
                v_zetaDeltaSet_2394_ = leanh::lean_ctor_get(v___y_2362_, 1);
                leanh::lean_inc(v_zetaDeltaSet_2394_);
                v_lctx_2395_ = leanh::lean_ctor_get(v___y_2362_, 2);
                leanh::lean_inc_ref(v_lctx_2395_);
                v_localInstances_2396_ = leanh::lean_ctor_get(v___y_2362_, 3);
                leanh::lean_inc_ref(v_localInstances_2396_);
                v_defEqCtx_x3f_2397_ = leanh::lean_ctor_get(v___y_2362_, 4);
                leanh::lean_inc(v_defEqCtx_x3f_2397_);
                v_synthPendingDepth_2398_ = leanh::lean_ctor_get(v___y_2362_, 5);
                leanh::lean_inc(v_synthPendingDepth_2398_);
                v_canUnfold_x3f_2399_ = leanh::lean_ctor_get(v___y_2362_, 6);
                leanh::lean_inc(v_canUnfold_x3f_2399_);
                v_univApprox_2400_ = leanh::lean_ctor_get_uint8(
                    v___y_2362_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 7 + 1) as u32,
                );
                v_inTypeClassResolution_2401_ = leanh::lean_ctor_get_uint8(
                    v___y_2362_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 7 + 2) as u32,
                );
                v_cacheInferType_2402_ = leanh::lean_ctor_get_uint8(
                    v___y_2362_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 7 + 3) as u32,
                );
                v___x_2403_ = 2;
                if v_isShared_2392_ == 0 {
                    v_config_2405_ = v___x_2391_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2428_ = leanh::lean_alloc_ctor(0, 0, (19) as u32);
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_2428_,
                        0 as u32,
                        v_foApprox_2372_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_2428_,
                        1 as u32,
                        v_ctxApprox_2373_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_2428_,
                        2 as u32,
                        v_quasiPatternApprox_2374_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_2428_,
                        3 as u32,
                        v_constApprox_2375_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_2428_,
                        4 as u32,
                        v_isDefEqStuckEx_2376_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_2428_,
                        5 as u32,
                        v_unificationHints_2377_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_2428_,
                        6 as u32,
                        v_proofIrrelevance_2378_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_2428_,
                        7 as u32,
                        v_assignSyntheticOpaque_2379_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_2428_,
                        8 as u32,
                        v_offsetCnstrs_2380_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_2428_,
                        10 as u32,
                        v_etaStruct_2381_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_2428_,
                        11 as u32,
                        v_univApprox_2382_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_2428_,
                        12 as u32,
                        v_iota_2383_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_2428_,
                        13 as u32,
                        v_beta_2384_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_2428_,
                        14 as u32,
                        v_proj_2385_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_2428_,
                        15 as u32,
                        v_zeta_2386_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_2428_,
                        16 as u32,
                        v_zetaDelta_2387_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_2428_,
                        17 as u32,
                        v_zetaUnused_2388_,
                    );
                    leanh::lean_ctor_set_uint8(
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
                leanh::lean_ctor_set_uint8(v_config_2405_, 9 as u32, v___x_2403_);
                v___x_2406_ = l_Lean_Meta_Context_configKey(v___y_2362_);
                v_isSharedCheck_2420_ = (!leanh::lean_is_exclusive(v___y_2362_)) as u8;
                if v_isSharedCheck_2420_ == 0 {
                    v_unused_2421_ = leanh::lean_ctor_get(v___y_2362_, 6);
                    leanh::lean_dec(v_unused_2421_);
                    v_unused_2422_ = leanh::lean_ctor_get(v___y_2362_, 5);
                    leanh::lean_dec(v_unused_2422_);
                    v_unused_2423_ = leanh::lean_ctor_get(v___y_2362_, 4);
                    leanh::lean_dec(v_unused_2423_);
                    v_unused_2424_ = leanh::lean_ctor_get(v___y_2362_, 3);
                    leanh::lean_dec(v_unused_2424_);
                    v_unused_2425_ = leanh::lean_ctor_get(v___y_2362_, 2);
                    leanh::lean_dec(v_unused_2425_);
                    v_unused_2426_ = leanh::lean_ctor_get(v___y_2362_, 1);
                    leanh::lean_dec(v_unused_2426_);
                    v_unused_2427_ = leanh::lean_ctor_get(v___y_2362_, 0);
                    leanh::lean_dec(v_unused_2427_);
                    v___x_2408_ = v___y_2362_;
                    v_isShared_2409_ = v_isSharedCheck_2420_;
                    state = 3;
                    continue;
                } else {
                    leanh::lean_dec(v___y_2362_);
                    v___x_2408_ = leanh::lean_box(0);
                    v_isShared_2409_ = v_isSharedCheck_2420_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_2410_ = 3u64;
                v___x_2411_ = lean_uint64_shift_right(v___x_2406_, v___x_2410_);
                v___x_2412_ = lean_uint64_shift_left(v___x_2411_, v___x_2410_);
                v___x_2413_ = leanh::lean_uint64_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_Elab_Tactic_Conv_matchPattern_x3f___lam__0___closed__0
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_Elab_Tactic_Conv_matchPattern_x3f___lam__0___closed__0_once
                    ),
                    _init_l_Lean_Elab_Tactic_Conv_matchPattern_x3f___lam__0___closed__0,
                );
                v_key_2414_ = lean_uint64_lor(v___x_2412_, v___x_2413_);
                v___x_2415_ = leanh::lean_alloc_ctor(0, 1, (8) as u32);
                leanh::lean_ctor_set(v___x_2415_, 0, v_config_2405_);
                leanh::lean_ctor_set_uint64(
                    v___x_2415_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                    v_key_2414_,
                );
                if v_isShared_2409_ == 0 {
                    leanh::lean_ctor_set(v___x_2408_, 0, v___x_2415_);
                    v___x_2417_ = v___x_2408_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2419_ = leanh::lean_alloc_ctor(0, 7, (4) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2419_, 0, v___x_2415_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2419_, 1, v_zetaDeltaSet_2394_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2419_, 2, v_lctx_2395_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2419_, 3, v_localInstances_2396_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2419_, 4, v_defEqCtx_x3f_2397_);
                    leanh::lean_ctor_set(
                        v_reuseFailAlloc_2419_,
                        5,
                        v_synthPendingDepth_2398_,
                    );
                    leanh::lean_ctor_set(v_reuseFailAlloc_2419_, 6, v_canUnfold_x3f_2399_);
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_2419_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 7) as u32,
                        v_trackZetaDelta_2393_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_2419_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 7 + 1) as u32,
                        v_univApprox_2400_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_2419_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 7 + 2) as u32,
                        v_inTypeClassResolution_2401_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_2419_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 7 + 3) as u32,
                        v_cacheInferType_2402_,
                    );
                    v___x_2417_ = v_reuseFailAlloc_2419_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_2418_ = l___private_Lean_Elab_Tactic_Conv_Pattern_0__Lean_Elab_Tactic_Conv_matchPattern_x3f_go_x3f(v_snd_2370_, v_e_2361_, v___x_2417_, v___y_2363_, v___y_2364_, v___y_2365_);
                leanh::lean_dec_ref(v___x_2417_);
                return v___x_2418_;
            }
            5 => {
                if v_isShared_2433_ == 0 {
                    v___x_2435_ = v___x_2432_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_2436_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2436_, 0, v_a_2430_);
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
    mut v_pattern_2438_: *mut leanh::LeanObject,
    mut v_e_2439_: *mut leanh::LeanObject,
    mut v___y_2440_: *mut leanh::LeanObject,
    mut v___y_2441_: *mut leanh::LeanObject,
    mut v___y_2442_: *mut leanh::LeanObject,
    mut v___y_2443_: *mut leanh::LeanObject,
    mut v___y_2444_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2445_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2445_ = l_Lean_Elab_Tactic_Conv_matchPattern_x3f___lam__0(
        v_pattern_2438_,
        v_e_2439_,
        v___y_2440_,
        v___y_2441_,
        v___y_2442_,
        v___y_2443_,
    );
    leanh::lean_dec(v___y_2443_);
    leanh::lean_dec_ref(v___y_2442_);
    leanh::lean_dec(v___y_2441_);
    return v_res_2445_;
}
pub unsafe fn l_Lean_Elab_Tactic_Conv_matchPattern_x3f(
    mut v_pattern_2446_: *mut leanh::LeanObject,
    mut v_e_2447_: *mut leanh::LeanObject,
    mut v_a_2448_: *mut leanh::LeanObject,
    mut v_a_2449_: *mut leanh::LeanObject,
    mut v_a_2450_: *mut leanh::LeanObject,
    mut v_a_2451_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_2453_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2454_: u8 = 0;
    let mut v___x_2455_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_2453_ = leanh::lean_alloc_closure(
        l_Lean_Elab_Tactic_Conv_matchPattern_x3f___lam__0___boxed as *mut core::ffi::c_void,
        7,
        2,
    );
    leanh::lean_closure_set(v___f_2453_, 0, v_pattern_2446_);
    leanh::lean_closure_set(v___f_2453_, 1, v_e_2447_);
    v___x_2454_ = 0;
    v___x_2455_ = l_Lean_Meta_withNewMCtxDepth___at___00Lean_Elab_Tactic_Conv_matchPattern_x3f_spec__0___redArg(v___f_2453_, v___x_2454_, v_a_2448_, v_a_2449_, v_a_2450_, v_a_2451_);
    return v___x_2455_;
}
pub unsafe fn l_Lean_Elab_Tactic_Conv_matchPattern_x3f___boxed(
    mut v_pattern_2456_: *mut leanh::LeanObject,
    mut v_e_2457_: *mut leanh::LeanObject,
    mut v_a_2458_: *mut leanh::LeanObject,
    mut v_a_2459_: *mut leanh::LeanObject,
    mut v_a_2460_: *mut leanh::LeanObject,
    mut v_a_2461_: *mut leanh::LeanObject,
    mut v_a_2462_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2463_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2463_ = l_Lean_Elab_Tactic_Conv_matchPattern_x3f(
        v_pattern_2456_,
        v_e_2457_,
        v_a_2458_,
        v_a_2459_,
        v_a_2460_,
        v_a_2461_,
    );
    leanh::lean_dec(v_a_2461_);
    leanh::lean_dec_ref(v_a_2460_);
    leanh::lean_dec(v_a_2459_);
    leanh::lean_dec_ref(v_a_2458_);
    return v_res_2463_;
}
pub unsafe fn l_Lean_Elab_Tactic_Conv_PatternMatchState_ctorIdx(
    mut v_x_2464_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_2464_) == 0 {
        let mut v___x_2465_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_2465_ = leanh::lean_unsigned_to_nat(0);
        return v___x_2465_;
    } else {
        let mut v___x_2466_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_2466_ = leanh::lean_unsigned_to_nat(1);
        return v___x_2466_;
    }
}
pub unsafe fn l_Lean_Elab_Tactic_Conv_PatternMatchState_ctorIdx___boxed(
    mut v_x_2467_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2468_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2468_ = l_Lean_Elab_Tactic_Conv_PatternMatchState_ctorIdx(v_x_2467_);
    leanh::lean_dec_ref(v_x_2467_);
    return v_res_2468_;
}
pub unsafe fn l_Lean_Elab_Tactic_Conv_PatternMatchState_ctorElim___redArg(
    mut v_t_2469_: *mut leanh::LeanObject,
    mut v_k_2470_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_t_2469_) == 0 {
        let mut v_subgoals_2471_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2472_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_subgoals_2471_ = leanh::lean_ctor_get(v_t_2469_, 0);
        leanh::lean_inc_ref(v_subgoals_2471_);
        leanh::lean_dec_ref_known(v_t_2469_, 1);
        v___x_2472_ = leanh::lean_apply_1(v_k_2470_, v_subgoals_2471_);
        return v___x_2472_;
    } else {
        let mut v_subgoals_2473_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_idx_2474_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_remaining_2475_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2476_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_subgoals_2473_ = leanh::lean_ctor_get(v_t_2469_, 0);
        leanh::lean_inc_ref(v_subgoals_2473_);
        v_idx_2474_ = leanh::lean_ctor_get(v_t_2469_, 1);
        leanh::lean_inc(v_idx_2474_);
        v_remaining_2475_ = leanh::lean_ctor_get(v_t_2469_, 2);
        leanh::lean_inc(v_remaining_2475_);
        leanh::lean_dec_ref_known(v_t_2469_, 3);
        v___x_2476_ =
            leanh::lean_apply_3(v_k_2470_, v_subgoals_2473_, v_idx_2474_, v_remaining_2475_);
        return v___x_2476_;
    }
}
pub unsafe fn l_Lean_Elab_Tactic_Conv_PatternMatchState_ctorElim(
    mut v_motive_2477_: *mut leanh::LeanObject,
    mut v_ctorIdx_2478_: *mut leanh::LeanObject,
    mut v_t_2479_: *mut leanh::LeanObject,
    mut v_h_2480_: *mut leanh::LeanObject,
    mut v_k_2481_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2482_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2482_ = l_Lean_Elab_Tactic_Conv_PatternMatchState_ctorElim___redArg(v_t_2479_, v_k_2481_);
    return v___x_2482_;
}
pub unsafe fn l_Lean_Elab_Tactic_Conv_PatternMatchState_ctorElim___boxed(
    mut v_motive_2483_: *mut leanh::LeanObject,
    mut v_ctorIdx_2484_: *mut leanh::LeanObject,
    mut v_t_2485_: *mut leanh::LeanObject,
    mut v_h_2486_: *mut leanh::LeanObject,
    mut v_k_2487_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2488_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2488_ = l_Lean_Elab_Tactic_Conv_PatternMatchState_ctorElim(
        v_motive_2483_,
        v_ctorIdx_2484_,
        v_t_2485_,
        v_h_2486_,
        v_k_2487_,
    );
    leanh::lean_dec(v_ctorIdx_2484_);
    return v_res_2488_;
}
pub unsafe fn l_Lean_Elab_Tactic_Conv_PatternMatchState_all_elim___redArg(
    mut v_t_2489_: *mut leanh::LeanObject,
    mut v_all_2490_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2491_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2491_ =
        l_Lean_Elab_Tactic_Conv_PatternMatchState_ctorElim___redArg(v_t_2489_, v_all_2490_);
    return v___x_2491_;
}
pub unsafe fn l_Lean_Elab_Tactic_Conv_PatternMatchState_all_elim(
    mut v_motive_2492_: *mut leanh::LeanObject,
    mut v_t_2493_: *mut leanh::LeanObject,
    mut v_h_2494_: *mut leanh::LeanObject,
    mut v_all_2495_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2496_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2496_ =
        l_Lean_Elab_Tactic_Conv_PatternMatchState_ctorElim___redArg(v_t_2493_, v_all_2495_);
    return v___x_2496_;
}
pub unsafe fn l_Lean_Elab_Tactic_Conv_PatternMatchState_occs_elim___redArg(
    mut v_t_2497_: *mut leanh::LeanObject,
    mut v_occs_2498_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2499_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2499_ =
        l_Lean_Elab_Tactic_Conv_PatternMatchState_ctorElim___redArg(v_t_2497_, v_occs_2498_);
    return v___x_2499_;
}
pub unsafe fn l_Lean_Elab_Tactic_Conv_PatternMatchState_occs_elim(
    mut v_motive_2500_: *mut leanh::LeanObject,
    mut v_t_2501_: *mut leanh::LeanObject,
    mut v_h_2502_: *mut leanh::LeanObject,
    mut v_occs_2503_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2504_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2504_ =
        l_Lean_Elab_Tactic_Conv_PatternMatchState_ctorElim___redArg(v_t_2501_, v_occs_2503_);
    return v___x_2504_;
}
pub unsafe fn l_Lean_Elab_Tactic_Conv_PatternMatchState_isDone(
    mut v_x_2505_: *mut leanh::LeanObject,
) -> u8 {
    if leanh::lean_obj_tag(v_x_2505_) == 0 {
        let mut v___x_2506_: u8 = 0;
        v___x_2506_ = 0;
        return v___x_2506_;
    } else {
        let mut v_remaining_2507_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2508_: u8 = 0;
        v_remaining_2507_ = leanh::lean_ctor_get(v_x_2505_, 2);
        v___x_2508_ = l_List_isEmpty___redArg(v_remaining_2507_);
        return v___x_2508_;
    }
}
pub unsafe fn l_Lean_Elab_Tactic_Conv_PatternMatchState_isDone___boxed(
    mut v_x_2509_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2510_: u8 = 0;
    let mut v_r_2511_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2510_ = l_Lean_Elab_Tactic_Conv_PatternMatchState_isDone(v_x_2509_);
    leanh::lean_dec_ref(v_x_2509_);
    v_r_2511_ = leanh::lean_box((v_res_2510_) as usize);
    return v_r_2511_;
}
pub unsafe fn l_Lean_Elab_Tactic_Conv_PatternMatchState_isReady(
    mut v_x_2512_: *mut leanh::LeanObject,
) -> u8 {
    if leanh::lean_obj_tag(v_x_2512_) == 0 {
        let mut v___x_2513_: u8 = 0;
        v___x_2513_ = 1;
        return v___x_2513_;
    } else {
        let mut v_remaining_2514_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_remaining_2514_ = leanh::lean_ctor_get(v_x_2512_, 2);
        if leanh::lean_obj_tag(v_remaining_2514_) == 1 {
            let mut v_head_2515_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_idx_2516_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_fst_2517_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2518_: u8 = 0;
            v_head_2515_ = leanh::lean_ctor_get(v_remaining_2514_, 0);
            v_idx_2516_ = leanh::lean_ctor_get(v_x_2512_, 1);
            v_fst_2517_ = leanh::lean_ctor_get(v_head_2515_, 0);
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
    mut v_x_2520_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2521_: u8 = 0;
    let mut v_r_2522_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2521_ = l_Lean_Elab_Tactic_Conv_PatternMatchState_isReady(v_x_2520_);
    leanh::lean_dec_ref(v_x_2520_);
    v_r_2522_ = leanh::lean_box((v_res_2521_) as usize);
    return v_r_2522_;
}
pub unsafe fn l_Lean_Elab_Tactic_Conv_PatternMatchState_skip(
    mut v_x_2523_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_subgoals_2524_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_idx_2525_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_remaining_2526_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2528_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2529_: u8 = 0;
    let mut v___x_2530_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2531_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2533_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2534_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2535_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_2523_) == 1 {
                    v_subgoals_2524_ = leanh::lean_ctor_get(v_x_2523_, 0);
                    v_idx_2525_ = leanh::lean_ctor_get(v_x_2523_, 1);
                    v_remaining_2526_ = leanh::lean_ctor_get(v_x_2523_, 2);
                    v_isSharedCheck_2535_ = (!leanh::lean_is_exclusive(v_x_2523_)) as u8;
                    if v_isSharedCheck_2535_ == 0 {
                        v___x_2528_ = v_x_2523_;
                        v_isShared_2529_ = v_isSharedCheck_2535_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_remaining_2526_);
                        leanh::lean_inc(v_idx_2525_);
                        leanh::lean_inc(v_subgoals_2524_);
                        leanh::lean_dec(v_x_2523_);
                        v___x_2528_ = leanh::lean_box(0);
                        v_isShared_2529_ = v_isSharedCheck_2535_;
                        state = 1;
                        continue;
                    }
                } else {
                    return v_x_2523_;
                }
            }
            1 => {
                v___x_2530_ = leanh::lean_unsigned_to_nat(1);
                v___x_2531_ = lean_nat_add(v_idx_2525_, v___x_2530_);
                leanh::lean_dec(v_idx_2525_);
                if v_isShared_2529_ == 0 {
                    leanh::lean_ctor_set(v___x_2528_, 1, v___x_2531_);
                    v___x_2533_ = v___x_2528_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2534_ = leanh::lean_alloc_ctor(1, 3, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2534_, 0, v_subgoals_2524_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2534_, 1, v___x_2531_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2534_, 2, v_remaining_2526_);
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
    mut v_mvarId_2536_: *mut leanh::LeanObject,
    mut v_x_2537_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_subgoals_2538_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2540_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2541_: u8 = 0;
    let mut v___x_2542_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2544_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2545_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2546_: u8 = 0;
    let mut v_remaining_2547_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_2548_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_subgoals_2549_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_idx_2550_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2552_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2553_: u8 = 0;
    let mut v_tail_2554_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2555_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2557_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2558_: u8 = 0;
    let mut v___x_2560_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2561_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2562_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2563_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2565_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2566_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2567_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2568_: u8 = 0;
    let mut v_unused_2569_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2570_: u8 = 0;
    let mut v_unused_2571_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_2537_) == 0 {
                    v_subgoals_2538_ = leanh::lean_ctor_get(v_x_2537_, 0);
                    v_isSharedCheck_2546_ = (!leanh::lean_is_exclusive(v_x_2537_)) as u8;
                    if v_isSharedCheck_2546_ == 0 {
                        v___x_2540_ = v_x_2537_;
                        v_isShared_2541_ = v_isSharedCheck_2546_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_subgoals_2538_);
                        leanh::lean_dec(v_x_2537_);
                        v___x_2540_ = leanh::lean_box(0);
                        v_isShared_2541_ = v_isSharedCheck_2546_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_remaining_2547_ = leanh::lean_ctor_get(v_x_2537_, 2);
                    if leanh::lean_obj_tag(v_remaining_2547_) == 1 {
                        leanh::lean_inc_ref(v_remaining_2547_);
                        v_head_2548_ = leanh::lean_ctor_get(v_remaining_2547_, 0);
                        leanh::lean_inc(v_head_2548_);
                        v_subgoals_2549_ = leanh::lean_ctor_get(v_x_2537_, 0);
                        v_idx_2550_ = leanh::lean_ctor_get(v_x_2537_, 1);
                        v_isSharedCheck_2570_ = (!leanh::lean_is_exclusive(v_x_2537_)) as u8;
                        if v_isSharedCheck_2570_ == 0 {
                            v_unused_2571_ = leanh::lean_ctor_get(v_x_2537_, 2);
                            leanh::lean_dec(v_unused_2571_);
                            v___x_2552_ = v_x_2537_;
                            v_isShared_2553_ = v_isSharedCheck_2570_;
                            state = 3;
                            continue;
                        } else {
                            leanh::lean_inc(v_idx_2550_);
                            leanh::lean_inc(v_subgoals_2549_);
                            leanh::lean_dec(v_x_2537_);
                            v___x_2552_ = leanh::lean_box(0);
                            v_isShared_2553_ = v_isSharedCheck_2570_;
                            state = 3;
                            continue;
                        }
                    } else {
                        leanh::lean_dec(v_mvarId_2536_);
                        return v_x_2537_;
                    }
                }
            }
            1 => {
                v___x_2542_ = lean_array_push(v_subgoals_2538_, v_mvarId_2536_);
                if v_isShared_2541_ == 0 {
                    leanh::lean_ctor_set(v___x_2540_, 0, v___x_2542_);
                    v___x_2544_ = v___x_2540_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2545_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2545_, 0, v___x_2542_);
                    v___x_2544_ = v_reuseFailAlloc_2545_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2544_;
            }
            3 => {
                v_tail_2554_ = leanh::lean_ctor_get(v_remaining_2547_, 1);
                leanh::lean_inc(v_tail_2554_);
                leanh::lean_dec_ref_known(v_remaining_2547_, 2);
                v_snd_2555_ = leanh::lean_ctor_get(v_head_2548_, 1);
                v_isSharedCheck_2568_ = (!leanh::lean_is_exclusive(v_head_2548_)) as u8;
                if v_isSharedCheck_2568_ == 0 {
                    v_unused_2569_ = leanh::lean_ctor_get(v_head_2548_, 0);
                    leanh::lean_dec(v_unused_2569_);
                    v___x_2557_ = v_head_2548_;
                    v_isShared_2558_ = v_isSharedCheck_2568_;
                    state = 4;
                    continue;
                } else {
                    leanh::lean_inc(v_snd_2555_);
                    leanh::lean_dec(v_head_2548_);
                    v___x_2557_ = leanh::lean_box(0);
                    v_isShared_2558_ = v_isSharedCheck_2568_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                if v_isShared_2558_ == 0 {
                    leanh::lean_ctor_set(v___x_2557_, 1, v_mvarId_2536_);
                    leanh::lean_ctor_set(v___x_2557_, 0, v_snd_2555_);
                    v___x_2560_ = v___x_2557_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_2567_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2567_, 0, v_snd_2555_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2567_, 1, v_mvarId_2536_);
                    v___x_2560_ = v_reuseFailAlloc_2567_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v___x_2561_ = lean_array_push(v_subgoals_2549_, v___x_2560_);
                v___x_2562_ = leanh::lean_unsigned_to_nat(1);
                v___x_2563_ = lean_nat_add(v_idx_2550_, v___x_2562_);
                leanh::lean_dec(v_idx_2550_);
                if v_isShared_2553_ == 0 {
                    leanh::lean_ctor_set(v___x_2552_, 2, v_tail_2554_);
                    leanh::lean_ctor_set(v___x_2552_, 1, v___x_2563_);
                    leanh::lean_ctor_set(v___x_2552_, 0, v___x_2561_);
                    v___x_2565_ = v___x_2552_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_2566_ = leanh::lean_alloc_ctor(1, 3, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2566_, 0, v___x_2561_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2566_, 1, v___x_2563_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2566_, 2, v_tail_2554_);
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
    mut v_as_2572_: *mut leanh::LeanObject,
    mut v_sz_2573_: usize,
    mut v_i_2574_: usize,
    mut v_b_2575_: *mut leanh::LeanObject,
    mut v___y_2576_: *mut leanh::LeanObject,
    mut v___y_2577_: *mut leanh::LeanObject,
    mut v___y_2578_: *mut leanh::LeanObject,
    mut v___y_2579_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2581_: u8 = 0;
    let mut v___x_2582_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2583_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2584_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2585_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2586_: usize = 0;
    let mut v___x_2587_: usize = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2581_ = lean_usize_dec_lt(v_i_2574_, v_sz_2573_);
                if v___x_2581_ == 0 {
                    v___x_2582_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_2582_, 0, v_b_2575_);
                    return v___x_2582_;
                } else {
                    v_a_2583_ = lean_array_uget_borrowed(v_as_2572_, v_i_2574_);
                    leanh::lean_inc(v_a_2583_);
                    v___x_2584_ = l_Lean_Meta_mkCongrFun(
                        v_b_2575_,
                        v_a_2583_,
                        v___y_2576_,
                        v___y_2577_,
                        v___y_2578_,
                        v___y_2579_,
                    );
                    if leanh::lean_obj_tag(v___x_2584_) == 0 {
                        v_a_2585_ = leanh::lean_ctor_get(v___x_2584_, 0);
                        leanh::lean_inc(v_a_2585_);
                        leanh::lean_dec_ref_known(v___x_2584_, 1);
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
    mut v_as_2589_: *mut leanh::LeanObject,
    mut v_sz_2590_: *mut leanh::LeanObject,
    mut v_i_2591_: *mut leanh::LeanObject,
    mut v_b_2592_: *mut leanh::LeanObject,
    mut v___y_2593_: *mut leanh::LeanObject,
    mut v___y_2594_: *mut leanh::LeanObject,
    mut v___y_2595_: *mut leanh::LeanObject,
    mut v___y_2596_: *mut leanh::LeanObject,
    mut v___y_2597_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_sz_boxed_2598_: usize = 0;
    let mut v_i_boxed_2599_: usize = 0;
    let mut v_res_2600_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_2598_ = leanh::lean_unbox_usize(v_sz_2590_);
    leanh::lean_dec(v_sz_2590_);
    v_i_boxed_2599_ = leanh::lean_unbox_usize(v_i_2591_);
    leanh::lean_dec(v_i_2591_);
    v_res_2600_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Conv_Pattern_0__Lean_Elab_Tactic_Conv_pre_spec__0___redArg(v_as_2589_, v_sz_boxed_2598_, v_i_boxed_2599_, v_b_2592_, v___y_2593_, v___y_2594_, v___y_2595_, v___y_2596_);
    leanh::lean_dec(v___y_2596_);
    leanh::lean_dec_ref(v___y_2595_);
    leanh::lean_dec(v___y_2594_);
    leanh::lean_dec_ref(v___y_2593_);
    leanh::lean_dec_ref(v_as_2589_);
    return v_res_2600_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Conv_Pattern_0__Lean_Elab_Tactic_Conv_pre(
    mut v_pattern_2603_: *mut leanh::LeanObject,
    mut v_state_2604_: *mut leanh::LeanObject,
    mut v_e_2605_: *mut leanh::LeanObject,
    mut v_a_2606_: *mut leanh::LeanObject,
    mut v_a_2607_: *mut leanh::LeanObject,
    mut v_a_2608_: *mut leanh::LeanObject,
    mut v_a_2609_: *mut leanh::LeanObject,
    mut v_a_2610_: *mut leanh::LeanObject,
    mut v_a_2611_: *mut leanh::LeanObject,
    mut v_a_2612_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2614_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2615_: u8 = 0;
    let mut v___x_2616_: u8 = 0;
    let mut v___x_2617_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2618_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2620_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2621_: u8 = 0;
    let mut v_val_2622_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2624_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2625_: u8 = 0;
    let mut v_fst_2626_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2627_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2628_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2629_: u8 = 0;
    let mut v___x_2630_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2631_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2632_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2633_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2635_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2636_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2637_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2638_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2639_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_2640_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2641_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2642_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2643_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2644_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2645_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_2646_: usize = 0;
    let mut v___x_2647_: usize = 0;
    let mut v___x_2648_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2649_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2651_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2652_: u8 = 0;
    let mut v___x_2653_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2655_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2656_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2657_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2659_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2660_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2661_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2662_: u8 = 0;
    let mut v_a_2663_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2665_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2666_: u8 = 0;
    let mut v___x_2668_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2669_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2670_: u8 = 0;
    let mut v_a_2671_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2673_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2674_: u8 = 0;
    let mut v___x_2676_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2677_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2678_: u8 = 0;
    let mut v_isSharedCheck_2679_: u8 = 0;
    let mut v___x_2680_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2682_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2683_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2684_: u8 = 0;
    let mut v_a_2685_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2687_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2688_: u8 = 0;
    let mut v___x_2690_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2691_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2692_: u8 = 0;
    let mut v___x_2693_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2694_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2695_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2696_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2614_ = lean_st_ref_get(v_state_2604_);
                v___x_2615_ = l_Lean_Elab_Tactic_Conv_PatternMatchState_isDone(v___x_2614_);
                leanh::lean_dec(v___x_2614_);
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
                    if leanh::lean_obj_tag(v___x_2617_) == 0 {
                        v_a_2618_ = leanh::lean_ctor_get(v___x_2617_, 0);
                        v_isSharedCheck_2684_ =
                            (!leanh::lean_is_exclusive(v___x_2617_)) as u8;
                        if v_isSharedCheck_2684_ == 0 {
                            v___x_2620_ = v___x_2617_;
                            v_isShared_2621_ = v_isSharedCheck_2684_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_2618_);
                            leanh::lean_dec(v___x_2617_);
                            v___x_2620_ = leanh::lean_box(0);
                            v_isShared_2621_ = v_isSharedCheck_2684_;
                            state = 1;
                            continue;
                        }
                    } else {
                        v_a_2685_ = leanh::lean_ctor_get(v___x_2617_, 0);
                        v_isSharedCheck_2692_ =
                            (!leanh::lean_is_exclusive(v___x_2617_)) as u8;
                        if v_isSharedCheck_2692_ == 0 {
                            v___x_2687_ = v___x_2617_;
                            v_isShared_2688_ = v_isSharedCheck_2692_;
                            state = 12;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_2685_);
                            leanh::lean_dec(v___x_2617_);
                            v___x_2687_ = leanh::lean_box(0);
                            v_isShared_2688_ = v_isSharedCheck_2692_;
                            state = 12;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_dec_ref(v_pattern_2603_);
                    v___x_2693_ = leanh::lean_box(0);
                    v___x_2694_ = leanh::lean_alloc_ctor(0, 2, (1) as u32);
                    leanh::lean_ctor_set(v___x_2694_, 0, v_e_2605_);
                    leanh::lean_ctor_set(v___x_2694_, 1, v___x_2693_);
                    leanh::lean_ctor_set_uint8(
                        v___x_2694_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 2) as u32,
                        v___x_2616_,
                    );
                    v___x_2695_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_2695_, 0, v___x_2694_);
                    v___x_2696_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_2696_, 0, v___x_2695_);
                    return v___x_2696_;
                }
            }
            1 => {
                if leanh::lean_obj_tag(v_a_2618_) == 1 {
                    v_val_2622_ = leanh::lean_ctor_get(v_a_2618_, 0);
                    v_isSharedCheck_2679_ = (!leanh::lean_is_exclusive(v_a_2618_)) as u8;
                    if v_isSharedCheck_2679_ == 0 {
                        v___x_2624_ = v_a_2618_;
                        v_isShared_2625_ = v_isSharedCheck_2679_;
                        state = 2;
                        continue;
                    } else {
                        leanh::lean_inc(v_val_2622_);
                        leanh::lean_dec(v_a_2618_);
                        v___x_2624_ = leanh::lean_box(0);
                        v_isShared_2625_ = v_isSharedCheck_2679_;
                        state = 2;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v_a_2618_);
                    v___x_2680_ = l___private_Lean_Elab_Tactic_Conv_Pattern_0__Lean_Elab_Tactic_Conv_pre___closed__0;
                    if v_isShared_2621_ == 0 {
                        leanh::lean_ctor_set(v___x_2620_, 0, v___x_2680_);
                        v___x_2682_ = v___x_2620_;
                        state = 11;
                        continue;
                    } else {
                        v_reuseFailAlloc_2683_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2683_, 0, v___x_2680_);
                        v___x_2682_ = v_reuseFailAlloc_2683_;
                        state = 11;
                        continue;
                    }
                }
            }
            2 => {
                v_fst_2626_ = leanh::lean_ctor_get(v_val_2622_, 0);
                leanh::lean_inc(v_fst_2626_);
                v_snd_2627_ = leanh::lean_ctor_get(v_val_2622_, 1);
                leanh::lean_inc(v_snd_2627_);
                leanh::lean_dec(v_val_2622_);
                v___x_2628_ = lean_st_ref_get(v_state_2604_);
                v___x_2629_ = l_Lean_Elab_Tactic_Conv_PatternMatchState_isReady(v___x_2628_);
                leanh::lean_dec(v___x_2628_);
                if v___x_2629_ == 0 {
                    leanh::lean_dec(v_snd_2627_);
                    leanh::lean_dec(v_fst_2626_);
                    leanh::lean_del_object(v___x_2624_);
                    v___x_2630_ = lean_st_ref_take(v_state_2604_);
                    v___x_2631_ = l_Lean_Elab_Tactic_Conv_PatternMatchState_skip(v___x_2630_);
                    v___x_2632_ = lean_st_ref_set(v_state_2604_, v___x_2631_);
                    v___x_2633_ = l___private_Lean_Elab_Tactic_Conv_Pattern_0__Lean_Elab_Tactic_Conv_pre___closed__0;
                    if v_isShared_2621_ == 0 {
                        leanh::lean_ctor_set(v___x_2620_, 0, v___x_2633_);
                        v___x_2635_ = v___x_2620_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_2636_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2636_, 0, v___x_2633_);
                        v___x_2635_ = v_reuseFailAlloc_2636_;
                        state = 3;
                        continue;
                    }
                } else {
                    leanh::lean_del_object(v___x_2620_);
                    v___x_2637_ = leanh::lean_box(0);
                    v___x_2638_ = l_Lean_Elab_Tactic_Conv_mkConvGoalFor(
                        v_fst_2626_,
                        v___x_2637_,
                        v_a_2609_,
                        v_a_2610_,
                        v_a_2611_,
                        v_a_2612_,
                    );
                    if leanh::lean_obj_tag(v___x_2638_) == 0 {
                        v_a_2639_ = leanh::lean_ctor_get(v___x_2638_, 0);
                        leanh::lean_inc(v_a_2639_);
                        leanh::lean_dec_ref_known(v___x_2638_, 1);
                        v_fst_2640_ = leanh::lean_ctor_get(v_a_2639_, 0);
                        leanh::lean_inc(v_fst_2640_);
                        v_snd_2641_ = leanh::lean_ctor_get(v_a_2639_, 1);
                        leanh::lean_inc(v_snd_2641_);
                        leanh::lean_dec(v_a_2639_);
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
                        if leanh::lean_obj_tag(v___x_2648_) == 0 {
                            v_a_2649_ = leanh::lean_ctor_get(v___x_2648_, 0);
                            v_isSharedCheck_2662_ =
                                (!leanh::lean_is_exclusive(v___x_2648_)) as u8;
                            if v_isSharedCheck_2662_ == 0 {
                                v___x_2651_ = v___x_2648_;
                                v_isShared_2652_ = v_isSharedCheck_2662_;
                                state = 4;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_2649_);
                                leanh::lean_dec(v___x_2648_);
                                v___x_2651_ = leanh::lean_box(0);
                                v_isShared_2652_ = v_isSharedCheck_2662_;
                                state = 4;
                                continue;
                            }
                        } else {
                            leanh::lean_dec(v_fst_2640_);
                            leanh::lean_dec(v_snd_2627_);
                            leanh::lean_del_object(v___x_2624_);
                            v_a_2663_ = leanh::lean_ctor_get(v___x_2648_, 0);
                            v_isSharedCheck_2670_ =
                                (!leanh::lean_is_exclusive(v___x_2648_)) as u8;
                            if v_isSharedCheck_2670_ == 0 {
                                v___x_2665_ = v___x_2648_;
                                v_isShared_2666_ = v_isSharedCheck_2670_;
                                state = 7;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_2663_);
                                leanh::lean_dec(v___x_2648_);
                                v___x_2665_ = leanh::lean_box(0);
                                v_isShared_2666_ = v_isSharedCheck_2670_;
                                state = 7;
                                continue;
                            }
                        }
                    } else {
                        leanh::lean_dec(v_snd_2627_);
                        leanh::lean_del_object(v___x_2624_);
                        v_a_2671_ = leanh::lean_ctor_get(v___x_2638_, 0);
                        v_isSharedCheck_2678_ =
                            (!leanh::lean_is_exclusive(v___x_2638_)) as u8;
                        if v_isSharedCheck_2678_ == 0 {
                            v___x_2673_ = v___x_2638_;
                            v_isShared_2674_ = v_isSharedCheck_2678_;
                            state = 9;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_2671_);
                            leanh::lean_dec(v___x_2638_);
                            v___x_2673_ = leanh::lean_box(0);
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
                leanh::lean_dec(v_snd_2627_);
                if v_isShared_2625_ == 0 {
                    leanh::lean_ctor_set(v___x_2624_, 0, v_a_2649_);
                    v___x_2655_ = v___x_2624_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_2661_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2661_, 0, v_a_2649_);
                    v___x_2655_ = v_reuseFailAlloc_2661_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v___x_2656_ = leanh::lean_alloc_ctor(0, 2, (1) as u32);
                leanh::lean_ctor_set(v___x_2656_, 0, v___x_2653_);
                leanh::lean_ctor_set(v___x_2656_, 1, v___x_2655_);
                leanh::lean_ctor_set_uint8(
                    v___x_2656_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 2) as u32,
                    v___x_2616_,
                );
                v___x_2657_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_2657_, 0, v___x_2656_);
                if v_isShared_2652_ == 0 {
                    leanh::lean_ctor_set(v___x_2651_, 0, v___x_2657_);
                    v___x_2659_ = v___x_2651_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_2660_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2660_, 0, v___x_2657_);
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
                    v_reuseFailAlloc_2669_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2669_, 0, v_a_2663_);
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
                    v_reuseFailAlloc_2677_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2677_, 0, v_a_2671_);
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
                    v_reuseFailAlloc_2691_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2691_, 0, v_a_2685_);
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
    mut v_pattern_2697_: *mut leanh::LeanObject,
    mut v_state_2698_: *mut leanh::LeanObject,
    mut v_e_2699_: *mut leanh::LeanObject,
    mut v_a_2700_: *mut leanh::LeanObject,
    mut v_a_2701_: *mut leanh::LeanObject,
    mut v_a_2702_: *mut leanh::LeanObject,
    mut v_a_2703_: *mut leanh::LeanObject,
    mut v_a_2704_: *mut leanh::LeanObject,
    mut v_a_2705_: *mut leanh::LeanObject,
    mut v_a_2706_: *mut leanh::LeanObject,
    mut v_a_2707_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2708_: *mut leanh::LeanObject = core::ptr::null_mut();
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
    leanh::lean_dec(v_a_2706_);
    leanh::lean_dec_ref(v_a_2705_);
    leanh::lean_dec(v_a_2704_);
    leanh::lean_dec_ref(v_a_2703_);
    leanh::lean_dec(v_a_2702_);
    leanh::lean_dec_ref(v_a_2701_);
    leanh::lean_dec(v_a_2700_);
    leanh::lean_dec(v_state_2698_);
    return v_res_2708_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Conv_Pattern_0__Lean_Elab_Tactic_Conv_pre_spec__0(
    mut v_as_2709_: *mut leanh::LeanObject,
    mut v_sz_2710_: usize,
    mut v_i_2711_: usize,
    mut v_b_2712_: *mut leanh::LeanObject,
    mut v___y_2713_: *mut leanh::LeanObject,
    mut v___y_2714_: *mut leanh::LeanObject,
    mut v___y_2715_: *mut leanh::LeanObject,
    mut v___y_2716_: *mut leanh::LeanObject,
    mut v___y_2717_: *mut leanh::LeanObject,
    mut v___y_2718_: *mut leanh::LeanObject,
    mut v___y_2719_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2721_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2721_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Conv_Pattern_0__Lean_Elab_Tactic_Conv_pre_spec__0___redArg(v_as_2709_, v_sz_2710_, v_i_2711_, v_b_2712_, v___y_2716_, v___y_2717_, v___y_2718_, v___y_2719_);
    return v___x_2721_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Conv_Pattern_0__Lean_Elab_Tactic_Conv_pre_spec__0___boxed(
    mut v_as_2722_: *mut leanh::LeanObject,
    mut v_sz_2723_: *mut leanh::LeanObject,
    mut v_i_2724_: *mut leanh::LeanObject,
    mut v_b_2725_: *mut leanh::LeanObject,
    mut v___y_2726_: *mut leanh::LeanObject,
    mut v___y_2727_: *mut leanh::LeanObject,
    mut v___y_2728_: *mut leanh::LeanObject,
    mut v___y_2729_: *mut leanh::LeanObject,
    mut v___y_2730_: *mut leanh::LeanObject,
    mut v___y_2731_: *mut leanh::LeanObject,
    mut v___y_2732_: *mut leanh::LeanObject,
    mut v___y_2733_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_sz_boxed_2734_: usize = 0;
    let mut v_i_boxed_2735_: usize = 0;
    let mut v_res_2736_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_2734_ = leanh::lean_unbox_usize(v_sz_2723_);
    leanh::lean_dec(v_sz_2723_);
    v_i_boxed_2735_ = leanh::lean_unbox_usize(v_i_2724_);
    leanh::lean_dec(v_i_2724_);
    v_res_2736_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Conv_Pattern_0__Lean_Elab_Tactic_Conv_pre_spec__0(v_as_2722_, v_sz_boxed_2734_, v_i_boxed_2735_, v_b_2725_, v___y_2726_, v___y_2727_, v___y_2728_, v___y_2729_, v___y_2730_, v___y_2731_, v___y_2732_);
    leanh::lean_dec(v___y_2732_);
    leanh::lean_dec_ref(v___y_2731_);
    leanh::lean_dec(v___y_2730_);
    leanh::lean_dec_ref(v___y_2729_);
    leanh::lean_dec(v___y_2728_);
    leanh::lean_dec_ref(v___y_2727_);
    leanh::lean_dec(v___y_2726_);
    leanh::lean_dec_ref(v_as_2722_);
    return v_res_2736_;
}
pub unsafe fn _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__0___redArg___closed__0()
-> *mut leanh::LeanObject {
    let mut v___x_2737_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2738_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2739_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2737_ = leanh::lean_box(0);
    v___x_2738_ = l_Lean_Elab_unsupportedSyntaxExceptionId;
    v___x_2739_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_2739_, 0, v___x_2738_);
    leanh::lean_ctor_set(v___x_2739_, 1, v___x_2737_);
    return v___x_2739_;
}
pub unsafe fn l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__0___redArg()
-> *mut leanh::LeanObject {
    let mut v___x_2741_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2742_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2741_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__0___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__0___redArg___closed__0_once), _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__0___redArg___closed__0);
    v___x_2742_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_2742_, 0, v___x_2741_);
    return v___x_2742_;
}
pub unsafe fn l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__0___redArg___boxed(
    mut v___y_2743_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2744_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2744_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__0___redArg();
    return v_res_2744_;
}
pub unsafe fn l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__0(
    mut v_00_u03b1_2745_: *mut leanh::LeanObject,
    mut v___y_2746_: *mut leanh::LeanObject,
    mut v___y_2747_: *mut leanh::LeanObject,
    mut v___y_2748_: *mut leanh::LeanObject,
    mut v___y_2749_: *mut leanh::LeanObject,
    mut v___y_2750_: *mut leanh::LeanObject,
    mut v___y_2751_: *mut leanh::LeanObject,
    mut v___y_2752_: *mut leanh::LeanObject,
    mut v___y_2753_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2755_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2755_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__0___redArg();
    return v___x_2755_;
}
pub unsafe fn l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__0___boxed(
    mut v_00_u03b1_2756_: *mut leanh::LeanObject,
    mut v___y_2757_: *mut leanh::LeanObject,
    mut v___y_2758_: *mut leanh::LeanObject,
    mut v___y_2759_: *mut leanh::LeanObject,
    mut v___y_2760_: *mut leanh::LeanObject,
    mut v___y_2761_: *mut leanh::LeanObject,
    mut v___y_2762_: *mut leanh::LeanObject,
    mut v___y_2763_: *mut leanh::LeanObject,
    mut v___y_2764_: *mut leanh::LeanObject,
    mut v___y_2765_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2766_: *mut leanh::LeanObject = core::ptr::null_mut();
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
    leanh::lean_dec(v___y_2764_);
    leanh::lean_dec_ref(v___y_2763_);
    leanh::lean_dec(v___y_2762_);
    leanh::lean_dec_ref(v___y_2761_);
    leanh::lean_dec(v___y_2760_);
    leanh::lean_dec_ref(v___y_2759_);
    leanh::lean_dec(v___y_2758_);
    leanh::lean_dec_ref(v___y_2757_);
    return v_res_2766_;
}
pub unsafe fn l_Lean_Elab_Term_withoutErrToSorry___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__2___redArg(
    mut v_a_2767_: *mut leanh::LeanObject,
    mut v___y_2768_: *mut leanh::LeanObject,
    mut v___y_2769_: *mut leanh::LeanObject,
    mut v___y_2770_: *mut leanh::LeanObject,
    mut v___y_2771_: *mut leanh::LeanObject,
    mut v___y_2772_: *mut leanh::LeanObject,
    mut v___y_2773_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2775_: *mut leanh::LeanObject = core::ptr::null_mut();
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
    mut v_a_2776_: *mut leanh::LeanObject,
    mut v___y_2777_: *mut leanh::LeanObject,
    mut v___y_2778_: *mut leanh::LeanObject,
    mut v___y_2779_: *mut leanh::LeanObject,
    mut v___y_2780_: *mut leanh::LeanObject,
    mut v___y_2781_: *mut leanh::LeanObject,
    mut v___y_2782_: *mut leanh::LeanObject,
    mut v___y_2783_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2784_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2784_ = l_Lean_Elab_Term_withoutErrToSorry___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__2___redArg(v_a_2776_, v___y_2777_, v___y_2778_, v___y_2779_, v___y_2780_, v___y_2781_, v___y_2782_);
    leanh::lean_dec(v___y_2782_);
    leanh::lean_dec_ref(v___y_2781_);
    leanh::lean_dec(v___y_2780_);
    leanh::lean_dec_ref(v___y_2779_);
    leanh::lean_dec(v___y_2778_);
    leanh::lean_dec_ref(v___y_2777_);
    return v_res_2784_;
}
pub unsafe fn l_Lean_Elab_Term_withoutErrToSorry___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__2(
    mut v_00_u03b1_2785_: *mut leanh::LeanObject,
    mut v_a_2786_: *mut leanh::LeanObject,
    mut v___y_2787_: *mut leanh::LeanObject,
    mut v___y_2788_: *mut leanh::LeanObject,
    mut v___y_2789_: *mut leanh::LeanObject,
    mut v___y_2790_: *mut leanh::LeanObject,
    mut v___y_2791_: *mut leanh::LeanObject,
    mut v___y_2792_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2794_: *mut leanh::LeanObject = core::ptr::null_mut();
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
    mut v_00_u03b1_2795_: *mut leanh::LeanObject,
    mut v_a_2796_: *mut leanh::LeanObject,
    mut v___y_2797_: *mut leanh::LeanObject,
    mut v___y_2798_: *mut leanh::LeanObject,
    mut v___y_2799_: *mut leanh::LeanObject,
    mut v___y_2800_: *mut leanh::LeanObject,
    mut v___y_2801_: *mut leanh::LeanObject,
    mut v___y_2802_: *mut leanh::LeanObject,
    mut v___y_2803_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2804_: *mut leanh::LeanObject = core::ptr::null_mut();
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
    leanh::lean_dec(v___y_2802_);
    leanh::lean_dec_ref(v___y_2801_);
    leanh::lean_dec(v___y_2800_);
    leanh::lean_dec_ref(v___y_2799_);
    leanh::lean_dec(v___y_2798_);
    leanh::lean_dec_ref(v___y_2797_);
    return v_res_2804_;
}
pub unsafe fn l_Lean_Elab_Tactic_Conv_evalPattern___lam__0(
    mut v_e_2805_: *mut leanh::LeanObject,
    mut v___y_2806_: *mut leanh::LeanObject,
    mut v___y_2807_: *mut leanh::LeanObject,
    mut v___y_2808_: *mut leanh::LeanObject,
    mut v___y_2809_: *mut leanh::LeanObject,
    mut v___y_2810_: *mut leanh::LeanObject,
    mut v___y_2811_: *mut leanh::LeanObject,
    mut v___y_2812_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2814_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2815_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2814_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_2814_, 0, v_e_2805_);
    v___x_2815_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_2815_, 0, v___x_2814_);
    return v___x_2815_;
}
pub unsafe fn l_Lean_Elab_Tactic_Conv_evalPattern___lam__0___boxed(
    mut v_e_2816_: *mut leanh::LeanObject,
    mut v___y_2817_: *mut leanh::LeanObject,
    mut v___y_2818_: *mut leanh::LeanObject,
    mut v___y_2819_: *mut leanh::LeanObject,
    mut v___y_2820_: *mut leanh::LeanObject,
    mut v___y_2821_: *mut leanh::LeanObject,
    mut v___y_2822_: *mut leanh::LeanObject,
    mut v___y_2823_: *mut leanh::LeanObject,
    mut v___y_2824_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2825_: *mut leanh::LeanObject = core::ptr::null_mut();
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
    leanh::lean_dec(v___y_2823_);
    leanh::lean_dec_ref(v___y_2822_);
    leanh::lean_dec(v___y_2821_);
    leanh::lean_dec_ref(v___y_2820_);
    leanh::lean_dec(v___y_2819_);
    leanh::lean_dec_ref(v___y_2818_);
    leanh::lean_dec(v___y_2817_);
    return v_res_2825_;
}
pub unsafe fn l_Lean_Elab_Tactic_Conv_evalPattern___lam__1(
    mut v___x_2826_: *mut leanh::LeanObject,
    mut v___x_2827_: *mut leanh::LeanObject,
    mut v___x_2828_: u8,
    mut v___y_2829_: *mut leanh::LeanObject,
    mut v___y_2830_: *mut leanh::LeanObject,
    mut v___y_2831_: *mut leanh::LeanObject,
    mut v___y_2832_: *mut leanh::LeanObject,
    mut v___y_2833_: *mut leanh::LeanObject,
    mut v___y_2834_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2836_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2837_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2838_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2839_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2841_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2842_: u8 = 0;
    let mut v___x_2844_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2845_: *mut leanh::LeanObject = core::ptr::null_mut();
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
                if leanh::lean_obj_tag(v___x_2836_) == 0 {
                    v_a_2837_ = leanh::lean_ctor_get(v___x_2836_, 0);
                    leanh::lean_inc(v_a_2837_);
                    leanh::lean_dec_ref_known(v___x_2836_, 1);
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
                    v_a_2839_ = leanh::lean_ctor_get(v___x_2836_, 0);
                    v_isSharedCheck_2846_ = (!leanh::lean_is_exclusive(v___x_2836_)) as u8;
                    if v_isSharedCheck_2846_ == 0 {
                        v___x_2841_ = v___x_2836_;
                        v_isShared_2842_ = v_isSharedCheck_2846_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_2839_);
                        leanh::lean_dec(v___x_2836_);
                        v___x_2841_ = leanh::lean_box(0);
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
                    v_reuseFailAlloc_2845_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2845_, 0, v_a_2839_);
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
    mut v___x_2847_: *mut leanh::LeanObject,
    mut v___x_2848_: *mut leanh::LeanObject,
    mut v___x_2849_: *mut leanh::LeanObject,
    mut v___y_2850_: *mut leanh::LeanObject,
    mut v___y_2851_: *mut leanh::LeanObject,
    mut v___y_2852_: *mut leanh::LeanObject,
    mut v___y_2853_: *mut leanh::LeanObject,
    mut v___y_2854_: *mut leanh::LeanObject,
    mut v___y_2855_: *mut leanh::LeanObject,
    mut v___y_2856_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_18448__boxed_2857_: u8 = 0;
    let mut v_res_2858_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_18448__boxed_2857_ = (leanh::lean_unbox(v___x_2849_) as u8);
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
    leanh::lean_dec(v___y_2855_);
    leanh::lean_dec_ref(v___y_2854_);
    leanh::lean_dec(v___y_2853_);
    leanh::lean_dec_ref(v___y_2852_);
    leanh::lean_dec(v___y_2851_);
    leanh::lean_dec_ref(v___y_2850_);
    return v_res_2858_;
}
pub unsafe fn l_Lean_Elab_Tactic_Conv_evalPattern___lam__2(
    mut v___x_2859_: *mut leanh::LeanObject,
    mut v___f_2860_: *mut leanh::LeanObject,
    mut v___y_2861_: *mut leanh::LeanObject,
    mut v___y_2862_: *mut leanh::LeanObject,
    mut v___y_2863_: *mut leanh::LeanObject,
    mut v___y_2864_: *mut leanh::LeanObject,
    mut v___y_2865_: *mut leanh::LeanObject,
    mut v___y_2866_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_fileName_2868_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fileMap_2869_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_2870_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_currRecDepth_2871_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_maxRecDepth_2872_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_2873_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_currNamespace_2874_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_openDecls_2875_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_initHeartbeats_2876_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_maxHeartbeats_2877_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_quotContext_2878_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_currMacroScope_2879_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_diag_2880_: u8 = 0;
    let mut v_cancelTk_x3f_2881_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_suppressElabErrors_2882_: u8 = 0;
    let mut v_inheritedTraceOptions_2883_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2885_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2886_: u8 = 0;
    let mut v_ref_2887_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2889_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2890_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2891_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2892_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_fileName_2868_ = leanh::lean_ctor_get(v___y_2865_, 0);
                v_fileMap_2869_ = leanh::lean_ctor_get(v___y_2865_, 1);
                v_options_2870_ = leanh::lean_ctor_get(v___y_2865_, 2);
                v_currRecDepth_2871_ = leanh::lean_ctor_get(v___y_2865_, 3);
                v_maxRecDepth_2872_ = leanh::lean_ctor_get(v___y_2865_, 4);
                v_ref_2873_ = leanh::lean_ctor_get(v___y_2865_, 5);
                v_currNamespace_2874_ = leanh::lean_ctor_get(v___y_2865_, 6);
                v_openDecls_2875_ = leanh::lean_ctor_get(v___y_2865_, 7);
                v_initHeartbeats_2876_ = leanh::lean_ctor_get(v___y_2865_, 8);
                v_maxHeartbeats_2877_ = leanh::lean_ctor_get(v___y_2865_, 9);
                v_quotContext_2878_ = leanh::lean_ctor_get(v___y_2865_, 10);
                v_currMacroScope_2879_ = leanh::lean_ctor_get(v___y_2865_, 11);
                v_diag_2880_ = leanh::lean_ctor_get_uint8(
                    v___y_2865_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 14) as u32,
                );
                v_cancelTk_x3f_2881_ = leanh::lean_ctor_get(v___y_2865_, 12);
                v_suppressElabErrors_2882_ = leanh::lean_ctor_get_uint8(
                    v___y_2865_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 14 + 1) as u32,
                );
                v_inheritedTraceOptions_2883_ = leanh::lean_ctor_get(v___y_2865_, 13);
                v_isSharedCheck_2892_ = (!leanh::lean_is_exclusive(v___y_2865_)) as u8;
                if v_isSharedCheck_2892_ == 0 {
                    v___x_2885_ = v___y_2865_;
                    v_isShared_2886_ = v_isSharedCheck_2892_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_inheritedTraceOptions_2883_);
                    leanh::lean_inc(v_cancelTk_x3f_2881_);
                    leanh::lean_inc(v_currMacroScope_2879_);
                    leanh::lean_inc(v_quotContext_2878_);
                    leanh::lean_inc(v_maxHeartbeats_2877_);
                    leanh::lean_inc(v_initHeartbeats_2876_);
                    leanh::lean_inc(v_openDecls_2875_);
                    leanh::lean_inc(v_currNamespace_2874_);
                    leanh::lean_inc(v_ref_2873_);
                    leanh::lean_inc(v_maxRecDepth_2872_);
                    leanh::lean_inc(v_currRecDepth_2871_);
                    leanh::lean_inc(v_options_2870_);
                    leanh::lean_inc(v_fileMap_2869_);
                    leanh::lean_inc(v_fileName_2868_);
                    leanh::lean_dec(v___y_2865_);
                    v___x_2885_ = leanh::lean_box(0);
                    v_isShared_2886_ = v_isSharedCheck_2892_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_ref_2887_ = l_Lean_replaceRef(v___x_2859_, v_ref_2873_);
                leanh::lean_dec(v_ref_2873_);
                if v_isShared_2886_ == 0 {
                    leanh::lean_ctor_set(v___x_2885_, 5, v_ref_2887_);
                    v___x_2889_ = v___x_2885_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2891_ = leanh::lean_alloc_ctor(0, 14, (2) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2891_, 0, v_fileName_2868_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2891_, 1, v_fileMap_2869_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2891_, 2, v_options_2870_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2891_, 3, v_currRecDepth_2871_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2891_, 4, v_maxRecDepth_2872_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2891_, 5, v_ref_2887_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2891_, 6, v_currNamespace_2874_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2891_, 7, v_openDecls_2875_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2891_, 8, v_initHeartbeats_2876_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2891_, 9, v_maxHeartbeats_2877_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2891_, 10, v_quotContext_2878_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2891_, 11, v_currMacroScope_2879_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2891_, 12, v_cancelTk_x3f_2881_);
                    leanh::lean_ctor_set(
                        v_reuseFailAlloc_2891_,
                        13,
                        v_inheritedTraceOptions_2883_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_2891_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 14) as u32,
                        v_diag_2880_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_2891_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 14 + 1) as u32,
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
                leanh::lean_dec_ref(v___x_2889_);
                return v___x_2890_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_Tactic_Conv_evalPattern___lam__2___boxed(
    mut v___x_2893_: *mut leanh::LeanObject,
    mut v___f_2894_: *mut leanh::LeanObject,
    mut v___y_2895_: *mut leanh::LeanObject,
    mut v___y_2896_: *mut leanh::LeanObject,
    mut v___y_2897_: *mut leanh::LeanObject,
    mut v___y_2898_: *mut leanh::LeanObject,
    mut v___y_2899_: *mut leanh::LeanObject,
    mut v___y_2900_: *mut leanh::LeanObject,
    mut v___y_2901_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2902_: *mut leanh::LeanObject = core::ptr::null_mut();
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
    leanh::lean_dec(v___y_2900_);
    leanh::lean_dec(v___y_2898_);
    leanh::lean_dec_ref(v___y_2897_);
    leanh::lean_dec(v___y_2896_);
    leanh::lean_dec_ref(v___y_2895_);
    leanh::lean_dec(v___x_2893_);
    return v_res_2902_;
}
pub unsafe fn l_Lean_Elab_Tactic_Conv_evalPattern___lam__3(
    mut v___x_2903_: *mut leanh::LeanObject,
    mut v___x_2904_: u8,
    mut v_e_2905_: *mut leanh::LeanObject,
    mut v___y_2906_: *mut leanh::LeanObject,
    mut v___y_2907_: *mut leanh::LeanObject,
    mut v___y_2908_: *mut leanh::LeanObject,
    mut v___y_2909_: *mut leanh::LeanObject,
    mut v___y_2910_: *mut leanh::LeanObject,
    mut v___y_2911_: *mut leanh::LeanObject,
    mut v___y_2912_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2914_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2915_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2916_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2914_ = leanh::lean_alloc_ctor(0, 2, (1) as u32);
    leanh::lean_ctor_set(v___x_2914_, 0, v_e_2905_);
    leanh::lean_ctor_set(v___x_2914_, 1, v___x_2903_);
    leanh::lean_ctor_set_uint8(
        v___x_2914_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 2) as u32,
        v___x_2904_,
    );
    v___x_2915_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_2915_, 0, v___x_2914_);
    v___x_2916_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_2916_, 0, v___x_2915_);
    return v___x_2916_;
}
pub unsafe fn l_Lean_Elab_Tactic_Conv_evalPattern___lam__3___boxed(
    mut v___x_2917_: *mut leanh::LeanObject,
    mut v___x_2918_: *mut leanh::LeanObject,
    mut v_e_2919_: *mut leanh::LeanObject,
    mut v___y_2920_: *mut leanh::LeanObject,
    mut v___y_2921_: *mut leanh::LeanObject,
    mut v___y_2922_: *mut leanh::LeanObject,
    mut v___y_2923_: *mut leanh::LeanObject,
    mut v___y_2924_: *mut leanh::LeanObject,
    mut v___y_2925_: *mut leanh::LeanObject,
    mut v___y_2926_: *mut leanh::LeanObject,
    mut v___y_2927_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_18542__boxed_2928_: u8 = 0;
    let mut v_res_2929_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_18542__boxed_2928_ = (leanh::lean_unbox(v___x_2918_) as u8);
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
    leanh::lean_dec(v___y_2926_);
    leanh::lean_dec_ref(v___y_2925_);
    leanh::lean_dec(v___y_2924_);
    leanh::lean_dec_ref(v___y_2923_);
    leanh::lean_dec(v___y_2922_);
    leanh::lean_dec_ref(v___y_2921_);
    leanh::lean_dec(v___y_2920_);
    return v_res_2929_;
}
pub unsafe fn l_Lean_Elab_Tactic_Conv_evalPattern___lam__4(
    mut v___x_2930_: *mut leanh::LeanObject,
    mut v_x_2931_: *mut leanh::LeanObject,
    mut v___y_2932_: *mut leanh::LeanObject,
    mut v___y_2933_: *mut leanh::LeanObject,
    mut v___y_2934_: *mut leanh::LeanObject,
    mut v___y_2935_: *mut leanh::LeanObject,
    mut v___y_2936_: *mut leanh::LeanObject,
    mut v___y_2937_: *mut leanh::LeanObject,
    mut v___y_2938_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2940_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2941_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2940_ = leanh::lean_alloc_ctor(2, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_2940_, 0, v___x_2930_);
    v___x_2941_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_2941_, 0, v___x_2940_);
    return v___x_2941_;
}
pub unsafe fn l_Lean_Elab_Tactic_Conv_evalPattern___lam__4___boxed(
    mut v___x_2942_: *mut leanh::LeanObject,
    mut v_x_2943_: *mut leanh::LeanObject,
    mut v___y_2944_: *mut leanh::LeanObject,
    mut v___y_2945_: *mut leanh::LeanObject,
    mut v___y_2946_: *mut leanh::LeanObject,
    mut v___y_2947_: *mut leanh::LeanObject,
    mut v___y_2948_: *mut leanh::LeanObject,
    mut v___y_2949_: *mut leanh::LeanObject,
    mut v___y_2950_: *mut leanh::LeanObject,
    mut v___y_2951_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2952_: *mut leanh::LeanObject = core::ptr::null_mut();
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
    leanh::lean_dec(v___y_2950_);
    leanh::lean_dec_ref(v___y_2949_);
    leanh::lean_dec(v___y_2948_);
    leanh::lean_dec_ref(v___y_2947_);
    leanh::lean_dec(v___y_2946_);
    leanh::lean_dec_ref(v___y_2945_);
    leanh::lean_dec(v___y_2944_);
    leanh::lean_dec_ref(v_x_2943_);
    return v_res_2952_;
}
pub unsafe fn l_Lean_Elab_Tactic_Conv_evalPattern___lam__5(
    mut v___x_2953_: *mut leanh::LeanObject,
    mut v_x_2954_: *mut leanh::LeanObject,
    mut v___y_2955_: *mut leanh::LeanObject,
    mut v___y_2956_: *mut leanh::LeanObject,
    mut v___y_2957_: *mut leanh::LeanObject,
    mut v___y_2958_: *mut leanh::LeanObject,
    mut v___y_2959_: *mut leanh::LeanObject,
    mut v___y_2960_: *mut leanh::LeanObject,
    mut v___y_2961_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2963_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2963_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_2963_, 0, v___x_2953_);
    return v___x_2963_;
}
pub unsafe fn l_Lean_Elab_Tactic_Conv_evalPattern___lam__5___boxed(
    mut v___x_2964_: *mut leanh::LeanObject,
    mut v_x_2965_: *mut leanh::LeanObject,
    mut v___y_2966_: *mut leanh::LeanObject,
    mut v___y_2967_: *mut leanh::LeanObject,
    mut v___y_2968_: *mut leanh::LeanObject,
    mut v___y_2969_: *mut leanh::LeanObject,
    mut v___y_2970_: *mut leanh::LeanObject,
    mut v___y_2971_: *mut leanh::LeanObject,
    mut v___y_2972_: *mut leanh::LeanObject,
    mut v___y_2973_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2974_: *mut leanh::LeanObject = core::ptr::null_mut();
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
    leanh::lean_dec(v___y_2972_);
    leanh::lean_dec_ref(v___y_2971_);
    leanh::lean_dec(v___y_2970_);
    leanh::lean_dec_ref(v___y_2969_);
    leanh::lean_dec(v___y_2968_);
    leanh::lean_dec_ref(v___y_2967_);
    leanh::lean_dec(v___y_2966_);
    leanh::lean_dec_ref(v_x_2965_);
    return v_res_2974_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__5(
    mut v_sz_2975_: usize,
    mut v_i_2976_: usize,
    mut v_bs_2977_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2978_: u8 = 0;
    let mut v_v_2979_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2980_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2981_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_2982_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2983_: usize = 0;
    let mut v___x_2984_: usize = 0;
    let mut v___x_2985_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2978_ = lean_usize_dec_lt(v_i_2976_, v_sz_2975_);
                if v___x_2978_ == 0 {
                    return v_bs_2977_;
                } else {
                    v_v_2979_ = lean_array_uget_borrowed(v_bs_2977_, v_i_2976_);
                    v_snd_2980_ = leanh::lean_ctor_get(v_v_2979_, 1);
                    leanh::lean_inc(v_snd_2980_);
                    v___x_2981_ = leanh::lean_unsigned_to_nat(0);
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
    mut v_sz_2987_: *mut leanh::LeanObject,
    mut v_i_2988_: *mut leanh::LeanObject,
    mut v_bs_2989_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_sz_boxed_2990_: usize = 0;
    let mut v_i_boxed_2991_: usize = 0;
    let mut v_res_2992_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_2990_ = leanh::lean_unbox_usize(v_sz_2987_);
    leanh::lean_dec(v_sz_2987_);
    v_i_boxed_2991_ = leanh::lean_unbox_usize(v_i_2988_);
    leanh::lean_dec(v_i_2988_);
    v_res_2992_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__5(v_sz_boxed_2990_, v_i_boxed_2991_, v_bs_2989_);
    return v_res_2992_;
}
pub unsafe fn l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__6_spec__8___redArg(
    mut v_hi_2993_: *mut leanh::LeanObject,
    mut v_pivot_2994_: *mut leanh::LeanObject,
    mut v_as_2995_: *mut leanh::LeanObject,
    mut v_i_2996_: *mut leanh::LeanObject,
    mut v_k_2997_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2998_: u8 = 0;
    let mut v___x_2999_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3000_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3001_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_3002_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_3003_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3004_: u8 = 0;
    let mut v___x_3005_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3006_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3008_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3009_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3010_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3011_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2998_ = lean_nat_dec_lt(v_k_2997_, v_hi_2993_);
                if v___x_2998_ == 0 {
                    leanh::lean_dec(v_k_2997_);
                    v___x_2999_ = lean_array_fswap(v_as_2995_, v_i_2996_, v_hi_2993_);
                    v___x_3000_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_3000_, 0, v_i_2996_);
                    leanh::lean_ctor_set(v___x_3000_, 1, v___x_2999_);
                    return v___x_3000_;
                } else {
                    v___x_3001_ = lean_array_fget_borrowed(v_as_2995_, v_k_2997_);
                    v_fst_3002_ = leanh::lean_ctor_get(v___x_3001_, 0);
                    v_fst_3003_ = leanh::lean_ctor_get(v_pivot_2994_, 0);
                    v___x_3004_ = lean_nat_dec_lt(v_fst_3002_, v_fst_3003_);
                    if v___x_3004_ == 0 {
                        v___x_3005_ = leanh::lean_unsigned_to_nat(1);
                        v___x_3006_ = lean_nat_add(v_k_2997_, v___x_3005_);
                        leanh::lean_dec(v_k_2997_);
                        v_k_2997_ = v___x_3006_;
                        state = 0;
                        continue;
                    } else {
                        v___x_3008_ = lean_array_fswap(v_as_2995_, v_i_2996_, v_k_2997_);
                        v___x_3009_ = leanh::lean_unsigned_to_nat(1);
                        v___x_3010_ = lean_nat_add(v_i_2996_, v___x_3009_);
                        leanh::lean_dec(v_i_2996_);
                        v___x_3011_ = lean_nat_add(v_k_2997_, v___x_3009_);
                        leanh::lean_dec(v_k_2997_);
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
    mut v_hi_3013_: *mut leanh::LeanObject,
    mut v_pivot_3014_: *mut leanh::LeanObject,
    mut v_as_3015_: *mut leanh::LeanObject,
    mut v_i_3016_: *mut leanh::LeanObject,
    mut v_k_3017_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3018_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3018_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__6_spec__8___redArg(v_hi_3013_, v_pivot_3014_, v_as_3015_, v_i_3016_, v_k_3017_);
    leanh::lean_dec_ref(v_pivot_3014_);
    leanh::lean_dec(v_hi_3013_);
    return v_res_3018_;
}
pub unsafe fn l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__6___redArg___lam__0(
    mut v_x1_3019_: *mut leanh::LeanObject,
    mut v_x2_3020_: *mut leanh::LeanObject,
) -> u8 {
    let mut v_fst_3021_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_3022_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3023_: u8 = 0;
    v_fst_3021_ = leanh::lean_ctor_get(v_x1_3019_, 0);
    v_fst_3022_ = leanh::lean_ctor_get(v_x2_3020_, 0);
    v___x_3023_ = lean_nat_dec_lt(v_fst_3021_, v_fst_3022_);
    return v___x_3023_;
}
pub unsafe fn l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__6___redArg___lam__0___boxed(
    mut v_x1_3024_: *mut leanh::LeanObject,
    mut v_x2_3025_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3026_: u8 = 0;
    let mut v_r_3027_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3026_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__6___redArg___lam__0(v_x1_3024_, v_x2_3025_);
    leanh::lean_dec_ref(v_x2_3025_);
    leanh::lean_dec_ref(v_x1_3024_);
    v_r_3027_ = leanh::lean_box((v_res_3026_) as usize);
    return v_r_3027_;
}
pub unsafe fn l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__6___redArg(
    mut v_n_3028_: *mut leanh::LeanObject,
    mut v_as_3029_: *mut leanh::LeanObject,
    mut v_lo_3030_: *mut leanh::LeanObject,
    mut v_hi_3031_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___y_3033_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_pivot_3034_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3035_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_3036_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3037_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3038_: u8 = 0;
    let mut v___x_3039_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3040_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3041_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3043_: u8 = 0;
    let mut v___x_3044_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3045_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_mid_3046_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3048_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3049_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3050_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3051_: u8 = 0;
    let mut v___x_3052_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3054_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3055_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3056_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3057_: u8 = 0;
    let mut v___x_3058_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3059_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3060_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3061_: u8 = 0;
    let mut v___x_3062_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3043_ = lean_nat_dec_lt(v_lo_3030_, v_hi_3031_);
                if v___x_3043_ == 0 {
                    leanh::lean_dec(v_lo_3030_);
                    return v_as_3029_;
                } else {
                    v___x_3044_ = lean_nat_add(v_lo_3030_, v_hi_3031_);
                    v___x_3045_ = leanh::lean_unsigned_to_nat(1);
                    v_mid_3046_ = lean_nat_shiftr(v___x_3044_, v___x_3045_);
                    leanh::lean_dec(v___x_3044_);
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
                leanh::lean_inc_n(v_lo_3030_, 2);
                v___x_3035_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__6_spec__8___redArg(v_hi_3031_, v_pivot_3034_, v___y_3033_, v_lo_3030_, v_lo_3030_);
                leanh::lean_dec(v_pivot_3034_);
                v_fst_3036_ = leanh::lean_ctor_get(v___x_3035_, 0);
                leanh::lean_inc(v_fst_3036_);
                v_snd_3037_ = leanh::lean_ctor_get(v___x_3035_, 1);
                leanh::lean_inc(v_snd_3037_);
                leanh::lean_dec_ref(v___x_3035_);
                v___x_3038_ = lean_nat_dec_le(v_hi_3031_, v_fst_3036_);
                if v___x_3038_ == 0 {
                    v___x_3039_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__6___redArg(v_n_3028_, v_snd_3037_, v_lo_3030_, v_fst_3036_);
                    v___x_3040_ = leanh::lean_unsigned_to_nat(1);
                    v___x_3041_ = lean_nat_add(v_fst_3036_, v___x_3040_);
                    leanh::lean_dec(v_fst_3036_);
                    v_as_3029_ = v___x_3039_;
                    v_lo_3030_ = v___x_3041_;
                    state = 0;
                    continue;
                } else {
                    leanh::lean_dec(v_fst_3036_);
                    leanh::lean_dec(v_lo_3030_);
                    return v_snd_3037_;
                }
            }
            2 => {
                v___x_3049_ = lean_array_fget_borrowed(v___y_3048_, v_mid_3046_);
                v___x_3050_ = lean_array_fget_borrowed(v___y_3048_, v_hi_3031_);
                v___x_3051_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__6___redArg___lam__0(v___x_3049_, v___x_3050_);
                if v___x_3051_ == 0 {
                    leanh::lean_dec(v_mid_3046_);
                    v___y_3033_ = v___y_3048_;
                    state = 1;
                    continue;
                } else {
                    v___x_3052_ = lean_array_fswap(v___y_3048_, v_mid_3046_, v_hi_3031_);
                    leanh::lean_dec(v_mid_3046_);
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
    mut v_n_3063_: *mut leanh::LeanObject,
    mut v_as_3064_: *mut leanh::LeanObject,
    mut v_lo_3065_: *mut leanh::LeanObject,
    mut v_hi_3066_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3067_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3067_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__6___redArg(v_n_3063_, v_as_3064_, v_lo_3065_, v_hi_3066_);
    leanh::lean_dec(v_hi_3066_);
    leanh::lean_dec(v_n_3063_);
    return v_res_3067_;
}
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__4_spec__5(
    mut v_msgData_3068_: *mut leanh::LeanObject,
    mut v___y_3069_: *mut leanh::LeanObject,
    mut v___y_3070_: *mut leanh::LeanObject,
    mut v___y_3071_: *mut leanh::LeanObject,
    mut v___y_3072_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3074_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_3075_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3076_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_3077_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_lctx_3078_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_3079_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3080_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3081_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3082_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3074_ = lean_st_ref_get(v___y_3072_);
    v_env_3075_ = leanh::lean_ctor_get(v___x_3074_, 0);
    leanh::lean_inc_ref(v_env_3075_);
    leanh::lean_dec(v___x_3074_);
    v___x_3076_ = lean_st_ref_get(v___y_3070_);
    v_mctx_3077_ = leanh::lean_ctor_get(v___x_3076_, 0);
    leanh::lean_inc_ref(v_mctx_3077_);
    leanh::lean_dec(v___x_3076_);
    v_lctx_3078_ = leanh::lean_ctor_get(v___y_3069_, 2);
    v_options_3079_ = leanh::lean_ctor_get(v___y_3071_, 2);
    leanh::lean_inc_ref(v_options_3079_);
    leanh::lean_inc_ref(v_lctx_3078_);
    v___x_3080_ = leanh::lean_alloc_ctor(0, 4, (0) as u32);
    leanh::lean_ctor_set(v___x_3080_, 0, v_env_3075_);
    leanh::lean_ctor_set(v___x_3080_, 1, v_mctx_3077_);
    leanh::lean_ctor_set(v___x_3080_, 2, v_lctx_3078_);
    leanh::lean_ctor_set(v___x_3080_, 3, v_options_3079_);
    v___x_3081_ = leanh::lean_alloc_ctor(3, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_3081_, 0, v___x_3080_);
    leanh::lean_ctor_set(v___x_3081_, 1, v_msgData_3068_);
    v___x_3082_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_3082_, 0, v___x_3081_);
    return v___x_3082_;
}
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__4_spec__5___boxed(
    mut v_msgData_3083_: *mut leanh::LeanObject,
    mut v___y_3084_: *mut leanh::LeanObject,
    mut v___y_3085_: *mut leanh::LeanObject,
    mut v___y_3086_: *mut leanh::LeanObject,
    mut v___y_3087_: *mut leanh::LeanObject,
    mut v___y_3088_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3089_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3089_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__4_spec__5(v_msgData_3083_, v___y_3084_, v___y_3085_, v___y_3086_, v___y_3087_);
    leanh::lean_dec(v___y_3087_);
    leanh::lean_dec_ref(v___y_3086_);
    leanh::lean_dec(v___y_3085_);
    leanh::lean_dec_ref(v___y_3084_);
    return v_res_3089_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__4___redArg(
    mut v_msg_3090_: *mut leanh::LeanObject,
    mut v___y_3091_: *mut leanh::LeanObject,
    mut v___y_3092_: *mut leanh::LeanObject,
    mut v___y_3093_: *mut leanh::LeanObject,
    mut v___y_3094_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_ref_3096_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3097_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3098_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3100_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3101_: u8 = 0;
    let mut v___x_3102_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3104_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3105_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3106_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ref_3096_ = leanh::lean_ctor_get(v___y_3093_, 5);
                v___x_3097_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__4_spec__5(v_msg_3090_, v___y_3091_, v___y_3092_, v___y_3093_, v___y_3094_);
                v_a_3098_ = leanh::lean_ctor_get(v___x_3097_, 0);
                v_isSharedCheck_3106_ = (!leanh::lean_is_exclusive(v___x_3097_)) as u8;
                if v_isSharedCheck_3106_ == 0 {
                    v___x_3100_ = v___x_3097_;
                    v_isShared_3101_ = v_isSharedCheck_3106_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_a_3098_);
                    leanh::lean_dec(v___x_3097_);
                    v___x_3100_ = leanh::lean_box(0);
                    v_isShared_3101_ = v_isSharedCheck_3106_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                leanh::lean_inc(v_ref_3096_);
                v___x_3102_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_3102_, 0, v_ref_3096_);
                leanh::lean_ctor_set(v___x_3102_, 1, v_a_3098_);
                if v_isShared_3101_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_3100_, 1);
                    leanh::lean_ctor_set(v___x_3100_, 0, v___x_3102_);
                    v___x_3104_ = v___x_3100_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3105_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3105_, 0, v___x_3102_);
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
    mut v_msg_3107_: *mut leanh::LeanObject,
    mut v___y_3108_: *mut leanh::LeanObject,
    mut v___y_3109_: *mut leanh::LeanObject,
    mut v___y_3110_: *mut leanh::LeanObject,
    mut v___y_3111_: *mut leanh::LeanObject,
    mut v___y_3112_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3113_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3113_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__4___redArg(
        v_msg_3107_,
        v___y_3108_,
        v___y_3109_,
        v___y_3110_,
        v___y_3111_,
    );
    leanh::lean_dec(v___y_3111_);
    leanh::lean_dec_ref(v___y_3110_);
    leanh::lean_dec(v___y_3109_);
    leanh::lean_dec_ref(v___y_3108_);
    return v_res_3113_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__3_spec__3_spec__4_spec__12_spec__16___redArg(
    mut v_x_3114_: *mut leanh::LeanObject,
    mut v_x_3115_: *mut leanh::LeanObject,
    mut v_x_3116_: *mut leanh::LeanObject,
    mut v_x_3117_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_ks_3118_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_vs_3119_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3121_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3122_: u8 = 0;
    let mut v___x_3123_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3124_: u8 = 0;
    let mut v___x_3125_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3126_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3128_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3129_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_x27_3130_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3131_: u8 = 0;
    let mut v___x_3133_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3134_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3135_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3137_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3138_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3139_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3141_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3142_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3143_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ks_3118_ = leanh::lean_ctor_get(v_x_3114_, 0);
                v_vs_3119_ = leanh::lean_ctor_get(v_x_3114_, 1);
                v_isSharedCheck_3143_ = (!leanh::lean_is_exclusive(v_x_3114_)) as u8;
                if v_isSharedCheck_3143_ == 0 {
                    v___x_3121_ = v_x_3114_;
                    v_isShared_3122_ = v_isSharedCheck_3143_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_vs_3119_);
                    leanh::lean_inc(v_ks_3118_);
                    leanh::lean_dec(v_x_3114_);
                    v___x_3121_ = leanh::lean_box(0);
                    v_isShared_3122_ = v_isSharedCheck_3143_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_3123_ = lean_array_get_size(v_ks_3118_);
                v___x_3124_ = lean_nat_dec_lt(v_x_3115_, v___x_3123_);
                if v___x_3124_ == 0 {
                    leanh::lean_dec(v_x_3115_);
                    v___x_3125_ = lean_array_push(v_ks_3118_, v_x_3116_);
                    v___x_3126_ = lean_array_push(v_vs_3119_, v_x_3117_);
                    if v_isShared_3122_ == 0 {
                        leanh::lean_ctor_set(v___x_3121_, 1, v___x_3126_);
                        leanh::lean_ctor_set(v___x_3121_, 0, v___x_3125_);
                        v___x_3128_ = v___x_3121_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_3129_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_3129_, 0, v___x_3125_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_3129_, 1, v___x_3126_);
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
                                leanh::lean_alloc_ctor(1, 2, (0) as u32);
                            leanh::lean_ctor_set(v_reuseFailAlloc_3137_, 0, v_ks_3118_);
                            leanh::lean_ctor_set(v_reuseFailAlloc_3137_, 1, v_vs_3119_);
                            v___x_3133_ = v_reuseFailAlloc_3137_;
                            state = 3;
                            continue;
                        }
                    } else {
                        v___x_3138_ = lean_array_fset(v_ks_3118_, v_x_3115_, v_x_3116_);
                        v___x_3139_ = lean_array_fset(v_vs_3119_, v_x_3115_, v_x_3117_);
                        leanh::lean_dec(v_x_3115_);
                        if v_isShared_3122_ == 0 {
                            leanh::lean_ctor_set(v___x_3121_, 1, v___x_3139_);
                            leanh::lean_ctor_set(v___x_3121_, 0, v___x_3138_);
                            v___x_3141_ = v___x_3121_;
                            state = 4;
                            continue;
                        } else {
                            v_reuseFailAlloc_3142_ =
                                leanh::lean_alloc_ctor(1, 2, (0) as u32);
                            leanh::lean_ctor_set(v_reuseFailAlloc_3142_, 0, v___x_3138_);
                            leanh::lean_ctor_set(v_reuseFailAlloc_3142_, 1, v___x_3139_);
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
                v___x_3134_ = leanh::lean_unsigned_to_nat(1);
                v___x_3135_ = lean_nat_add(v_x_3115_, v___x_3134_);
                leanh::lean_dec(v_x_3115_);
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
    mut v_n_3144_: *mut leanh::LeanObject,
    mut v_k_3145_: *mut leanh::LeanObject,
    mut v_v_3146_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3147_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3148_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3147_ = leanh::lean_unsigned_to_nat(0);
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
    v___x_3153_ = leanh::lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__3_spec__3_spec__4___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__3_spec__3_spec__4___redArg___closed__0_once), _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__3_spec__3_spec__4___redArg___closed__0);
    v___x_3154_ = lean_usize_sub(v___x_3153_, v___x_3152_);
    return v___x_3154_;
}
pub unsafe fn _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__3_spec__3_spec__4___redArg___closed__2()
-> *mut leanh::LeanObject {
    let mut v___x_3155_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3155_ = l_Lean_PersistentHashMap_mkEmptyEntries(
        leanh::lean_box(0),
        leanh::lean_box(0),
    );
    return v___x_3155_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__3_spec__3_spec__4___redArg(
    mut v_x_3156_: *mut leanh::LeanObject,
    mut v_x_3157_: usize,
    mut v_x_3158_: usize,
    mut v_x_3159_: *mut leanh::LeanObject,
    mut v_x_3160_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_es_3161_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3162_: usize = 0;
    let mut v___x_3163_: usize = 0;
    let mut v___x_3164_: usize = 0;
    let mut v___x_3165_: usize = 0;
    let mut v_j_3166_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3167_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3168_: u8 = 0;
    let mut v___x_3170_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3171_: u8 = 0;
    let mut v_v_3172_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3173_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_xs_x27_3174_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3176_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3177_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3179_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3180_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_key_3181_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3182_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3184_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3185_: u8 = 0;
    let mut v___x_3186_: u8 = 0;
    let mut v___x_3187_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3188_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3190_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3191_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3192_: u8 = 0;
    let mut v_node_3193_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3195_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3196_: u8 = 0;
    let mut v___x_3197_: usize = 0;
    let mut v___x_3198_: usize = 0;
    let mut v___x_3199_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3201_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3202_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3203_: u8 = 0;
    let mut v___x_3204_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3205_: u8 = 0;
    let mut v_unused_3206_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ks_3207_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_vs_3208_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3210_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3211_: u8 = 0;
    let mut v___x_3213_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_newNode_3214_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3216_: u8 = 0;
    let mut v_ks_3217_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_vs_3218_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3219_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3220_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3221_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3222_: usize = 0;
    let mut v___x_3223_: u8 = 0;
    let mut v___x_3224_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3225_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3226_: u8 = 0;
    let mut v_reuseFailAlloc_3227_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3228_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_3156_) == 0 {
                    v_es_3161_ = leanh::lean_ctor_get(v_x_3156_, 0);
                    v___x_3162_ = 5usize;
                    v___x_3163_ = 1usize;
                    v___x_3164_ = leanh::lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__3_spec__3_spec__4___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__3_spec__3_spec__4___redArg___closed__1_once), _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__3_spec__3_spec__4___redArg___closed__1);
                    v___x_3165_ = lean_usize_land(v_x_3157_, v___x_3164_);
                    v_j_3166_ = lean_usize_to_nat(v___x_3165_);
                    v___x_3167_ = lean_array_get_size(v_es_3161_);
                    v___x_3168_ = lean_nat_dec_lt(v_j_3166_, v___x_3167_);
                    if v___x_3168_ == 0 {
                        leanh::lean_dec(v_j_3166_);
                        leanh::lean_dec(v_x_3160_);
                        leanh::lean_dec(v_x_3159_);
                        return v_x_3156_;
                    } else {
                        leanh::lean_inc_ref(v_es_3161_);
                        v_isSharedCheck_3205_ = (!leanh::lean_is_exclusive(v_x_3156_)) as u8;
                        if v_isSharedCheck_3205_ == 0 {
                            v_unused_3206_ = leanh::lean_ctor_get(v_x_3156_, 0);
                            leanh::lean_dec(v_unused_3206_);
                            v___x_3170_ = v_x_3156_;
                            v_isShared_3171_ = v_isSharedCheck_3205_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_dec(v_x_3156_);
                            v___x_3170_ = leanh::lean_box(0);
                            v_isShared_3171_ = v_isSharedCheck_3205_;
                            state = 1;
                            continue;
                        }
                    }
                } else {
                    v_ks_3207_ = leanh::lean_ctor_get(v_x_3156_, 0);
                    v_vs_3208_ = leanh::lean_ctor_get(v_x_3156_, 1);
                    v_isSharedCheck_3228_ = (!leanh::lean_is_exclusive(v_x_3156_)) as u8;
                    if v_isSharedCheck_3228_ == 0 {
                        v___x_3210_ = v_x_3156_;
                        v_isShared_3211_ = v_isSharedCheck_3228_;
                        state = 8;
                        continue;
                    } else {
                        leanh::lean_inc(v_vs_3208_);
                        leanh::lean_inc(v_ks_3207_);
                        leanh::lean_dec(v_x_3156_);
                        v___x_3210_ = leanh::lean_box(0);
                        v_isShared_3211_ = v_isSharedCheck_3228_;
                        state = 8;
                        continue;
                    }
                }
            }
            1 => {
                v_v_3172_ = lean_array_fget(v_es_3161_, v_j_3166_);
                v___x_3173_ = leanh::lean_box(0);
                v_xs_x27_3174_ = lean_array_fset(v_es_3161_, v_j_3166_, v___x_3173_);
                match leanh::lean_obj_tag(v_v_3172_) {
                    0 => {
                        v_key_3181_ = leanh::lean_ctor_get(v_v_3172_, 0);
                        v_val_3182_ = leanh::lean_ctor_get(v_v_3172_, 1);
                        v_isSharedCheck_3192_ = (!leanh::lean_is_exclusive(v_v_3172_)) as u8;
                        if v_isSharedCheck_3192_ == 0 {
                            v___x_3184_ = v_v_3172_;
                            v_isShared_3185_ = v_isSharedCheck_3192_;
                            state = 4;
                            continue;
                        } else {
                            leanh::lean_inc(v_val_3182_);
                            leanh::lean_inc(v_key_3181_);
                            leanh::lean_dec(v_v_3172_);
                            v___x_3184_ = leanh::lean_box(0);
                            v_isShared_3185_ = v_isSharedCheck_3192_;
                            state = 4;
                            continue;
                        }
                    }
                    1 => {
                        v_node_3193_ = leanh::lean_ctor_get(v_v_3172_, 0);
                        v_isSharedCheck_3203_ = (!leanh::lean_is_exclusive(v_v_3172_)) as u8;
                        if v_isSharedCheck_3203_ == 0 {
                            v___x_3195_ = v_v_3172_;
                            v_isShared_3196_ = v_isSharedCheck_3203_;
                            state = 6;
                            continue;
                        } else {
                            leanh::lean_inc(v_node_3193_);
                            leanh::lean_dec(v_v_3172_);
                            v___x_3195_ = leanh::lean_box(0);
                            v_isShared_3196_ = v_isSharedCheck_3203_;
                            state = 6;
                            continue;
                        }
                    }
                    _ => {
                        v___x_3204_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v___x_3204_, 0, v_x_3159_);
                        leanh::lean_ctor_set(v___x_3204_, 1, v_x_3160_);
                        v___y_3176_ = v___x_3204_;
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                v___x_3177_ = lean_array_fset(v_xs_x27_3174_, v_j_3166_, v___y_3176_);
                leanh::lean_dec(v_j_3166_);
                if v_isShared_3171_ == 0 {
                    leanh::lean_ctor_set(v___x_3170_, 0, v___x_3177_);
                    v___x_3179_ = v___x_3170_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_3180_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3180_, 0, v___x_3177_);
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
                    leanh::lean_del_object(v___x_3184_);
                    v___x_3187_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(
                        v_key_3181_,
                        v_val_3182_,
                        v_x_3159_,
                        v_x_3160_,
                    );
                    v___x_3188_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_3188_, 0, v___x_3187_);
                    v___y_3176_ = v___x_3188_;
                    state = 2;
                    continue;
                } else {
                    leanh::lean_dec(v_val_3182_);
                    leanh::lean_dec(v_key_3181_);
                    if v_isShared_3185_ == 0 {
                        leanh::lean_ctor_set(v___x_3184_, 1, v_x_3160_);
                        leanh::lean_ctor_set(v___x_3184_, 0, v_x_3159_);
                        v___x_3190_ = v___x_3184_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_3191_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_3191_, 0, v_x_3159_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_3191_, 1, v_x_3160_);
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
                    leanh::lean_ctor_set(v___x_3195_, 0, v___x_3199_);
                    v___x_3201_ = v___x_3195_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_3202_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3202_, 0, v___x_3199_);
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
                    v_reuseFailAlloc_3227_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3227_, 0, v_ks_3207_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3227_, 1, v_vs_3208_);
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
                    v___x_3225_ = leanh::lean_unsigned_to_nat(4);
                    v___x_3226_ = lean_nat_dec_lt(v___x_3224_, v___x_3225_);
                    leanh::lean_dec(v___x_3224_);
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
                    v_ks_3217_ = leanh::lean_ctor_get(v_newNode_3214_, 0);
                    leanh::lean_inc_ref(v_ks_3217_);
                    v_vs_3218_ = leanh::lean_ctor_get(v_newNode_3214_, 1);
                    leanh::lean_inc_ref(v_vs_3218_);
                    leanh::lean_dec_ref(v_newNode_3214_);
                    v___x_3219_ = leanh::lean_unsigned_to_nat(0);
                    v___x_3220_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__3_spec__3_spec__4___redArg___closed__2), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__3_spec__3_spec__4___redArg___closed__2_once), _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__3_spec__3_spec__4___redArg___closed__2);
                    v___x_3221_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__3_spec__3_spec__4_spec__13___redArg(v_x_3158_, v_ks_3217_, v_vs_3218_, v___x_3219_, v___x_3220_);
                    leanh::lean_dec_ref(v_vs_3218_);
                    leanh::lean_dec_ref(v_ks_3217_);
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
    mut v_keys_3230_: *mut leanh::LeanObject,
    mut v_vals_3231_: *mut leanh::LeanObject,
    mut v_i_3232_: *mut leanh::LeanObject,
    mut v_entries_3233_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3234_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3235_: u8 = 0;
    let mut v_k_3236_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_3237_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3238_: u64 = 0;
    let mut v_h_3239_: usize = 0;
    let mut v___x_3240_: usize = 0;
    let mut v___x_3241_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3242_: usize = 0;
    let mut v___x_3243_: usize = 0;
    let mut v___x_3244_: usize = 0;
    let mut v_h_3245_: usize = 0;
    let mut v___x_3246_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3247_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3234_ = lean_array_get_size(v_keys_3230_);
                v___x_3235_ = lean_nat_dec_lt(v_i_3232_, v___x_3234_);
                if v___x_3235_ == 0 {
                    leanh::lean_dec(v_i_3232_);
                    return v_entries_3233_;
                } else {
                    v_k_3236_ = lean_array_fget_borrowed(v_keys_3230_, v_i_3232_);
                    v_v_3237_ = lean_array_fget_borrowed(v_vals_3231_, v_i_3232_);
                    v___x_3238_ = l_Lean_instHashableMVarId_hash(v_k_3236_);
                    v_h_3239_ = lean_uint64_to_usize(v___x_3238_);
                    v___x_3240_ = 5usize;
                    v___x_3241_ = leanh::lean_unsigned_to_nat(1);
                    v___x_3242_ = 1usize;
                    v___x_3243_ = lean_usize_sub(v_depth_3229_, v___x_3242_);
                    v___x_3244_ = lean_usize_mul(v___x_3240_, v___x_3243_);
                    v_h_3245_ = lean_usize_shift_right(v_h_3239_, v___x_3244_);
                    v___x_3246_ = lean_nat_add(v_i_3232_, v___x_3241_);
                    leanh::lean_dec(v_i_3232_);
                    leanh::lean_inc(v_v_3237_);
                    leanh::lean_inc(v_k_3236_);
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
    mut v_depth_3249_: *mut leanh::LeanObject,
    mut v_keys_3250_: *mut leanh::LeanObject,
    mut v_vals_3251_: *mut leanh::LeanObject,
    mut v_i_3252_: *mut leanh::LeanObject,
    mut v_entries_3253_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_depth_boxed_3254_: usize = 0;
    let mut v_res_3255_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_depth_boxed_3254_ = leanh::lean_unbox_usize(v_depth_3249_);
    leanh::lean_dec(v_depth_3249_);
    v_res_3255_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__3_spec__3_spec__4_spec__13___redArg(v_depth_boxed_3254_, v_keys_3250_, v_vals_3251_, v_i_3252_, v_entries_3253_);
    leanh::lean_dec_ref(v_vals_3251_);
    leanh::lean_dec_ref(v_keys_3250_);
    return v_res_3255_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__3_spec__3_spec__4___redArg___boxed(
    mut v_x_3256_: *mut leanh::LeanObject,
    mut v_x_3257_: *mut leanh::LeanObject,
    mut v_x_3258_: *mut leanh::LeanObject,
    mut v_x_3259_: *mut leanh::LeanObject,
    mut v_x_3260_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_x_18897__boxed_3261_: usize = 0;
    let mut v_x_18898__boxed_3262_: usize = 0;
    let mut v_res_3263_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_x_18897__boxed_3261_ = leanh::lean_unbox_usize(v_x_3257_);
    leanh::lean_dec(v_x_3257_);
    v_x_18898__boxed_3262_ = leanh::lean_unbox_usize(v_x_3258_);
    leanh::lean_dec(v_x_3258_);
    v_res_3263_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__3_spec__3_spec__4___redArg(v_x_3256_, v_x_18897__boxed_3261_, v_x_18898__boxed_3262_, v_x_3259_, v_x_3260_);
    return v_res_3263_;
}
pub unsafe fn l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__3_spec__3___redArg(
    mut v_x_3264_: *mut leanh::LeanObject,
    mut v_x_3265_: *mut leanh::LeanObject,
    mut v_x_3266_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3267_: u64 = 0;
    let mut v___x_3268_: usize = 0;
    let mut v___x_3269_: usize = 0;
    let mut v___x_3270_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3267_ = l_Lean_instHashableMVarId_hash(v_x_3265_);
    v___x_3268_ = lean_uint64_to_usize(v___x_3267_);
    v___x_3269_ = 1usize;
    v___x_3270_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__3_spec__3_spec__4___redArg(v_x_3264_, v___x_3268_, v___x_3269_, v_x_3265_, v_x_3266_);
    return v___x_3270_;
}
pub unsafe fn l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__3___redArg(
    mut v_mvarId_3271_: *mut leanh::LeanObject,
    mut v_val_3272_: *mut leanh::LeanObject,
    mut v___y_3273_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3275_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_3276_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_cache_3277_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_zetaDeltaFVarIds_3278_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_postponed_3279_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_diag_3280_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3282_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3283_: u8 = 0;
    let mut v_depth_3284_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_levelAssignDepth_3285_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_lmvarCounter_3286_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_mvarCounter_3287_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_lDecls_3288_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_decls_3289_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_userNames_3290_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_lAssignment_3291_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_eAssignment_3292_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_dAssignment_3293_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3295_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3296_: u8 = 0;
    let mut v___x_3297_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3299_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3301_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3302_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3303_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3304_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3305_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3306_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3307_: u8 = 0;
    let mut v_isSharedCheck_3308_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3275_ = lean_st_ref_take(v___y_3273_);
                v_mctx_3276_ = leanh::lean_ctor_get(v___x_3275_, 0);
                v_cache_3277_ = leanh::lean_ctor_get(v___x_3275_, 1);
                v_zetaDeltaFVarIds_3278_ = leanh::lean_ctor_get(v___x_3275_, 2);
                v_postponed_3279_ = leanh::lean_ctor_get(v___x_3275_, 3);
                v_diag_3280_ = leanh::lean_ctor_get(v___x_3275_, 4);
                v_isSharedCheck_3308_ = (!leanh::lean_is_exclusive(v___x_3275_)) as u8;
                if v_isSharedCheck_3308_ == 0 {
                    v___x_3282_ = v___x_3275_;
                    v_isShared_3283_ = v_isSharedCheck_3308_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_diag_3280_);
                    leanh::lean_inc(v_postponed_3279_);
                    leanh::lean_inc(v_zetaDeltaFVarIds_3278_);
                    leanh::lean_inc(v_cache_3277_);
                    leanh::lean_inc(v_mctx_3276_);
                    leanh::lean_dec(v___x_3275_);
                    v___x_3282_ = leanh::lean_box(0);
                    v_isShared_3283_ = v_isSharedCheck_3308_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_depth_3284_ = leanh::lean_ctor_get(v_mctx_3276_, 0);
                v_levelAssignDepth_3285_ = leanh::lean_ctor_get(v_mctx_3276_, 1);
                v_lmvarCounter_3286_ = leanh::lean_ctor_get(v_mctx_3276_, 2);
                v_mvarCounter_3287_ = leanh::lean_ctor_get(v_mctx_3276_, 3);
                v_lDecls_3288_ = leanh::lean_ctor_get(v_mctx_3276_, 4);
                v_decls_3289_ = leanh::lean_ctor_get(v_mctx_3276_, 5);
                v_userNames_3290_ = leanh::lean_ctor_get(v_mctx_3276_, 6);
                v_lAssignment_3291_ = leanh::lean_ctor_get(v_mctx_3276_, 7);
                v_eAssignment_3292_ = leanh::lean_ctor_get(v_mctx_3276_, 8);
                v_dAssignment_3293_ = leanh::lean_ctor_get(v_mctx_3276_, 9);
                v_isSharedCheck_3307_ = (!leanh::lean_is_exclusive(v_mctx_3276_)) as u8;
                if v_isSharedCheck_3307_ == 0 {
                    v___x_3295_ = v_mctx_3276_;
                    v_isShared_3296_ = v_isSharedCheck_3307_;
                    state = 2;
                    continue;
                } else {
                    leanh::lean_inc(v_dAssignment_3293_);
                    leanh::lean_inc(v_eAssignment_3292_);
                    leanh::lean_inc(v_lAssignment_3291_);
                    leanh::lean_inc(v_userNames_3290_);
                    leanh::lean_inc(v_decls_3289_);
                    leanh::lean_inc(v_lDecls_3288_);
                    leanh::lean_inc(v_mvarCounter_3287_);
                    leanh::lean_inc(v_lmvarCounter_3286_);
                    leanh::lean_inc(v_levelAssignDepth_3285_);
                    leanh::lean_inc(v_depth_3284_);
                    leanh::lean_dec(v_mctx_3276_);
                    v___x_3295_ = leanh::lean_box(0);
                    v_isShared_3296_ = v_isSharedCheck_3307_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_3297_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__3_spec__3___redArg(v_eAssignment_3292_, v_mvarId_3271_, v_val_3272_);
                if v_isShared_3296_ == 0 {
                    leanh::lean_ctor_set(v___x_3295_, 8, v___x_3297_);
                    v___x_3299_ = v___x_3295_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_3306_ = leanh::lean_alloc_ctor(0, 10, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3306_, 0, v_depth_3284_);
                    leanh::lean_ctor_set(
                        v_reuseFailAlloc_3306_,
                        1,
                        v_levelAssignDepth_3285_,
                    );
                    leanh::lean_ctor_set(v_reuseFailAlloc_3306_, 2, v_lmvarCounter_3286_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3306_, 3, v_mvarCounter_3287_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3306_, 4, v_lDecls_3288_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3306_, 5, v_decls_3289_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3306_, 6, v_userNames_3290_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3306_, 7, v_lAssignment_3291_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3306_, 8, v___x_3297_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3306_, 9, v_dAssignment_3293_);
                    v___x_3299_ = v_reuseFailAlloc_3306_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_3283_ == 0 {
                    leanh::lean_ctor_set(v___x_3282_, 0, v___x_3299_);
                    v___x_3301_ = v___x_3282_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3305_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3305_, 0, v___x_3299_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3305_, 1, v_cache_3277_);
                    leanh::lean_ctor_set(
                        v_reuseFailAlloc_3305_,
                        2,
                        v_zetaDeltaFVarIds_3278_,
                    );
                    leanh::lean_ctor_set(v_reuseFailAlloc_3305_, 3, v_postponed_3279_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3305_, 4, v_diag_3280_);
                    v___x_3301_ = v_reuseFailAlloc_3305_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_3302_ = lean_st_ref_set(v___y_3273_, v___x_3301_);
                v___x_3303_ = leanh::lean_box(0);
                v___x_3304_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_3304_, 0, v___x_3303_);
                return v___x_3304_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__3___redArg___boxed(
    mut v_mvarId_3309_: *mut leanh::LeanObject,
    mut v_val_3310_: *mut leanh::LeanObject,
    mut v___y_3311_: *mut leanh::LeanObject,
    mut v___y_3312_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3313_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3313_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__3___redArg(
        v_mvarId_3309_,
        v_val_3310_,
        v___y_3311_,
    );
    leanh::lean_dec(v___y_3311_);
    return v_res_3313_;
}
pub unsafe fn l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__9___redArg___lam__0(
    mut v_x1_3314_: *mut leanh::LeanObject,
    mut v_x2_3315_: *mut leanh::LeanObject,
) -> u8 {
    let mut v_fst_3316_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_3317_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3318_: u8 = 0;
    v_fst_3316_ = leanh::lean_ctor_get(v_x1_3314_, 0);
    v_fst_3317_ = leanh::lean_ctor_get(v_x2_3315_, 0);
    v___x_3318_ = lean_nat_dec_lt(v_fst_3316_, v_fst_3317_);
    return v___x_3318_;
}
pub unsafe fn l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__9___redArg___lam__0___boxed(
    mut v_x1_3319_: *mut leanh::LeanObject,
    mut v_x2_3320_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3321_: u8 = 0;
    let mut v_r_3322_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3321_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__9___redArg___lam__0(v_x1_3319_, v_x2_3320_);
    leanh::lean_dec_ref(v_x2_3320_);
    leanh::lean_dec_ref(v_x1_3319_);
    v_r_3322_ = leanh::lean_box((v_res_3321_) as usize);
    return v_r_3322_;
}
pub unsafe fn l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__9_spec__13___redArg(
    mut v_hi_3323_: *mut leanh::LeanObject,
    mut v_pivot_3324_: *mut leanh::LeanObject,
    mut v_as_3325_: *mut leanh::LeanObject,
    mut v_i_3326_: *mut leanh::LeanObject,
    mut v_k_3327_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3328_: u8 = 0;
    let mut v___x_3329_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3330_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3331_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_3332_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_3333_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3334_: u8 = 0;
    let mut v___x_3335_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3336_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3338_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3339_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3340_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3341_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3328_ = lean_nat_dec_lt(v_k_3327_, v_hi_3323_);
                if v___x_3328_ == 0 {
                    leanh::lean_dec(v_k_3327_);
                    v___x_3329_ = lean_array_fswap(v_as_3325_, v_i_3326_, v_hi_3323_);
                    v___x_3330_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_3330_, 0, v_i_3326_);
                    leanh::lean_ctor_set(v___x_3330_, 1, v___x_3329_);
                    return v___x_3330_;
                } else {
                    v___x_3331_ = lean_array_fget_borrowed(v_as_3325_, v_k_3327_);
                    v_fst_3332_ = leanh::lean_ctor_get(v___x_3331_, 0);
                    v_fst_3333_ = leanh::lean_ctor_get(v_pivot_3324_, 0);
                    v___x_3334_ = lean_nat_dec_lt(v_fst_3332_, v_fst_3333_);
                    if v___x_3334_ == 0 {
                        v___x_3335_ = leanh::lean_unsigned_to_nat(1);
                        v___x_3336_ = lean_nat_add(v_k_3327_, v___x_3335_);
                        leanh::lean_dec(v_k_3327_);
                        v_k_3327_ = v___x_3336_;
                        state = 0;
                        continue;
                    } else {
                        v___x_3338_ = lean_array_fswap(v_as_3325_, v_i_3326_, v_k_3327_);
                        v___x_3339_ = leanh::lean_unsigned_to_nat(1);
                        v___x_3340_ = lean_nat_add(v_i_3326_, v___x_3339_);
                        leanh::lean_dec(v_i_3326_);
                        v___x_3341_ = lean_nat_add(v_k_3327_, v___x_3339_);
                        leanh::lean_dec(v_k_3327_);
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
    mut v_hi_3343_: *mut leanh::LeanObject,
    mut v_pivot_3344_: *mut leanh::LeanObject,
    mut v_as_3345_: *mut leanh::LeanObject,
    mut v_i_3346_: *mut leanh::LeanObject,
    mut v_k_3347_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3348_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3348_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__9_spec__13___redArg(v_hi_3343_, v_pivot_3344_, v_as_3345_, v_i_3346_, v_k_3347_);
    leanh::lean_dec_ref(v_pivot_3344_);
    leanh::lean_dec(v_hi_3343_);
    return v_res_3348_;
}
pub unsafe fn l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__9___redArg(
    mut v_n_3349_: *mut leanh::LeanObject,
    mut v_as_3350_: *mut leanh::LeanObject,
    mut v_lo_3351_: *mut leanh::LeanObject,
    mut v_hi_3352_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___y_3354_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_pivot_3355_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3356_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_3357_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3358_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3359_: u8 = 0;
    let mut v___x_3360_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3361_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3362_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3364_: u8 = 0;
    let mut v___x_3365_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3366_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_mid_3367_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3369_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3370_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3371_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3372_: u8 = 0;
    let mut v___x_3373_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3375_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3376_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3377_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3378_: u8 = 0;
    let mut v___x_3379_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3380_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3381_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3382_: u8 = 0;
    let mut v___x_3383_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3364_ = lean_nat_dec_lt(v_lo_3351_, v_hi_3352_);
                if v___x_3364_ == 0 {
                    leanh::lean_dec(v_lo_3351_);
                    return v_as_3350_;
                } else {
                    v___x_3365_ = lean_nat_add(v_lo_3351_, v_hi_3352_);
                    v___x_3366_ = leanh::lean_unsigned_to_nat(1);
                    v_mid_3367_ = lean_nat_shiftr(v___x_3365_, v___x_3366_);
                    leanh::lean_dec(v___x_3365_);
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
                leanh::lean_inc_n(v_lo_3351_, 2);
                v___x_3356_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__9_spec__13___redArg(v_hi_3352_, v_pivot_3355_, v___y_3354_, v_lo_3351_, v_lo_3351_);
                leanh::lean_dec(v_pivot_3355_);
                v_fst_3357_ = leanh::lean_ctor_get(v___x_3356_, 0);
                leanh::lean_inc(v_fst_3357_);
                v_snd_3358_ = leanh::lean_ctor_get(v___x_3356_, 1);
                leanh::lean_inc(v_snd_3358_);
                leanh::lean_dec_ref(v___x_3356_);
                v___x_3359_ = lean_nat_dec_le(v_hi_3352_, v_fst_3357_);
                if v___x_3359_ == 0 {
                    v___x_3360_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__9___redArg(v_n_3349_, v_snd_3358_, v_lo_3351_, v_fst_3357_);
                    v___x_3361_ = leanh::lean_unsigned_to_nat(1);
                    v___x_3362_ = lean_nat_add(v_fst_3357_, v___x_3361_);
                    leanh::lean_dec(v_fst_3357_);
                    v_as_3350_ = v___x_3360_;
                    v_lo_3351_ = v___x_3362_;
                    state = 0;
                    continue;
                } else {
                    leanh::lean_dec(v_fst_3357_);
                    leanh::lean_dec(v_lo_3351_);
                    return v_snd_3358_;
                }
            }
            2 => {
                v___x_3370_ = lean_array_fget_borrowed(v___y_3369_, v_mid_3367_);
                v___x_3371_ = lean_array_fget_borrowed(v___y_3369_, v_hi_3352_);
                v___x_3372_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__9___redArg___lam__0(v___x_3370_, v___x_3371_);
                if v___x_3372_ == 0 {
                    leanh::lean_dec(v_mid_3367_);
                    v___y_3354_ = v___y_3369_;
                    state = 1;
                    continue;
                } else {
                    v___x_3373_ = lean_array_fswap(v___y_3369_, v_mid_3367_, v_hi_3352_);
                    leanh::lean_dec(v_mid_3367_);
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
    mut v_n_3384_: *mut leanh::LeanObject,
    mut v_as_3385_: *mut leanh::LeanObject,
    mut v_lo_3386_: *mut leanh::LeanObject,
    mut v_hi_3387_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3388_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3388_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__9___redArg(v_n_3384_, v_as_3385_, v_lo_3386_, v_hi_3387_);
    leanh::lean_dec(v_hi_3387_);
    leanh::lean_dec(v_n_3384_);
    return v_res_3388_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__1___redArg(
    mut v_ref_3389_: *mut leanh::LeanObject,
    mut v_msg_3390_: *mut leanh::LeanObject,
    mut v___y_3391_: *mut leanh::LeanObject,
    mut v___y_3392_: *mut leanh::LeanObject,
    mut v___y_3393_: *mut leanh::LeanObject,
    mut v___y_3394_: *mut leanh::LeanObject,
    mut v___y_3395_: *mut leanh::LeanObject,
    mut v___y_3396_: *mut leanh::LeanObject,
    mut v___y_3397_: *mut leanh::LeanObject,
    mut v___y_3398_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_fileName_3400_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fileMap_3401_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_3402_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_currRecDepth_3403_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_maxRecDepth_3404_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_3405_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_currNamespace_3406_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_openDecls_3407_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_initHeartbeats_3408_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_maxHeartbeats_3409_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_quotContext_3410_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_currMacroScope_3411_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_diag_3412_: u8 = 0;
    let mut v_cancelTk_x3f_3413_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_suppressElabErrors_3414_: u8 = 0;
    let mut v_inheritedTraceOptions_3415_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_3416_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3417_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3418_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_fileName_3400_ = leanh::lean_ctor_get(v___y_3397_, 0);
    v_fileMap_3401_ = leanh::lean_ctor_get(v___y_3397_, 1);
    v_options_3402_ = leanh::lean_ctor_get(v___y_3397_, 2);
    v_currRecDepth_3403_ = leanh::lean_ctor_get(v___y_3397_, 3);
    v_maxRecDepth_3404_ = leanh::lean_ctor_get(v___y_3397_, 4);
    v_ref_3405_ = leanh::lean_ctor_get(v___y_3397_, 5);
    v_currNamespace_3406_ = leanh::lean_ctor_get(v___y_3397_, 6);
    v_openDecls_3407_ = leanh::lean_ctor_get(v___y_3397_, 7);
    v_initHeartbeats_3408_ = leanh::lean_ctor_get(v___y_3397_, 8);
    v_maxHeartbeats_3409_ = leanh::lean_ctor_get(v___y_3397_, 9);
    v_quotContext_3410_ = leanh::lean_ctor_get(v___y_3397_, 10);
    v_currMacroScope_3411_ = leanh::lean_ctor_get(v___y_3397_, 11);
    v_diag_3412_ = leanh::lean_ctor_get_uint8(
        v___y_3397_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 14) as u32,
    );
    v_cancelTk_x3f_3413_ = leanh::lean_ctor_get(v___y_3397_, 12);
    v_suppressElabErrors_3414_ = leanh::lean_ctor_get_uint8(
        v___y_3397_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 14 + 1) as u32,
    );
    v_inheritedTraceOptions_3415_ = leanh::lean_ctor_get(v___y_3397_, 13);
    v_ref_3416_ = l_Lean_replaceRef(v_ref_3389_, v_ref_3405_);
    leanh::lean_inc_ref(v_inheritedTraceOptions_3415_);
    leanh::lean_inc(v_cancelTk_x3f_3413_);
    leanh::lean_inc(v_currMacroScope_3411_);
    leanh::lean_inc(v_quotContext_3410_);
    leanh::lean_inc(v_maxHeartbeats_3409_);
    leanh::lean_inc(v_initHeartbeats_3408_);
    leanh::lean_inc(v_openDecls_3407_);
    leanh::lean_inc(v_currNamespace_3406_);
    leanh::lean_inc(v_maxRecDepth_3404_);
    leanh::lean_inc(v_currRecDepth_3403_);
    leanh::lean_inc_ref(v_options_3402_);
    leanh::lean_inc_ref(v_fileMap_3401_);
    leanh::lean_inc_ref(v_fileName_3400_);
    v___x_3417_ = leanh::lean_alloc_ctor(0, 14, (2) as u32);
    leanh::lean_ctor_set(v___x_3417_, 0, v_fileName_3400_);
    leanh::lean_ctor_set(v___x_3417_, 1, v_fileMap_3401_);
    leanh::lean_ctor_set(v___x_3417_, 2, v_options_3402_);
    leanh::lean_ctor_set(v___x_3417_, 3, v_currRecDepth_3403_);
    leanh::lean_ctor_set(v___x_3417_, 4, v_maxRecDepth_3404_);
    leanh::lean_ctor_set(v___x_3417_, 5, v_ref_3416_);
    leanh::lean_ctor_set(v___x_3417_, 6, v_currNamespace_3406_);
    leanh::lean_ctor_set(v___x_3417_, 7, v_openDecls_3407_);
    leanh::lean_ctor_set(v___x_3417_, 8, v_initHeartbeats_3408_);
    leanh::lean_ctor_set(v___x_3417_, 9, v_maxHeartbeats_3409_);
    leanh::lean_ctor_set(v___x_3417_, 10, v_quotContext_3410_);
    leanh::lean_ctor_set(v___x_3417_, 11, v_currMacroScope_3411_);
    leanh::lean_ctor_set(v___x_3417_, 12, v_cancelTk_x3f_3413_);
    leanh::lean_ctor_set(v___x_3417_, 13, v_inheritedTraceOptions_3415_);
    leanh::lean_ctor_set_uint8(
        v___x_3417_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 14) as u32,
        v_diag_3412_,
    );
    leanh::lean_ctor_set_uint8(
        v___x_3417_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 14 + 1) as u32,
        v_suppressElabErrors_3414_,
    );
    v___x_3418_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__4___redArg(
        v_msg_3390_,
        v___y_3395_,
        v___y_3396_,
        v___x_3417_,
        v___y_3398_,
    );
    leanh::lean_dec_ref_known(v___x_3417_, 14);
    return v___x_3418_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__1___redArg___boxed(
    mut v_ref_3419_: *mut leanh::LeanObject,
    mut v_msg_3420_: *mut leanh::LeanObject,
    mut v___y_3421_: *mut leanh::LeanObject,
    mut v___y_3422_: *mut leanh::LeanObject,
    mut v___y_3423_: *mut leanh::LeanObject,
    mut v___y_3424_: *mut leanh::LeanObject,
    mut v___y_3425_: *mut leanh::LeanObject,
    mut v___y_3426_: *mut leanh::LeanObject,
    mut v___y_3427_: *mut leanh::LeanObject,
    mut v___y_3428_: *mut leanh::LeanObject,
    mut v___y_3429_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3430_: *mut leanh::LeanObject = core::ptr::null_mut();
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
    leanh::lean_dec(v___y_3428_);
    leanh::lean_dec_ref(v___y_3427_);
    leanh::lean_dec(v___y_3426_);
    leanh::lean_dec_ref(v___y_3425_);
    leanh::lean_dec(v___y_3424_);
    leanh::lean_dec_ref(v___y_3423_);
    leanh::lean_dec(v___y_3422_);
    leanh::lean_dec_ref(v___y_3421_);
    leanh::lean_dec(v_ref_3419_);
    return v_res_3430_;
}
pub unsafe fn _init_l_Array_mapFinIdxM_map___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__7___redArg___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_3432_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3433_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3432_ = l_Array_mapFinIdxM_map___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__7___redArg___closed__0;
    v___x_3433_ = l_Lean_stringToMessageData(v___x_3432_);
    return v___x_3433_;
}
pub unsafe fn l_Array_mapFinIdxM_map___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__7___redArg(
    mut v_as_3434_: *mut leanh::LeanObject,
    mut v_i_3435_: *mut leanh::LeanObject,
    mut v_j_3436_: *mut leanh::LeanObject,
    mut v_bs_3437_: *mut leanh::LeanObject,
    mut v___y_3438_: *mut leanh::LeanObject,
    mut v___y_3439_: *mut leanh::LeanObject,
    mut v___y_3440_: *mut leanh::LeanObject,
    mut v___y_3441_: *mut leanh::LeanObject,
    mut v___y_3442_: *mut leanh::LeanObject,
    mut v___y_3443_: *mut leanh::LeanObject,
    mut v___y_3444_: *mut leanh::LeanObject,
    mut v___y_3445_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_zero_3447_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isZero_3448_: u8 = 0;
    let mut v___x_3449_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_one_3450_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_n_3451_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3453_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3454_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3455_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3457_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3458_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isZero_3459_: u8 = 0;
    let mut v___x_3460_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3461_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3462_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3464_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3465_: u8 = 0;
    let mut v___x_3467_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3468_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3469_: u8 = 0;
    let mut v_n_3470_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3471_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_zero_3447_ = leanh::lean_unsigned_to_nat(0);
                v_isZero_3448_ = lean_nat_dec_eq(v_i_3435_, v_zero_3447_);
                if v_isZero_3448_ == 1 {
                    leanh::lean_dec(v_j_3436_);
                    leanh::lean_dec(v_i_3435_);
                    v___x_3449_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_3449_, 0, v_bs_3437_);
                    return v___x_3449_;
                } else {
                    v_one_3450_ = leanh::lean_unsigned_to_nat(1);
                    v_n_3451_ = lean_nat_sub(v_i_3435_, v_one_3450_);
                    leanh::lean_dec(v_i_3435_);
                    v___x_3457_ = lean_array_fget_borrowed(v_as_3434_, v_j_3436_);
                    v___x_3458_ = l_Lean_TSyntax_getNat(v___x_3457_);
                    v_isZero_3459_ = lean_nat_dec_eq(v___x_3458_, v_zero_3447_);
                    if v_isZero_3459_ == 1 {
                        leanh::lean_dec(v___x_3458_);
                        leanh::lean_dec(v_n_3451_);
                        leanh::lean_dec_ref(v_bs_3437_);
                        leanh::lean_dec(v_j_3436_);
                        v___x_3460_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Array_mapFinIdxM_map___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__7___redArg___closed__1), core::ptr::addr_of_mut!(l_Array_mapFinIdxM_map___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__7___redArg___closed__1_once), _init_l_Array_mapFinIdxM_map___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__7___redArg___closed__1);
                        v___x_3461_ = l_Lean_throwErrorAt___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__1___redArg(v___x_3457_, v___x_3460_, v___y_3438_, v___y_3439_, v___y_3440_, v___y_3441_, v___y_3442_, v___y_3443_, v___y_3444_, v___y_3445_);
                        v_a_3462_ = leanh::lean_ctor_get(v___x_3461_, 0);
                        v_isSharedCheck_3469_ =
                            (!leanh::lean_is_exclusive(v___x_3461_)) as u8;
                        if v_isSharedCheck_3469_ == 0 {
                            v___x_3464_ = v___x_3461_;
                            v_isShared_3465_ = v_isSharedCheck_3469_;
                            state = 2;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_3462_);
                            leanh::lean_dec(v___x_3461_);
                            v___x_3464_ = leanh::lean_box(0);
                            v_isShared_3465_ = v_isSharedCheck_3469_;
                            state = 2;
                            continue;
                        }
                    } else {
                        v_n_3470_ = lean_nat_sub(v___x_3458_, v_one_3450_);
                        leanh::lean_dec(v___x_3458_);
                        leanh::lean_inc(v_j_3436_);
                        v___x_3471_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v___x_3471_, 0, v_n_3470_);
                        leanh::lean_ctor_set(v___x_3471_, 1, v_j_3436_);
                        v_a_3453_ = v___x_3471_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_3454_ = lean_nat_add(v_j_3436_, v_one_3450_);
                leanh::lean_dec(v_j_3436_);
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
                    v_reuseFailAlloc_3468_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3468_, 0, v_a_3462_);
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
    mut v_as_3472_: *mut leanh::LeanObject,
    mut v_i_3473_: *mut leanh::LeanObject,
    mut v_j_3474_: *mut leanh::LeanObject,
    mut v_bs_3475_: *mut leanh::LeanObject,
    mut v___y_3476_: *mut leanh::LeanObject,
    mut v___y_3477_: *mut leanh::LeanObject,
    mut v___y_3478_: *mut leanh::LeanObject,
    mut v___y_3479_: *mut leanh::LeanObject,
    mut v___y_3480_: *mut leanh::LeanObject,
    mut v___y_3481_: *mut leanh::LeanObject,
    mut v___y_3482_: *mut leanh::LeanObject,
    mut v___y_3483_: *mut leanh::LeanObject,
    mut v___y_3484_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3485_: *mut leanh::LeanObject = core::ptr::null_mut();
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
    leanh::lean_dec(v___y_3483_);
    leanh::lean_dec_ref(v___y_3482_);
    leanh::lean_dec(v___y_3481_);
    leanh::lean_dec_ref(v___y_3480_);
    leanh::lean_dec(v___y_3479_);
    leanh::lean_dec_ref(v___y_3478_);
    leanh::lean_dec(v___y_3477_);
    leanh::lean_dec_ref(v___y_3476_);
    leanh::lean_dec_ref(v_as_3472_);
    return v_res_3485_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_allDiffAuxAux___at___00__private_Init_Data_Array_Basic_0__Array_allDiffAux___at___00Array_allDiff___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__8_spec__11_spec__13___redArg(
    mut v_as_3486_: *mut leanh::LeanObject,
    mut v_a_3487_: *mut leanh::LeanObject,
    mut v_x_3488_: *mut leanh::LeanObject,
) -> u8 {
    let mut v_zero_3489_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isZero_3490_: u8 = 0;
    let mut v_fst_3491_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_one_3492_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_n_3493_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3494_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_3495_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3496_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_zero_3489_ = leanh::lean_unsigned_to_nat(0);
                v_isZero_3490_ = lean_nat_dec_eq(v_x_3488_, v_zero_3489_);
                if v_isZero_3490_ == 1 {
                    leanh::lean_dec(v_x_3488_);
                    return v_isZero_3490_;
                } else {
                    v_fst_3491_ = leanh::lean_ctor_get(v_a_3487_, 0);
                    v_one_3492_ = leanh::lean_unsigned_to_nat(1);
                    v_n_3493_ = lean_nat_sub(v_x_3488_, v_one_3492_);
                    leanh::lean_dec(v_x_3488_);
                    v___x_3494_ = lean_array_fget_borrowed(v_as_3486_, v_n_3493_);
                    v_fst_3495_ = leanh::lean_ctor_get(v___x_3494_, 0);
                    v___x_3496_ = lean_nat_dec_eq(v_fst_3491_, v_fst_3495_);
                    if v___x_3496_ == 0 {
                        v_x_3488_ = v_n_3493_;
                        state = 0;
                        continue;
                    } else {
                        leanh::lean_dec(v_n_3493_);
                        return v_isZero_3490_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_allDiffAuxAux___at___00__private_Init_Data_Array_Basic_0__Array_allDiffAux___at___00Array_allDiff___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__8_spec__11_spec__13___redArg___boxed(
    mut v_as_3498_: *mut leanh::LeanObject,
    mut v_a_3499_: *mut leanh::LeanObject,
    mut v_x_3500_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3501_: u8 = 0;
    let mut v_r_3502_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3501_ = l___private_Init_Data_Array_Basic_0__Array_allDiffAuxAux___at___00__private_Init_Data_Array_Basic_0__Array_allDiffAux___at___00Array_allDiff___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__8_spec__11_spec__13___redArg(v_as_3498_, v_a_3499_, v_x_3500_);
    leanh::lean_dec_ref(v_a_3499_);
    leanh::lean_dec_ref(v_as_3498_);
    v_r_3502_ = leanh::lean_box((v_res_3501_) as usize);
    return v_r_3502_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_allDiffAux___at___00Array_allDiff___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__8_spec__11(
    mut v_as_3503_: *mut leanh::LeanObject,
    mut v_i_3504_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_3505_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3506_: u8 = 0;
    let mut v___x_3507_: u8 = 0;
    let mut v___x_3508_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3509_: u8 = 0;
    let mut v___x_3510_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3511_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3505_ = lean_array_get_size(v_as_3503_);
                v___x_3506_ = lean_nat_dec_lt(v_i_3504_, v___x_3505_);
                if v___x_3506_ == 0 {
                    leanh::lean_dec(v_i_3504_);
                    v___x_3507_ = 1;
                    return v___x_3507_;
                } else {
                    v___x_3508_ = lean_array_fget_borrowed(v_as_3503_, v_i_3504_);
                    leanh::lean_inc(v_i_3504_);
                    v___x_3509_ = l___private_Init_Data_Array_Basic_0__Array_allDiffAuxAux___at___00__private_Init_Data_Array_Basic_0__Array_allDiffAux___at___00Array_allDiff___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__8_spec__11_spec__13___redArg(v_as_3503_, v___x_3508_, v_i_3504_);
                    if v___x_3509_ == 0 {
                        leanh::lean_dec(v_i_3504_);
                        return v___x_3509_;
                    } else {
                        v___x_3510_ = leanh::lean_unsigned_to_nat(1);
                        v___x_3511_ = lean_nat_add(v_i_3504_, v___x_3510_);
                        leanh::lean_dec(v_i_3504_);
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
    mut v_as_3513_: *mut leanh::LeanObject,
    mut v_i_3514_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3515_: u8 = 0;
    let mut v_r_3516_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3515_ = l___private_Init_Data_Array_Basic_0__Array_allDiffAux___at___00Array_allDiff___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__8_spec__11(v_as_3513_, v_i_3514_);
    leanh::lean_dec_ref(v_as_3513_);
    v_r_3516_ = leanh::lean_box((v_res_3515_) as usize);
    return v_r_3516_;
}
pub unsafe fn l_Array_allDiff___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__8(
    mut v_as_3517_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_3518_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3519_: u8 = 0;
    v___x_3518_ = leanh::lean_unsigned_to_nat(0);
    v___x_3519_ = l___private_Init_Data_Array_Basic_0__Array_allDiffAux___at___00Array_allDiff___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__8_spec__11(v_as_3517_, v___x_3518_);
    return v___x_3519_;
}
pub unsafe fn l_Array_allDiff___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__8___boxed(
    mut v_as_3520_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3521_: u8 = 0;
    let mut v_r_3522_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3521_ = l_Array_allDiff___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__8(v_as_3520_);
    leanh::lean_dec_ref(v_as_3520_);
    v_r_3522_ = leanh::lean_box((v_res_3521_) as usize);
    return v_r_3522_;
}
pub unsafe fn _init_l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__0()
-> *mut leanh::LeanObject {
    let mut v___x_3523_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3523_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(
        leanh::lean_box(0),
        leanh::lean_box(0),
    );
    return v___x_3523_;
}
pub unsafe fn _init_l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_3524_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3525_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3524_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__0),
        core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__0_once),
        _init_l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__0,
    );
    v___x_3525_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_3525_, 0, v___x_3524_);
    return v___x_3525_;
}
pub unsafe fn _init_l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__2()
-> *mut leanh::LeanObject {
    let mut v___x_3526_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3527_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3528_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3526_ = leanh::lean_unsigned_to_nat(0);
    v___x_3527_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__1),
        core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__1_once),
        _init_l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__1,
    );
    v___x_3528_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_3528_, 0, v___x_3527_);
    leanh::lean_ctor_set(v___x_3528_, 1, v___x_3526_);
    return v___x_3528_;
}
pub unsafe fn _init_l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__3()
-> *mut leanh::LeanObject {
    let mut v___x_3529_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3530_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3531_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3529_ = leanh::lean_unsigned_to_nat(32);
    v___x_3530_ = lean_mk_empty_array_with_capacity(v___x_3529_);
    v___x_3531_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_3531_, 0, v___x_3530_);
    return v___x_3531_;
}
pub unsafe fn _init_l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__4()
-> *mut leanh::LeanObject {
    let mut v___x_3532_: usize = 0;
    let mut v___x_3533_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3534_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3535_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3536_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3537_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3532_ = 5usize;
    v___x_3533_ = leanh::lean_unsigned_to_nat(0);
    v___x_3534_ = leanh::lean_unsigned_to_nat(32);
    v___x_3535_ = lean_mk_empty_array_with_capacity(v___x_3534_);
    v___x_3536_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__3),
        core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__3_once),
        _init_l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__3,
    );
    v___x_3537_ = leanh::lean_alloc_ctor(0, 4, (core::mem::size_of::<usize>() * 1) as u32);
    leanh::lean_ctor_set(v___x_3537_, 0, v___x_3536_);
    leanh::lean_ctor_set(v___x_3537_, 1, v___x_3535_);
    leanh::lean_ctor_set(v___x_3537_, 2, v___x_3533_);
    leanh::lean_ctor_set(v___x_3537_, 3, v___x_3533_);
    leanh::lean_ctor_set_usize(v___x_3537_, 4, v___x_3532_);
    return v___x_3537_;
}
pub unsafe fn _init_l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__5()
-> *mut leanh::LeanObject {
    let mut v___x_3538_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3539_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3540_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3538_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__4),
        core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__4_once),
        _init_l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__4,
    );
    v___x_3539_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__1),
        core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__1_once),
        _init_l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__1,
    );
    v___x_3540_ = leanh::lean_alloc_ctor(0, 4, (0) as u32);
    leanh::lean_ctor_set(v___x_3540_, 0, v___x_3539_);
    leanh::lean_ctor_set(v___x_3540_, 1, v___x_3539_);
    leanh::lean_ctor_set(v___x_3540_, 2, v___x_3539_);
    leanh::lean_ctor_set(v___x_3540_, 3, v___x_3538_);
    return v___x_3540_;
}
pub unsafe fn _init_l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__6()
-> *mut leanh::LeanObject {
    let mut v___x_3541_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3542_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3543_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3541_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__5),
        core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__5_once),
        _init_l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__5,
    );
    v___x_3542_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__2),
        core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__2_once),
        _init_l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__2,
    );
    v___x_3543_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_3543_, 0, v___x_3542_);
    leanh::lean_ctor_set(v___x_3543_, 1, v___x_3541_);
    return v___x_3543_;
}
pub unsafe fn _init_l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__8()
-> *mut leanh::LeanObject {
    let mut v___x_3545_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3546_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3545_ = l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__7;
    v___x_3546_ = l_Lean_stringToMessageData(v___x_3545_);
    return v___x_3546_;
}
pub unsafe fn _init_l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__10()
-> *mut leanh::LeanObject {
    let mut v___x_3548_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3549_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3548_ = l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__9;
    v___x_3549_ = l_Lean_stringToMessageData(v___x_3548_);
    return v___x_3549_;
}
pub unsafe fn _init_l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__12()
-> *mut leanh::LeanObject {
    let mut v___x_3551_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3552_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3551_ = l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__11;
    v___x_3552_ = l_Lean_stringToMessageData(v___x_3551_);
    return v___x_3552_;
}
pub unsafe fn _init_l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__14()
-> *mut leanh::LeanObject {
    let mut v___x_3554_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3555_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3554_ = l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__13;
    v___x_3555_ = l_Lean_stringToMessageData(v___x_3554_);
    return v___x_3555_;
}
pub unsafe fn _init_l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__17()
-> *mut leanh::LeanObject {
    let mut v___x_3559_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3560_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3559_ = l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__16;
    v___x_3560_ = l_Lean_stringToMessageData(v___x_3559_);
    return v___x_3560_;
}
pub unsafe fn l_Lean_Elab_Tactic_Conv_evalPattern___lam__6(
    mut v___x_3581_: u8,
    mut v___f_3582_: *mut leanh::LeanObject,
    mut v___x_3583_: u8,
    mut v_stx_3584_: *mut leanh::LeanObject,
    mut v___x_3585_: *mut leanh::LeanObject,
    mut v___x_3586_: *mut leanh::LeanObject,
    mut v___x_3587_: *mut leanh::LeanObject,
    mut v___x_3588_: *mut leanh::LeanObject,
    mut v___y_3589_: *mut leanh::LeanObject,
    mut v___y_3590_: *mut leanh::LeanObject,
    mut v___y_3591_: *mut leanh::LeanObject,
    mut v___y_3592_: *mut leanh::LeanObject,
    mut v___y_3593_: *mut leanh::LeanObject,
    mut v___y_3594_: *mut leanh::LeanObject,
    mut v___y_3595_: *mut leanh::LeanObject,
    mut v___y_3596_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___y_3599_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_subgoals_3600_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3601_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3602_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3603_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3604_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3605_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3606_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3607_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3608_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3609_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3610_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_expr_3611_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3612_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3613_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3614_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3615_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3616_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3617_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3618_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3619_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3620_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3621_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3623_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3624_: u8 = 0;
    let mut v___x_3626_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3627_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3628_: u8 = 0;
    let mut v_a_3629_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3631_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3632_: u8 = 0;
    let mut v___x_3634_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3635_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3636_: u8 = 0;
    let mut v_a_3637_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3639_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3640_: u8 = 0;
    let mut v___x_3642_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3643_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3644_: u8 = 0;
    let mut v___y_3646_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3647_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3648_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3649_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3650_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3651_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3652_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3653_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3654_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3655_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_3656_: usize = 0;
    let mut v___x_3657_: usize = 0;
    let mut v___x_3658_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3660_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3661_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3662_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3663_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3664_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3665_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3666_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3667_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3668_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3669_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3670_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3671_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3672_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3673_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3675_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3676_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3677_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3678_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3679_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3680_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3681_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3682_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3683_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3684_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3685_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3686_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3687_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3688_: u8 = 0;
    let mut v___x_3689_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3690_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3691_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3693_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3694_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3695_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3696_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3697_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3698_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3699_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3700_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3701_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3702_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3703_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3704_: u8 = 0;
    let mut v___x_3705_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3706_: u8 = 0;
    let mut v___y_3708_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3709_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3710_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3711_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3712_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3713_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3714_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3715_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3716_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3717_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3718_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3719_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3720_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3721_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3722_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3723_: u8 = 0;
    let mut v___x_3724_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3725_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3726_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3727_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3728_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3729_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_3730_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3732_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3733_: u8 = 0;
    let mut v___x_3734_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_subgoals_3735_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3736_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3737_: u8 = 0;
    let mut v_expr_3738_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3739_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3740_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3742_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3743_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3744_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3746_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3747_: u8 = 0;
    let mut v___x_3749_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3750_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3751_: u8 = 0;
    let mut v_reuseFailAlloc_3752_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_subgoals_3753_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_idx_3754_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_remaining_3755_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3756_: u8 = 0;
    let mut v___x_3757_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3758_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3760_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3761_: u8 = 0;
    let mut v_fst_3762_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3764_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3765_: u8 = 0;
    let mut v___x_3766_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3767_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3769_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3770_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3772_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3773_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3775_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3776_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3777_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3778_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3779_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3780_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3781_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3782_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3783_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3784_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3785_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3786_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3787_: u8 = 0;
    let mut v_unused_3788_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3789_: u8 = 0;
    let mut v_expr_3790_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3791_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3792_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3794_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3795_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3796_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3798_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3799_: u8 = 0;
    let mut v___x_3801_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3802_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3803_: u8 = 0;
    let mut v_reuseFailAlloc_3804_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3805_: u8 = 0;
    let mut v_unused_3806_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3807_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3809_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3810_: u8 = 0;
    let mut v___x_3812_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3813_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3814_: u8 = 0;
    let mut v___y_3816_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3817_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3818_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3819_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3820_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_occs_3821_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3822_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3823_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3824_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3825_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3826_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3827_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3828_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3829_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3830_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3831_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3832_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3833_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3834_: u8 = 0;
    let mut v_a_3835_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3837_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3838_: u8 = 0;
    let mut v___x_3840_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3841_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3842_: u8 = 0;
    let mut v___y_3844_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3845_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3846_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3847_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3848_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3849_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3850_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3851_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3852_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3853_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3854_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3855_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3856_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3857_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3858_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3859_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3860_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3862_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3863_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3864_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3865_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3866_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3867_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3868_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3869_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3870_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3871_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3872_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3873_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3874_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3875_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3876_: u8 = 0;
    let mut v___x_3877_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3878_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3880_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3881_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3882_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3883_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3884_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3885_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3886_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3887_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3888_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3889_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3890_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3891_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3892_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3893_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3894_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3895_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3896_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3897_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3899_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3900_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3901_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3902_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3903_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3904_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3905_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3906_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3907_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3908_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3909_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3910_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3911_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3912_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3913_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3914_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3915_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3916_: u8 = 0;
    let mut v_occs_3918_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3919_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3920_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3921_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3922_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3923_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3924_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3925_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3926_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_declName_x3f_3927_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_macroStack_3928_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_mayPostpone_3929_: u8 = 0;
    let mut v_errToSorry_3930_: u8 = 0;
    let mut v_autoBoundImplicitContext_3931_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_autoBoundImplicitForbidden_3932_: *mut leanh::LeanObject =
        core::ptr::null_mut();
    let mut v_sectionVars_3933_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_sectionFVars_3934_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_implicitLambda_3935_: u8 = 0;
    let mut v_heedElabAsElim_3936_: u8 = 0;
    let mut v_isNoncomputableSection_3937_: u8 = 0;
    let mut v_isMetaSection_3938_: u8 = 0;
    let mut v_inPattern_3939_: u8 = 0;
    let mut v_tacSnap_x3f_3940_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_saveRecAppSyntax_3941_: u8 = 0;
    let mut v_holesAsSyntheticOpaque_3942_: u8 = 0;
    let mut v_checkDeprecated_3943_: u8 = 0;
    let mut v_fixedTermElabs_3944_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3945_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3946_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3947_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3948_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3949_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3950_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3951_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3952_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3953_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3954_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3955_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3956_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3957_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3958_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3959_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3960_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3961_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3962_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3963_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3964_: u8 = 0;
    let mut v___x_3965_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3966_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3967_: u8 = 0;
    let mut v___x_3968_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3969_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3971_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3972_: u8 = 0;
    let mut v___x_3974_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3975_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3976_: u8 = 0;
    let mut v___x_3977_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3978_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3979_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3980_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3981_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3982_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3983_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3984_: u8 = 0;
    let mut v___x_3985_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3986_: u8 = 0;
    let mut v_a_3987_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3989_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3990_: u8 = 0;
    let mut v___x_3992_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3993_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3994_: u8 = 0;
    let mut v___x_3995_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3996_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3998_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3999_: u8 = 0;
    let mut v___x_4001_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4002_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4003_: u8 = 0;
    let mut v_a_4004_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4006_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4007_: u8 = 0;
    let mut v___x_4009_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4010_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4011_: u8 = 0;
    let mut v___x_4012_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4013_: u8 = 0;
    let mut v___x_4014_: u8 = 0;
    let mut v___x_4015_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4016_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4017_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4018_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4019_: u8 = 0;
    let mut v___x_4020_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4021_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_occs_4022_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4023_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4024_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if v___x_3581_ == 0 {
                    leanh::lean_dec_ref(v___x_3588_);
                    leanh::lean_dec_ref(v___x_3587_);
                    leanh::lean_dec_ref(v___x_3586_);
                    leanh::lean_dec_ref(v___x_3585_);
                    leanh::lean_dec_ref(v___f_3582_);
                    v___x_3689_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__0___redArg();
                    return v___x_3689_;
                } else {
                    v___x_3690_ = leanh::lean_unsigned_to_nat(0);
                    v___x_3691_ = leanh::lean_unsigned_to_nat(1);
                    v___x_4012_ = l_Lean_Syntax_getArg(v_stx_3584_, v___x_3691_);
                    v___x_4013_ = l_Lean_Syntax_isNone(v___x_4012_);
                    if v___x_4013_ == 0 {
                        leanh::lean_inc(v___x_4012_);
                        v___x_4014_ = l_Lean_Syntax_matchesNull(v___x_4012_, v___x_3691_);
                        if v___x_4014_ == 0 {
                            leanh::lean_dec(v___x_4012_);
                            leanh::lean_dec_ref(v___x_3588_);
                            leanh::lean_dec_ref(v___x_3587_);
                            leanh::lean_dec_ref(v___x_3586_);
                            leanh::lean_dec_ref(v___x_3585_);
                            leanh::lean_dec_ref(v___f_3582_);
                            v___x_4015_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__0___redArg();
                            return v___x_4015_;
                        } else {
                            v___x_4016_ = l_Lean_Syntax_getArg(v___x_4012_, v___x_3690_);
                            leanh::lean_dec(v___x_4012_);
                            v___x_4017_ = l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__27;
                            leanh::lean_inc_ref(v___x_3588_);
                            leanh::lean_inc_ref(v___x_3587_);
                            leanh::lean_inc_ref(v___x_3586_);
                            leanh::lean_inc_ref(v___x_3585_);
                            v___x_4018_ = l_Lean_Name_mkStr5(
                                v___x_3585_,
                                v___x_3586_,
                                v___x_3587_,
                                v___x_3588_,
                                v___x_4017_,
                            );
                            leanh::lean_inc(v___x_4016_);
                            v___x_4019_ = l_Lean_Syntax_isOfKind(v___x_4016_, v___x_4018_);
                            leanh::lean_dec(v___x_4018_);
                            if v___x_4019_ == 0 {
                                leanh::lean_dec(v___x_4016_);
                                leanh::lean_dec_ref(v___x_3588_);
                                leanh::lean_dec_ref(v___x_3587_);
                                leanh::lean_dec_ref(v___x_3586_);
                                leanh::lean_dec_ref(v___x_3585_);
                                leanh::lean_dec_ref(v___f_3582_);
                                v___x_4020_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__0___redArg();
                                return v___x_4020_;
                            } else {
                                v___x_4021_ = leanh::lean_unsigned_to_nat(3);
                                v_occs_4022_ = l_Lean_Syntax_getArg(v___x_4016_, v___x_4021_);
                                leanh::lean_dec(v___x_4016_);
                                v___x_4023_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                                leanh::lean_ctor_set(v___x_4023_, 0, v_occs_4022_);
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
                        leanh::lean_dec(v___x_4012_);
                        v___x_4024_ = leanh::lean_box(0);
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
                if leanh::lean_obj_tag(v___x_3609_) == 0 {
                    v_a_3610_ = leanh::lean_ctor_get(v___x_3609_, 0);
                    leanh::lean_inc(v_a_3610_);
                    leanh::lean_dec_ref_known(v___x_3609_, 1);
                    v_expr_3611_ = leanh::lean_ctor_get(v___y_3599_, 0);
                    v___x_3612_ = l_Lean_Expr_mvarId_x21(v_a_3610_);
                    leanh::lean_dec(v_a_3610_);
                    leanh::lean_inc_ref(v_expr_3611_);
                    v___x_3613_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__3___redArg(v___x_3612_, v_expr_3611_, v___y_3606_);
                    leanh::lean_dec_ref(v___x_3613_);
                    v___x_3614_ = l_Lean_Elab_Tactic_getMainGoal___redArg(
                        v___y_3602_,
                        v___y_3605_,
                        v___y_3606_,
                        v___y_3607_,
                        v___y_3608_,
                    );
                    if leanh::lean_obj_tag(v___x_3614_) == 0 {
                        v_a_3615_ = leanh::lean_ctor_get(v___x_3614_, 0);
                        leanh::lean_inc(v_a_3615_);
                        leanh::lean_dec_ref_known(v___x_3614_, 1);
                        v___x_3616_ = l_Lean_Meta_Simp_Result_getProof(
                            v___y_3599_,
                            v___y_3605_,
                            v___y_3606_,
                            v___y_3607_,
                            v___y_3608_,
                        );
                        if leanh::lean_obj_tag(v___x_3616_) == 0 {
                            v_a_3617_ = leanh::lean_ctor_get(v___x_3616_, 0);
                            leanh::lean_inc(v_a_3617_);
                            leanh::lean_dec_ref_known(v___x_3616_, 1);
                            v___x_3618_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__3___redArg(v_a_3615_, v_a_3617_, v___y_3606_);
                            leanh::lean_dec_ref(v___x_3618_);
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
                            leanh::lean_dec(v_a_3615_);
                            leanh::lean_dec_ref(v_subgoals_3600_);
                            v_a_3621_ = leanh::lean_ctor_get(v___x_3616_, 0);
                            v_isSharedCheck_3628_ =
                                (!leanh::lean_is_exclusive(v___x_3616_)) as u8;
                            if v_isSharedCheck_3628_ == 0 {
                                v___x_3623_ = v___x_3616_;
                                v_isShared_3624_ = v_isSharedCheck_3628_;
                                state = 2;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_3621_);
                                leanh::lean_dec(v___x_3616_);
                                v___x_3623_ = leanh::lean_box(0);
                                v_isShared_3624_ = v_isSharedCheck_3628_;
                                state = 2;
                                continue;
                            }
                        }
                    } else {
                        leanh::lean_dec_ref(v_subgoals_3600_);
                        leanh::lean_dec_ref(v___y_3599_);
                        v_a_3629_ = leanh::lean_ctor_get(v___x_3614_, 0);
                        v_isSharedCheck_3636_ =
                            (!leanh::lean_is_exclusive(v___x_3614_)) as u8;
                        if v_isSharedCheck_3636_ == 0 {
                            v___x_3631_ = v___x_3614_;
                            v_isShared_3632_ = v_isSharedCheck_3636_;
                            state = 4;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_3629_);
                            leanh::lean_dec(v___x_3614_);
                            v___x_3631_ = leanh::lean_box(0);
                            v_isShared_3632_ = v_isSharedCheck_3636_;
                            state = 4;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_dec_ref(v_subgoals_3600_);
                    leanh::lean_dec_ref(v___y_3599_);
                    v_a_3637_ = leanh::lean_ctor_get(v___x_3609_, 0);
                    v_isSharedCheck_3644_ = (!leanh::lean_is_exclusive(v___x_3609_)) as u8;
                    if v_isSharedCheck_3644_ == 0 {
                        v___x_3639_ = v___x_3609_;
                        v_isShared_3640_ = v_isSharedCheck_3644_;
                        state = 6;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_3637_);
                        leanh::lean_dec(v___x_3609_);
                        v___x_3639_ = leanh::lean_box(0);
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
                    v_reuseFailAlloc_3627_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3627_, 0, v_a_3621_);
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
                    v_reuseFailAlloc_3635_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3635_, 0, v_a_3629_);
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
                    v_reuseFailAlloc_3643_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3643_, 0, v_a_3637_);
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
                leanh::lean_dec(v___y_3672_);
                leanh::lean_dec(v___y_3669_);
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
                    leanh::lean_dec(v___y_3677_);
                    leanh::lean_inc(v___y_3687_);
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
                        leanh::lean_inc(v___x_3705_);
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
                v___x_3725_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__6
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__6_once
                    ),
                    _init_l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__6,
                );
                leanh::lean_inc(v___y_3713_);
                leanh::lean_inc_ref(v___y_3722_);
                v___x_3726_ = leanh::lean_alloc_closure(
                    l___private_Lean_Elab_Tactic_Conv_Pattern_0__Lean_Elab_Tactic_Conv_pre___boxed
                        as *mut core::ffi::c_void,
                    11,
                    2,
                );
                leanh::lean_closure_set(v___x_3726_, 0, v___y_3722_);
                leanh::lean_closure_set(v___x_3726_, 1, v___y_3713_);
                leanh::lean_inc_ref(v___y_3712_);
                leanh::lean_inc_ref(v___y_3720_);
                v___x_3727_ = leanh::lean_alloc_ctor(0, 5, (1) as u32);
                leanh::lean_ctor_set(v___x_3727_, 0, v___x_3726_);
                leanh::lean_ctor_set(v___x_3727_, 1, v___y_3715_);
                leanh::lean_ctor_set(v___x_3727_, 2, v___y_3720_);
                leanh::lean_ctor_set(v___x_3727_, 3, v___f_3582_);
                leanh::lean_ctor_set(v___x_3727_, 4, v___y_3712_);
                leanh::lean_ctor_set_uint8(
                    v___x_3727_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 5) as u32,
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
                if leanh::lean_obj_tag(v___x_3728_) == 0 {
                    v_a_3729_ = leanh::lean_ctor_get(v___x_3728_, 0);
                    leanh::lean_inc(v_a_3729_);
                    leanh::lean_dec_ref_known(v___x_3728_, 1);
                    v_fst_3730_ = leanh::lean_ctor_get(v_a_3729_, 0);
                    v_isSharedCheck_3805_ = (!leanh::lean_is_exclusive(v_a_3729_)) as u8;
                    if v_isSharedCheck_3805_ == 0 {
                        v_unused_3806_ = leanh::lean_ctor_get(v_a_3729_, 1);
                        leanh::lean_dec(v_unused_3806_);
                        v___x_3732_ = v_a_3729_;
                        v_isShared_3733_ = v_isSharedCheck_3805_;
                        state = 13;
                        continue;
                    } else {
                        leanh::lean_inc(v_fst_3730_);
                        leanh::lean_dec(v_a_3729_);
                        v___x_3732_ = leanh::lean_box(0);
                        v_isShared_3733_ = v_isSharedCheck_3805_;
                        state = 13;
                        continue;
                    }
                } else {
                    leanh::lean_dec_ref(v___y_3722_);
                    leanh::lean_dec(v___y_3713_);
                    v_a_3807_ = leanh::lean_ctor_get(v___x_3728_, 0);
                    v_isSharedCheck_3814_ = (!leanh::lean_is_exclusive(v___x_3728_)) as u8;
                    if v_isSharedCheck_3814_ == 0 {
                        v___x_3809_ = v___x_3728_;
                        v_isShared_3810_ = v_isSharedCheck_3814_;
                        state = 25;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_3807_);
                        leanh::lean_dec(v___x_3728_);
                        v___x_3809_ = leanh::lean_box(0);
                        v_isShared_3810_ = v_isSharedCheck_3814_;
                        state = 25;
                        continue;
                    }
                }
            }
            13 => {
                v___x_3734_ = lean_st_ref_get(v___y_3713_);
                leanh::lean_dec(v___y_3713_);
                if leanh::lean_obj_tag(v___x_3734_) == 0 {
                    v_subgoals_3735_ = leanh::lean_ctor_get(v___x_3734_, 0);
                    leanh::lean_inc_ref(v_subgoals_3735_);
                    leanh::lean_dec_ref_known(v___x_3734_, 1);
                    v___x_3736_ = lean_array_get_size(v_subgoals_3735_);
                    v___x_3737_ = lean_nat_dec_eq(v___x_3736_, v___x_3690_);
                    if v___x_3737_ == 0 {
                        leanh::lean_del_object(v___x_3732_);
                        leanh::lean_dec_ref(v___y_3722_);
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
                        leanh::lean_dec_ref(v_subgoals_3735_);
                        leanh::lean_dec(v_fst_3730_);
                        v_expr_3738_ = leanh::lean_ctor_get(v___y_3722_, 2);
                        leanh::lean_inc_ref(v_expr_3738_);
                        leanh::lean_dec_ref(v___y_3722_);
                        v___x_3739_ = leanh::lean_obj_once(
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
                            leanh::lean_ctor_set_tag(v___x_3732_, 7);
                            leanh::lean_ctor_set(v___x_3732_, 1, v___x_3740_);
                            leanh::lean_ctor_set(v___x_3732_, 0, v___x_3739_);
                            v___x_3742_ = v___x_3732_;
                            state = 14;
                            continue;
                        } else {
                            v_reuseFailAlloc_3752_ =
                                leanh::lean_alloc_ctor(7, 2, (0) as u32);
                            leanh::lean_ctor_set(v_reuseFailAlloc_3752_, 0, v___x_3739_);
                            leanh::lean_ctor_set(v_reuseFailAlloc_3752_, 1, v___x_3740_);
                            v___x_3742_ = v_reuseFailAlloc_3752_;
                            state = 14;
                            continue;
                        }
                    }
                } else {
                    v_subgoals_3753_ = leanh::lean_ctor_get(v___x_3734_, 0);
                    leanh::lean_inc_ref(v_subgoals_3753_);
                    v_idx_3754_ = leanh::lean_ctor_get(v___x_3734_, 1);
                    leanh::lean_inc(v_idx_3754_);
                    v_remaining_3755_ = leanh::lean_ctor_get(v___x_3734_, 2);
                    leanh::lean_inc(v_remaining_3755_);
                    leanh::lean_dec_ref_known(v___x_3734_, 3);
                    v___x_3756_ = lean_nat_dec_eq(v_idx_3754_, v___x_3690_);
                    if v___x_3756_ == 0 {
                        leanh::lean_dec_ref(v___y_3722_);
                        v___x_3757_ = l_List_getLast_x3f___redArg(v_remaining_3755_);
                        leanh::lean_dec(v_remaining_3755_);
                        if leanh::lean_obj_tag(v___x_3757_) == 1 {
                            leanh::lean_dec_ref(v_subgoals_3753_);
                            leanh::lean_dec(v_fst_3730_);
                            v_val_3758_ = leanh::lean_ctor_get(v___x_3757_, 0);
                            v_isSharedCheck_3789_ =
                                (!leanh::lean_is_exclusive(v___x_3757_)) as u8;
                            if v_isSharedCheck_3789_ == 0 {
                                v___x_3760_ = v___x_3757_;
                                v_isShared_3761_ = v_isSharedCheck_3789_;
                                state = 17;
                                continue;
                            } else {
                                leanh::lean_inc(v_val_3758_);
                                leanh::lean_dec(v___x_3757_);
                                v___x_3760_ = leanh::lean_box(0);
                                v_isShared_3761_ = v_isSharedCheck_3789_;
                                state = 17;
                                continue;
                            }
                        } else {
                            leanh::lean_dec(v___x_3757_);
                            leanh::lean_dec(v_idx_3754_);
                            leanh::lean_del_object(v___x_3732_);
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
                        leanh::lean_dec(v_remaining_3755_);
                        leanh::lean_dec(v_idx_3754_);
                        leanh::lean_dec_ref(v_subgoals_3753_);
                        leanh::lean_dec(v_fst_3730_);
                        v_expr_3790_ = leanh::lean_ctor_get(v___y_3722_, 2);
                        leanh::lean_inc_ref(v_expr_3790_);
                        leanh::lean_dec_ref(v___y_3722_);
                        v___x_3791_ = leanh::lean_obj_once(
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
                            leanh::lean_ctor_set_tag(v___x_3732_, 7);
                            leanh::lean_ctor_set(v___x_3732_, 1, v___x_3792_);
                            leanh::lean_ctor_set(v___x_3732_, 0, v___x_3791_);
                            v___x_3794_ = v___x_3732_;
                            state = 22;
                            continue;
                        } else {
                            v_reuseFailAlloc_3804_ =
                                leanh::lean_alloc_ctor(7, 2, (0) as u32);
                            leanh::lean_ctor_set(v_reuseFailAlloc_3804_, 0, v___x_3791_);
                            leanh::lean_ctor_set(v_reuseFailAlloc_3804_, 1, v___x_3792_);
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
                v_a_3744_ = leanh::lean_ctor_get(v___x_3743_, 0);
                v_isSharedCheck_3751_ = (!leanh::lean_is_exclusive(v___x_3743_)) as u8;
                if v_isSharedCheck_3751_ == 0 {
                    v___x_3746_ = v___x_3743_;
                    v_isShared_3747_ = v_isSharedCheck_3751_;
                    state = 15;
                    continue;
                } else {
                    leanh::lean_inc(v_a_3744_);
                    leanh::lean_dec(v___x_3743_);
                    v___x_3746_ = leanh::lean_box(0);
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
                    v_reuseFailAlloc_3750_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3750_, 0, v_a_3744_);
                    v___x_3749_ = v_reuseFailAlloc_3750_;
                    state = 16;
                    continue;
                }
            }
            16 => {
                return v___x_3749_;
            }
            17 => {
                v_fst_3762_ = leanh::lean_ctor_get(v_val_3758_, 0);
                v_isSharedCheck_3787_ = (!leanh::lean_is_exclusive(v_val_3758_)) as u8;
                if v_isSharedCheck_3787_ == 0 {
                    v_unused_3788_ = leanh::lean_ctor_get(v_val_3758_, 1);
                    leanh::lean_dec(v_unused_3788_);
                    v___x_3764_ = v_val_3758_;
                    v_isShared_3765_ = v_isSharedCheck_3787_;
                    state = 18;
                    continue;
                } else {
                    leanh::lean_inc(v_fst_3762_);
                    leanh::lean_dec(v_val_3758_);
                    v___x_3764_ = leanh::lean_box(0);
                    v_isShared_3765_ = v_isSharedCheck_3787_;
                    state = 18;
                    continue;
                }
            }
            18 => {
                v___x_3766_ = leanh::lean_obj_once(
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
                    leanh::lean_ctor_set_tag(v___x_3760_, 3);
                    leanh::lean_ctor_set(v___x_3760_, 0, v___x_3767_);
                    v___x_3769_ = v___x_3760_;
                    state = 19;
                    continue;
                } else {
                    v_reuseFailAlloc_3786_ = leanh::lean_alloc_ctor(3, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3786_, 0, v___x_3767_);
                    v___x_3769_ = v_reuseFailAlloc_3786_;
                    state = 19;
                    continue;
                }
            }
            19 => {
                v___x_3770_ = l_Lean_MessageData_ofFormat(v___x_3769_);
                if v_isShared_3765_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_3764_, 7);
                    leanh::lean_ctor_set(v___x_3764_, 1, v___x_3770_);
                    leanh::lean_ctor_set(v___x_3764_, 0, v___x_3766_);
                    v___x_3772_ = v___x_3764_;
                    state = 20;
                    continue;
                } else {
                    v_reuseFailAlloc_3785_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3785_, 0, v___x_3766_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3785_, 1, v___x_3770_);
                    v___x_3772_ = v_reuseFailAlloc_3785_;
                    state = 20;
                    continue;
                }
            }
            20 => {
                v___x_3773_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__12
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__12_once
                    ),
                    _init_l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__12,
                );
                if v_isShared_3733_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_3732_, 7);
                    leanh::lean_ctor_set(v___x_3732_, 1, v___x_3773_);
                    leanh::lean_ctor_set(v___x_3732_, 0, v___x_3772_);
                    v___x_3775_ = v___x_3732_;
                    state = 21;
                    continue;
                } else {
                    v_reuseFailAlloc_3784_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3784_, 0, v___x_3772_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3784_, 1, v___x_3773_);
                    v___x_3775_ = v_reuseFailAlloc_3784_;
                    state = 21;
                    continue;
                }
            }
            21 => {
                v___x_3776_ = lean_nat_add(v_fst_3762_, v___x_3691_);
                leanh::lean_dec(v_fst_3762_);
                v___x_3777_ = l_Nat_reprFast(v___x_3776_);
                v___x_3778_ = leanh::lean_alloc_ctor(3, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_3778_, 0, v___x_3777_);
                v___x_3779_ = l_Lean_MessageData_ofFormat(v___x_3778_);
                v___x_3780_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_3780_, 0, v___x_3775_);
                leanh::lean_ctor_set(v___x_3780_, 1, v___x_3779_);
                v___x_3781_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__14
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__14_once
                    ),
                    _init_l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__14,
                );
                v___x_3782_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_3782_, 0, v___x_3780_);
                leanh::lean_ctor_set(v___x_3782_, 1, v___x_3781_);
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
                v_a_3796_ = leanh::lean_ctor_get(v___x_3795_, 0);
                v_isSharedCheck_3803_ = (!leanh::lean_is_exclusive(v___x_3795_)) as u8;
                if v_isSharedCheck_3803_ == 0 {
                    v___x_3798_ = v___x_3795_;
                    v_isShared_3799_ = v_isSharedCheck_3803_;
                    state = 23;
                    continue;
                } else {
                    leanh::lean_inc(v_a_3796_);
                    leanh::lean_dec(v___x_3795_);
                    v___x_3798_ = leanh::lean_box(0);
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
                    v_reuseFailAlloc_3802_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3802_, 0, v_a_3796_);
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
                    v_reuseFailAlloc_3813_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3813_, 0, v_a_3807_);
                    v___x_3812_ = v_reuseFailAlloc_3813_;
                    state = 26;
                    continue;
                }
            }
            26 => {
                return v___x_3812_;
            }
            27 => {
                leanh::lean_inc_ref(v_occs_3821_);
                v___x_3830_ = lean_st_mk_ref(v_occs_3821_);
                v___x_3831_ = l___private_Lean_Elab_Tactic_Conv_Pattern_0__Lean_Elab_Tactic_Conv_getContext___redArg(v___y_3826_, v___y_3828_, v___y_3829_);
                if leanh::lean_obj_tag(v___x_3831_) == 0 {
                    if leanh::lean_obj_tag(v_occs_3821_) == 0 {
                        leanh::lean_dec_ref_known(v_occs_3821_, 1);
                        v_a_3832_ = leanh::lean_ctor_get(v___x_3831_, 0);
                        leanh::lean_inc(v_a_3832_);
                        leanh::lean_dec_ref_known(v___x_3831_, 1);
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
                        leanh::lean_dec_ref(v_occs_3821_);
                        v_a_3833_ = leanh::lean_ctor_get(v___x_3831_, 0);
                        leanh::lean_inc(v_a_3833_);
                        leanh::lean_dec_ref_known(v___x_3831_, 1);
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
                    leanh::lean_dec(v___x_3830_);
                    leanh::lean_dec_ref(v_occs_3821_);
                    leanh::lean_dec_ref(v___y_3820_);
                    leanh::lean_dec_ref(v___y_3819_);
                    leanh::lean_dec_ref(v___y_3816_);
                    leanh::lean_dec_ref(v___f_3582_);
                    v_a_3835_ = leanh::lean_ctor_get(v___x_3831_, 0);
                    v_isSharedCheck_3842_ = (!leanh::lean_is_exclusive(v___x_3831_)) as u8;
                    if v_isSharedCheck_3842_ == 0 {
                        v___x_3837_ = v___x_3831_;
                        v_isShared_3838_ = v_isSharedCheck_3842_;
                        state = 28;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_3835_);
                        leanh::lean_dec(v___x_3831_);
                        v___x_3837_ = leanh::lean_box(0);
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
                    v_reuseFailAlloc_3841_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3841_, 0, v_a_3835_);
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
                v___x_3860_ = leanh::lean_alloc_ctor(1, 3, (0) as u32);
                leanh::lean_ctor_set(v___x_3860_, 0, v___x_3858_);
                leanh::lean_ctor_set(v___x_3860_, 1, v___x_3690_);
                leanh::lean_ctor_set(v___x_3860_, 2, v___x_3859_);
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
                    leanh::lean_dec_ref(v___y_3875_);
                    leanh::lean_dec_ref(v___y_3872_);
                    leanh::lean_dec_ref(v___y_3864_);
                    leanh::lean_dec_ref(v___y_3862_);
                    leanh::lean_dec_ref(v___f_3582_);
                    v___x_3877_ = leanh::lean_obj_once(
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
                leanh::lean_dec(v___y_3896_);
                leanh::lean_dec(v___y_3887_);
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
                    leanh::lean_dec(v___y_3901_);
                    leanh::lean_inc(v___y_3915_);
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
                v_declName_x3f_3927_ = leanh::lean_ctor_get(v___y_3921_, 0);
                v_macroStack_3928_ = leanh::lean_ctor_get(v___y_3921_, 1);
                v_mayPostpone_3929_ = leanh::lean_ctor_get_uint8(
                    v___y_3921_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 8) as u32,
                );
                v_errToSorry_3930_ = leanh::lean_ctor_get_uint8(
                    v___y_3921_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 8 + 1) as u32,
                );
                v_autoBoundImplicitContext_3931_ = leanh::lean_ctor_get(v___y_3921_, 2);
                v_autoBoundImplicitForbidden_3932_ = leanh::lean_ctor_get(v___y_3921_, 3);
                v_sectionVars_3933_ = leanh::lean_ctor_get(v___y_3921_, 4);
                v_sectionFVars_3934_ = leanh::lean_ctor_get(v___y_3921_, 5);
                v_implicitLambda_3935_ = leanh::lean_ctor_get_uint8(
                    v___y_3921_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 8 + 2) as u32,
                );
                v_heedElabAsElim_3936_ = leanh::lean_ctor_get_uint8(
                    v___y_3921_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 8 + 3) as u32,
                );
                v_isNoncomputableSection_3937_ = leanh::lean_ctor_get_uint8(
                    v___y_3921_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 8 + 4) as u32,
                );
                v_isMetaSection_3938_ = leanh::lean_ctor_get_uint8(
                    v___y_3921_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 8 + 5) as u32,
                );
                v_inPattern_3939_ = leanh::lean_ctor_get_uint8(
                    v___y_3921_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 8 + 7) as u32,
                );
                v_tacSnap_x3f_3940_ = leanh::lean_ctor_get(v___y_3921_, 6);
                v_saveRecAppSyntax_3941_ = leanh::lean_ctor_get_uint8(
                    v___y_3921_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 8 + 8) as u32,
                );
                v_holesAsSyntheticOpaque_3942_ = leanh::lean_ctor_get_uint8(
                    v___y_3921_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 8 + 9) as u32,
                );
                v_checkDeprecated_3943_ = leanh::lean_ctor_get_uint8(
                    v___y_3921_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 8 + 10) as u32,
                );
                v_fixedTermElabs_3944_ = leanh::lean_ctor_get(v___y_3921_, 7);
                v___x_3945_ = leanh::lean_unsigned_to_nat(2);
                v___x_3946_ = l_Lean_Syntax_getArg(v_stx_3584_, v___x_3945_);
                v___x_3947_ = leanh::lean_box(0);
                v___x_3948_ = leanh::lean_box((v___x_3583_) as usize);
                leanh::lean_inc(v___x_3946_);
                v___f_3949_ = leanh::lean_alloc_closure(
                    l_Lean_Elab_Tactic_Conv_evalPattern___lam__1___boxed as *mut core::ffi::c_void,
                    10,
                    3,
                );
                leanh::lean_closure_set(v___f_3949_, 0, v___x_3946_);
                leanh::lean_closure_set(v___f_3949_, 1, v___x_3947_);
                leanh::lean_closure_set(v___f_3949_, 2, v___x_3948_);
                v___f_3950_ = leanh::lean_alloc_closure(
                    l_Lean_Elab_Tactic_Conv_evalPattern___lam__2___boxed as *mut core::ffi::c_void,
                    9,
                    2,
                );
                leanh::lean_closure_set(v___f_3950_, 0, v___x_3946_);
                leanh::lean_closure_set(v___f_3950_, 1, v___f_3949_);
                leanh::lean_inc_ref(v_fixedTermElabs_3944_);
                leanh::lean_inc(v_tacSnap_x3f_3940_);
                leanh::lean_inc(v_sectionFVars_3934_);
                leanh::lean_inc(v_sectionVars_3933_);
                leanh::lean_inc_ref(v_autoBoundImplicitForbidden_3932_);
                leanh::lean_inc(v_autoBoundImplicitContext_3931_);
                leanh::lean_inc(v_macroStack_3928_);
                leanh::lean_inc(v_declName_x3f_3927_);
                v___x_3951_ = leanh::lean_alloc_ctor(0, 8, (11) as u32);
                leanh::lean_ctor_set(v___x_3951_, 0, v_declName_x3f_3927_);
                leanh::lean_ctor_set(v___x_3951_, 1, v_macroStack_3928_);
                leanh::lean_ctor_set(v___x_3951_, 2, v_autoBoundImplicitContext_3931_);
                leanh::lean_ctor_set(v___x_3951_, 3, v_autoBoundImplicitForbidden_3932_);
                leanh::lean_ctor_set(v___x_3951_, 4, v_sectionVars_3933_);
                leanh::lean_ctor_set(v___x_3951_, 5, v_sectionFVars_3934_);
                leanh::lean_ctor_set(v___x_3951_, 6, v_tacSnap_x3f_3940_);
                leanh::lean_ctor_set(v___x_3951_, 7, v_fixedTermElabs_3944_);
                leanh::lean_ctor_set_uint8(
                    v___x_3951_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 8) as u32,
                    v_mayPostpone_3929_,
                );
                leanh::lean_ctor_set_uint8(
                    v___x_3951_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 8 + 1) as u32,
                    v_errToSorry_3930_,
                );
                leanh::lean_ctor_set_uint8(
                    v___x_3951_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 8 + 2) as u32,
                    v_implicitLambda_3935_,
                );
                leanh::lean_ctor_set_uint8(
                    v___x_3951_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 8 + 3) as u32,
                    v_heedElabAsElim_3936_,
                );
                leanh::lean_ctor_set_uint8(
                    v___x_3951_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 8 + 4) as u32,
                    v_isNoncomputableSection_3937_,
                );
                leanh::lean_ctor_set_uint8(
                    v___x_3951_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 8 + 5) as u32,
                    v_isMetaSection_3938_,
                );
                leanh::lean_ctor_set_uint8(
                    v___x_3951_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 8 + 6) as u32,
                    v___x_3583_,
                );
                leanh::lean_ctor_set_uint8(
                    v___x_3951_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 8 + 7) as u32,
                    v_inPattern_3939_,
                );
                leanh::lean_ctor_set_uint8(
                    v___x_3951_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 8 + 8) as u32,
                    v_saveRecAppSyntax_3941_,
                );
                leanh::lean_ctor_set_uint8(
                    v___x_3951_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 8 + 9) as u32,
                    v_holesAsSyntheticOpaque_3942_,
                );
                leanh::lean_ctor_set_uint8(
                    v___x_3951_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 8 + 10) as u32,
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
                leanh::lean_dec_ref_known(v___x_3951_, 8);
                if leanh::lean_obj_tag(v___x_3952_) == 0 {
                    v_a_3953_ = leanh::lean_ctor_get(v___x_3952_, 0);
                    leanh::lean_inc(v_a_3953_);
                    leanh::lean_dec_ref_known(v___x_3952_, 1);
                    v___x_3954_ = l_Lean_Elab_Tactic_Conv_getLhs___redArg(
                        v___y_3920_,
                        v___y_3923_,
                        v___y_3924_,
                        v___y_3925_,
                        v___y_3926_,
                    );
                    if leanh::lean_obj_tag(v___x_3954_) == 0 {
                        v_a_3955_ = leanh::lean_ctor_get(v___x_3954_, 0);
                        leanh::lean_inc(v_a_3955_);
                        leanh::lean_dec_ref_known(v___x_3954_, 1);
                        v___x_3956_ = leanh::lean_box((v___x_3583_) as usize);
                        v___f_3957_ = leanh::lean_alloc_closure(
                            l_Lean_Elab_Tactic_Conv_evalPattern___lam__3___boxed
                                as *mut core::ffi::c_void,
                            11,
                            2,
                        );
                        leanh::lean_closure_set(v___f_3957_, 0, v___x_3947_);
                        leanh::lean_closure_set(v___f_3957_, 1, v___x_3956_);
                        v___f_3958_ = l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__18;
                        v___f_3959_ = l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__19;
                        if leanh::lean_obj_tag(v_occs_3918_) == 0 {
                            leanh::lean_dec_ref(v___x_3588_);
                            leanh::lean_dec_ref(v___x_3587_);
                            leanh::lean_dec_ref(v___x_3586_);
                            leanh::lean_dec_ref(v___x_3585_);
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
                            v_val_3961_ = leanh::lean_ctor_get(v_occs_3918_, 0);
                            leanh::lean_inc_n(v_val_3961_, 2);
                            leanh::lean_dec_ref_known(v_occs_3918_, 1);
                            v___x_3962_ = l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___closed__23;
                            leanh::lean_inc_ref(v___x_3588_);
                            leanh::lean_inc_ref(v___x_3587_);
                            leanh::lean_inc_ref(v___x_3586_);
                            leanh::lean_inc_ref(v___x_3585_);
                            v___x_3963_ = l_Lean_Name_mkStr5(
                                v___x_3585_,
                                v___x_3586_,
                                v___x_3587_,
                                v___x_3588_,
                                v___x_3962_,
                            );
                            v___x_3964_ = l_Lean_Syntax_isOfKind(v_val_3961_, v___x_3963_);
                            leanh::lean_dec(v___x_3963_);
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
                                leanh::lean_inc(v_val_3961_);
                                v___x_3967_ = l_Lean_Syntax_isOfKind(v_val_3961_, v___x_3966_);
                                leanh::lean_dec(v___x_3966_);
                                if v___x_3967_ == 0 {
                                    leanh::lean_dec(v_val_3961_);
                                    leanh::lean_dec_ref(v___f_3957_);
                                    leanh::lean_dec(v_a_3955_);
                                    leanh::lean_dec(v_a_3953_);
                                    leanh::lean_dec_ref(v___f_3582_);
                                    v___x_3968_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__0___redArg();
                                    v_a_3969_ = leanh::lean_ctor_get(v___x_3968_, 0);
                                    v_isSharedCheck_3976_ =
                                        (!leanh::lean_is_exclusive(v___x_3968_)) as u8;
                                    if v_isSharedCheck_3976_ == 0 {
                                        v___x_3971_ = v___x_3968_;
                                        v_isShared_3972_ = v_isSharedCheck_3976_;
                                        state = 35;
                                        continue;
                                    } else {
                                        leanh::lean_inc(v_a_3969_);
                                        leanh::lean_dec(v___x_3968_);
                                        v___x_3971_ = leanh::lean_box(0);
                                        v_isShared_3972_ = v_isSharedCheck_3976_;
                                        state = 35;
                                        continue;
                                    }
                                } else {
                                    v___x_3977_ = l_Lean_Syntax_getArg(v_val_3961_, v___x_3690_);
                                    leanh::lean_dec(v_val_3961_);
                                    v___x_3978_ = l_Lean_Syntax_getArgs(v___x_3977_);
                                    leanh::lean_dec(v___x_3977_);
                                    v___x_3979_ = lean_array_get_size(v___x_3978_);
                                    v___x_3980_ = lean_mk_empty_array_with_capacity(v___x_3979_);
                                    v___x_3981_ = l_Array_mapFinIdxM_map___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__7___redArg(v___x_3978_, v___x_3979_, v___x_3690_, v___x_3980_, v___y_3919_, v___y_3920_, v___y_3921_, v___y_3922_, v___y_3923_, v___y_3924_, v___y_3925_, v___y_3926_);
                                    leanh::lean_dec_ref(v___x_3978_);
                                    if leanh::lean_obj_tag(v___x_3981_) == 0 {
                                        v_a_3982_ = leanh::lean_ctor_get(v___x_3981_, 0);
                                        leanh::lean_inc(v_a_3982_);
                                        leanh::lean_dec_ref_known(v___x_3981_, 1);
                                        v___x_3983_ = lean_array_get_size(v_a_3982_);
                                        v___x_3984_ = lean_nat_dec_eq(v___x_3983_, v___x_3690_);
                                        if v___x_3984_ == 0 {
                                            v___x_3985_ = lean_nat_sub(v___x_3983_, v___x_3691_);
                                            v___x_3986_ = lean_nat_dec_le(v___x_3690_, v___x_3985_);
                                            if v___x_3986_ == 0 {
                                                leanh::lean_inc(v___x_3985_);
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
                                        leanh::lean_dec_ref(v___f_3957_);
                                        leanh::lean_dec(v_a_3955_);
                                        leanh::lean_dec(v_a_3953_);
                                        leanh::lean_dec_ref(v___f_3582_);
                                        v_a_3987_ = leanh::lean_ctor_get(v___x_3981_, 0);
                                        v_isSharedCheck_3994_ =
                                            (!leanh::lean_is_exclusive(v___x_3981_)) as u8;
                                        if v_isSharedCheck_3994_ == 0 {
                                            v___x_3989_ = v___x_3981_;
                                            v_isShared_3990_ = v_isSharedCheck_3994_;
                                            state = 37;
                                            continue;
                                        } else {
                                            leanh::lean_inc(v_a_3987_);
                                            leanh::lean_dec(v___x_3981_);
                                            v___x_3989_ = leanh::lean_box(0);
                                            v_isShared_3990_ = v_isSharedCheck_3994_;
                                            state = 37;
                                            continue;
                                        }
                                    }
                                }
                            } else {
                                leanh::lean_dec(v_val_3961_);
                                leanh::lean_dec_ref(v___x_3588_);
                                leanh::lean_dec_ref(v___x_3587_);
                                leanh::lean_dec_ref(v___x_3586_);
                                leanh::lean_dec_ref(v___x_3585_);
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
                        leanh::lean_dec(v_a_3953_);
                        leanh::lean_dec(v_occs_3918_);
                        leanh::lean_dec_ref(v___x_3588_);
                        leanh::lean_dec_ref(v___x_3587_);
                        leanh::lean_dec_ref(v___x_3586_);
                        leanh::lean_dec_ref(v___x_3585_);
                        leanh::lean_dec_ref(v___f_3582_);
                        v_a_3996_ = leanh::lean_ctor_get(v___x_3954_, 0);
                        v_isSharedCheck_4003_ =
                            (!leanh::lean_is_exclusive(v___x_3954_)) as u8;
                        if v_isSharedCheck_4003_ == 0 {
                            v___x_3998_ = v___x_3954_;
                            v_isShared_3999_ = v_isSharedCheck_4003_;
                            state = 39;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_3996_);
                            leanh::lean_dec(v___x_3954_);
                            v___x_3998_ = leanh::lean_box(0);
                            v_isShared_3999_ = v_isSharedCheck_4003_;
                            state = 39;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_dec(v_occs_3918_);
                    leanh::lean_dec_ref(v___x_3588_);
                    leanh::lean_dec_ref(v___x_3587_);
                    leanh::lean_dec_ref(v___x_3586_);
                    leanh::lean_dec_ref(v___x_3585_);
                    leanh::lean_dec_ref(v___f_3582_);
                    v_a_4004_ = leanh::lean_ctor_get(v___x_3952_, 0);
                    v_isSharedCheck_4011_ = (!leanh::lean_is_exclusive(v___x_3952_)) as u8;
                    if v_isSharedCheck_4011_ == 0 {
                        v___x_4006_ = v___x_3952_;
                        v_isShared_4007_ = v_isSharedCheck_4011_;
                        state = 41;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_4004_);
                        leanh::lean_dec(v___x_3952_);
                        v___x_4006_ = leanh::lean_box(0);
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
                    v_reuseFailAlloc_3975_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3975_, 0, v_a_3969_);
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
                    v_reuseFailAlloc_3993_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3993_, 0, v_a_3987_);
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
                    v_reuseFailAlloc_4002_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4002_, 0, v_a_3996_);
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
                    v_reuseFailAlloc_4010_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4010_, 0, v_a_4004_);
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
    _args: *mut *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4025_: *mut leanh::LeanObject = *_args.add(0);
    let mut v___f_4026_: *mut leanh::LeanObject = *_args.add(1);
    let mut v___x_4027_: *mut leanh::LeanObject = *_args.add(2);
    let mut v_stx_4028_: *mut leanh::LeanObject = *_args.add(3);
    let mut v___x_4029_: *mut leanh::LeanObject = *_args.add(4);
    let mut v___x_4030_: *mut leanh::LeanObject = *_args.add(5);
    let mut v___x_4031_: *mut leanh::LeanObject = *_args.add(6);
    let mut v___x_4032_: *mut leanh::LeanObject = *_args.add(7);
    let mut v___y_4033_: *mut leanh::LeanObject = *_args.add(8);
    let mut v___y_4034_: *mut leanh::LeanObject = *_args.add(9);
    let mut v___y_4035_: *mut leanh::LeanObject = *_args.add(10);
    let mut v___y_4036_: *mut leanh::LeanObject = *_args.add(11);
    let mut v___y_4037_: *mut leanh::LeanObject = *_args.add(12);
    let mut v___y_4038_: *mut leanh::LeanObject = *_args.add(13);
    let mut v___y_4039_: *mut leanh::LeanObject = *_args.add(14);
    let mut v___y_4040_: *mut leanh::LeanObject = *_args.add(15);
    let mut v___y_4041_: *mut leanh::LeanObject = *_args.add(16);
    let mut v___x_19478__boxed_4042_: u8 = 0;
    let mut v___x_19480__boxed_4043_: u8 = 0;
    let mut v_res_4044_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_19478__boxed_4042_ = (leanh::lean_unbox(v___x_4025_) as u8);
    v___x_19480__boxed_4043_ = (leanh::lean_unbox(v___x_4027_) as u8);
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
    leanh::lean_dec(v___y_4040_);
    leanh::lean_dec_ref(v___y_4039_);
    leanh::lean_dec(v___y_4038_);
    leanh::lean_dec_ref(v___y_4037_);
    leanh::lean_dec(v___y_4036_);
    leanh::lean_dec_ref(v___y_4035_);
    leanh::lean_dec(v___y_4034_);
    leanh::lean_dec_ref(v___y_4033_);
    leanh::lean_dec(v_stx_4028_);
    return v_res_4044_;
}
pub unsafe fn l_Lean_Elab_Tactic_Conv_evalPattern(
    mut v_stx_4057_: *mut leanh::LeanObject,
    mut v_a_4058_: *mut leanh::LeanObject,
    mut v_a_4059_: *mut leanh::LeanObject,
    mut v_a_4060_: *mut leanh::LeanObject,
    mut v_a_4061_: *mut leanh::LeanObject,
    mut v_a_4062_: *mut leanh::LeanObject,
    mut v_a_4063_: *mut leanh::LeanObject,
    mut v_a_4064_: *mut leanh::LeanObject,
    mut v_a_4065_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_4067_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4068_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4069_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4070_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4071_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4072_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4073_: u8 = 0;
    let mut v___x_4074_: u8 = 0;
    let mut v___x_4075_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4076_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4077_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4078_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_4067_ = l_Lean_Elab_Tactic_Conv_evalPattern___closed__0;
    v___x_4068_ = l_Lean_Elab_Tactic_Conv_evalPattern___closed__1;
    v___x_4069_ = l_Lean_Elab_Tactic_Conv_evalPattern___closed__2;
    v___x_4070_ = l_Lean_Elab_Tactic_Conv_evalPattern___closed__3;
    v___x_4071_ = l_Lean_Elab_Tactic_Conv_evalPattern___closed__4;
    v___x_4072_ = l_Lean_Elab_Tactic_Conv_evalPattern___closed__6;
    leanh::lean_inc(v_stx_4057_);
    v___x_4073_ = l_Lean_Syntax_isOfKind(v_stx_4057_, v___x_4072_);
    v___x_4074_ = 1;
    v___x_4075_ = leanh::lean_box((v___x_4073_) as usize);
    v___x_4076_ = leanh::lean_box((v___x_4074_) as usize);
    v___y_4077_ = leanh::lean_alloc_closure(
        l_Lean_Elab_Tactic_Conv_evalPattern___lam__6___boxed as *mut core::ffi::c_void,
        17,
        8,
    );
    leanh::lean_closure_set(v___y_4077_, 0, v___x_4075_);
    leanh::lean_closure_set(v___y_4077_, 1, v___f_4067_);
    leanh::lean_closure_set(v___y_4077_, 2, v___x_4076_);
    leanh::lean_closure_set(v___y_4077_, 3, v_stx_4057_);
    leanh::lean_closure_set(v___y_4077_, 4, v___x_4068_);
    leanh::lean_closure_set(v___y_4077_, 5, v___x_4069_);
    leanh::lean_closure_set(v___y_4077_, 6, v___x_4070_);
    leanh::lean_closure_set(v___y_4077_, 7, v___x_4071_);
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
    mut v_stx_4079_: *mut leanh::LeanObject,
    mut v_a_4080_: *mut leanh::LeanObject,
    mut v_a_4081_: *mut leanh::LeanObject,
    mut v_a_4082_: *mut leanh::LeanObject,
    mut v_a_4083_: *mut leanh::LeanObject,
    mut v_a_4084_: *mut leanh::LeanObject,
    mut v_a_4085_: *mut leanh::LeanObject,
    mut v_a_4086_: *mut leanh::LeanObject,
    mut v_a_4087_: *mut leanh::LeanObject,
    mut v_a_4088_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4089_: *mut leanh::LeanObject = core::ptr::null_mut();
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
    leanh::lean_dec(v_a_4087_);
    leanh::lean_dec_ref(v_a_4086_);
    leanh::lean_dec(v_a_4085_);
    leanh::lean_dec_ref(v_a_4084_);
    leanh::lean_dec(v_a_4083_);
    leanh::lean_dec_ref(v_a_4082_);
    leanh::lean_dec(v_a_4081_);
    leanh::lean_dec_ref(v_a_4080_);
    return v_res_4089_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__1(
    mut v_00_u03b1_4090_: *mut leanh::LeanObject,
    mut v_ref_4091_: *mut leanh::LeanObject,
    mut v_msg_4092_: *mut leanh::LeanObject,
    mut v___y_4093_: *mut leanh::LeanObject,
    mut v___y_4094_: *mut leanh::LeanObject,
    mut v___y_4095_: *mut leanh::LeanObject,
    mut v___y_4096_: *mut leanh::LeanObject,
    mut v___y_4097_: *mut leanh::LeanObject,
    mut v___y_4098_: *mut leanh::LeanObject,
    mut v___y_4099_: *mut leanh::LeanObject,
    mut v___y_4100_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4102_: *mut leanh::LeanObject = core::ptr::null_mut();
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
    mut v_00_u03b1_4103_: *mut leanh::LeanObject,
    mut v_ref_4104_: *mut leanh::LeanObject,
    mut v_msg_4105_: *mut leanh::LeanObject,
    mut v___y_4106_: *mut leanh::LeanObject,
    mut v___y_4107_: *mut leanh::LeanObject,
    mut v___y_4108_: *mut leanh::LeanObject,
    mut v___y_4109_: *mut leanh::LeanObject,
    mut v___y_4110_: *mut leanh::LeanObject,
    mut v___y_4111_: *mut leanh::LeanObject,
    mut v___y_4112_: *mut leanh::LeanObject,
    mut v___y_4113_: *mut leanh::LeanObject,
    mut v___y_4114_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4115_: *mut leanh::LeanObject = core::ptr::null_mut();
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
    leanh::lean_dec(v___y_4113_);
    leanh::lean_dec_ref(v___y_4112_);
    leanh::lean_dec(v___y_4111_);
    leanh::lean_dec_ref(v___y_4110_);
    leanh::lean_dec(v___y_4109_);
    leanh::lean_dec_ref(v___y_4108_);
    leanh::lean_dec(v___y_4107_);
    leanh::lean_dec_ref(v___y_4106_);
    leanh::lean_dec(v_ref_4104_);
    return v_res_4115_;
}
pub unsafe fn l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__3(
    mut v_mvarId_4116_: *mut leanh::LeanObject,
    mut v_val_4117_: *mut leanh::LeanObject,
    mut v___y_4118_: *mut leanh::LeanObject,
    mut v___y_4119_: *mut leanh::LeanObject,
    mut v___y_4120_: *mut leanh::LeanObject,
    mut v___y_4121_: *mut leanh::LeanObject,
    mut v___y_4122_: *mut leanh::LeanObject,
    mut v___y_4123_: *mut leanh::LeanObject,
    mut v___y_4124_: *mut leanh::LeanObject,
    mut v___y_4125_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4127_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4127_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__3___redArg(
        v_mvarId_4116_,
        v_val_4117_,
        v___y_4123_,
    );
    return v___x_4127_;
}
pub unsafe fn l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__3___boxed(
    mut v_mvarId_4128_: *mut leanh::LeanObject,
    mut v_val_4129_: *mut leanh::LeanObject,
    mut v___y_4130_: *mut leanh::LeanObject,
    mut v___y_4131_: *mut leanh::LeanObject,
    mut v___y_4132_: *mut leanh::LeanObject,
    mut v___y_4133_: *mut leanh::LeanObject,
    mut v___y_4134_: *mut leanh::LeanObject,
    mut v___y_4135_: *mut leanh::LeanObject,
    mut v___y_4136_: *mut leanh::LeanObject,
    mut v___y_4137_: *mut leanh::LeanObject,
    mut v___y_4138_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4139_: *mut leanh::LeanObject = core::ptr::null_mut();
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
    leanh::lean_dec(v___y_4137_);
    leanh::lean_dec_ref(v___y_4136_);
    leanh::lean_dec(v___y_4135_);
    leanh::lean_dec_ref(v___y_4134_);
    leanh::lean_dec(v___y_4133_);
    leanh::lean_dec_ref(v___y_4132_);
    leanh::lean_dec(v___y_4131_);
    leanh::lean_dec_ref(v___y_4130_);
    return v_res_4139_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__4(
    mut v_00_u03b1_4140_: *mut leanh::LeanObject,
    mut v_msg_4141_: *mut leanh::LeanObject,
    mut v___y_4142_: *mut leanh::LeanObject,
    mut v___y_4143_: *mut leanh::LeanObject,
    mut v___y_4144_: *mut leanh::LeanObject,
    mut v___y_4145_: *mut leanh::LeanObject,
    mut v___y_4146_: *mut leanh::LeanObject,
    mut v___y_4147_: *mut leanh::LeanObject,
    mut v___y_4148_: *mut leanh::LeanObject,
    mut v___y_4149_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4151_: *mut leanh::LeanObject = core::ptr::null_mut();
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
    mut v_00_u03b1_4152_: *mut leanh::LeanObject,
    mut v_msg_4153_: *mut leanh::LeanObject,
    mut v___y_4154_: *mut leanh::LeanObject,
    mut v___y_4155_: *mut leanh::LeanObject,
    mut v___y_4156_: *mut leanh::LeanObject,
    mut v___y_4157_: *mut leanh::LeanObject,
    mut v___y_4158_: *mut leanh::LeanObject,
    mut v___y_4159_: *mut leanh::LeanObject,
    mut v___y_4160_: *mut leanh::LeanObject,
    mut v___y_4161_: *mut leanh::LeanObject,
    mut v___y_4162_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4163_: *mut leanh::LeanObject = core::ptr::null_mut();
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
    leanh::lean_dec(v___y_4161_);
    leanh::lean_dec_ref(v___y_4160_);
    leanh::lean_dec(v___y_4159_);
    leanh::lean_dec_ref(v___y_4158_);
    leanh::lean_dec(v___y_4157_);
    leanh::lean_dec_ref(v___y_4156_);
    leanh::lean_dec(v___y_4155_);
    leanh::lean_dec_ref(v___y_4154_);
    return v_res_4163_;
}
pub unsafe fn l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__6(
    mut v_n_4164_: *mut leanh::LeanObject,
    mut v_as_4165_: *mut leanh::LeanObject,
    mut v_lo_4166_: *mut leanh::LeanObject,
    mut v_hi_4167_: *mut leanh::LeanObject,
    mut v_w_4168_: *mut leanh::LeanObject,
    mut v_hlo_4169_: *mut leanh::LeanObject,
    mut v_hhi_4170_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4171_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4171_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__6___redArg(v_n_4164_, v_as_4165_, v_lo_4166_, v_hi_4167_);
    return v___x_4171_;
}
pub unsafe fn l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__6___boxed(
    mut v_n_4172_: *mut leanh::LeanObject,
    mut v_as_4173_: *mut leanh::LeanObject,
    mut v_lo_4174_: *mut leanh::LeanObject,
    mut v_hi_4175_: *mut leanh::LeanObject,
    mut v_w_4176_: *mut leanh::LeanObject,
    mut v_hlo_4177_: *mut leanh::LeanObject,
    mut v_hhi_4178_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4179_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4179_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__6(v_n_4172_, v_as_4173_, v_lo_4174_, v_hi_4175_, v_w_4176_, v_hlo_4177_, v_hhi_4178_);
    leanh::lean_dec(v_hi_4175_);
    leanh::lean_dec(v_n_4172_);
    return v_res_4179_;
}
pub unsafe fn l_Array_mapFinIdxM_map___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__7(
    mut v_as_4180_: *mut leanh::LeanObject,
    mut v_i_4181_: *mut leanh::LeanObject,
    mut v_j_4182_: *mut leanh::LeanObject,
    mut v_inv_4183_: *mut leanh::LeanObject,
    mut v_bs_4184_: *mut leanh::LeanObject,
    mut v___y_4185_: *mut leanh::LeanObject,
    mut v___y_4186_: *mut leanh::LeanObject,
    mut v___y_4187_: *mut leanh::LeanObject,
    mut v___y_4188_: *mut leanh::LeanObject,
    mut v___y_4189_: *mut leanh::LeanObject,
    mut v___y_4190_: *mut leanh::LeanObject,
    mut v___y_4191_: *mut leanh::LeanObject,
    mut v___y_4192_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4194_: *mut leanh::LeanObject = core::ptr::null_mut();
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
    mut v_as_4195_: *mut leanh::LeanObject,
    mut v_i_4196_: *mut leanh::LeanObject,
    mut v_j_4197_: *mut leanh::LeanObject,
    mut v_inv_4198_: *mut leanh::LeanObject,
    mut v_bs_4199_: *mut leanh::LeanObject,
    mut v___y_4200_: *mut leanh::LeanObject,
    mut v___y_4201_: *mut leanh::LeanObject,
    mut v___y_4202_: *mut leanh::LeanObject,
    mut v___y_4203_: *mut leanh::LeanObject,
    mut v___y_4204_: *mut leanh::LeanObject,
    mut v___y_4205_: *mut leanh::LeanObject,
    mut v___y_4206_: *mut leanh::LeanObject,
    mut v___y_4207_: *mut leanh::LeanObject,
    mut v___y_4208_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4209_: *mut leanh::LeanObject = core::ptr::null_mut();
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
    leanh::lean_dec(v___y_4207_);
    leanh::lean_dec_ref(v___y_4206_);
    leanh::lean_dec(v___y_4205_);
    leanh::lean_dec_ref(v___y_4204_);
    leanh::lean_dec(v___y_4203_);
    leanh::lean_dec_ref(v___y_4202_);
    leanh::lean_dec(v___y_4201_);
    leanh::lean_dec_ref(v___y_4200_);
    leanh::lean_dec_ref(v_as_4195_);
    return v_res_4209_;
}
pub unsafe fn l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__9(
    mut v_n_4210_: *mut leanh::LeanObject,
    mut v_as_4211_: *mut leanh::LeanObject,
    mut v_lo_4212_: *mut leanh::LeanObject,
    mut v_hi_4213_: *mut leanh::LeanObject,
    mut v_w_4214_: *mut leanh::LeanObject,
    mut v_hlo_4215_: *mut leanh::LeanObject,
    mut v_hhi_4216_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4217_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4217_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__9___redArg(v_n_4210_, v_as_4211_, v_lo_4212_, v_hi_4213_);
    return v___x_4217_;
}
pub unsafe fn l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__9___boxed(
    mut v_n_4218_: *mut leanh::LeanObject,
    mut v_as_4219_: *mut leanh::LeanObject,
    mut v_lo_4220_: *mut leanh::LeanObject,
    mut v_hi_4221_: *mut leanh::LeanObject,
    mut v_w_4222_: *mut leanh::LeanObject,
    mut v_hlo_4223_: *mut leanh::LeanObject,
    mut v_hhi_4224_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4225_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4225_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__9(v_n_4218_, v_as_4219_, v_lo_4220_, v_hi_4221_, v_w_4222_, v_hlo_4223_, v_hhi_4224_);
    leanh::lean_dec(v_hi_4221_);
    leanh::lean_dec(v_n_4218_);
    return v_res_4225_;
}
pub unsafe fn l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__3_spec__3(
    mut v_00_u03b2_4226_: *mut leanh::LeanObject,
    mut v_x_4227_: *mut leanh::LeanObject,
    mut v_x_4228_: *mut leanh::LeanObject,
    mut v_x_4229_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4230_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4230_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__3_spec__3___redArg(v_x_4227_, v_x_4228_, v_x_4229_);
    return v___x_4230_;
}
pub unsafe fn l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__6_spec__8(
    mut v_n_4231_: *mut leanh::LeanObject,
    mut v_lo_4232_: *mut leanh::LeanObject,
    mut v_hi_4233_: *mut leanh::LeanObject,
    mut v_hhi_4234_: *mut leanh::LeanObject,
    mut v_pivot_4235_: *mut leanh::LeanObject,
    mut v_as_4236_: *mut leanh::LeanObject,
    mut v_i_4237_: *mut leanh::LeanObject,
    mut v_k_4238_: *mut leanh::LeanObject,
    mut v_ilo_4239_: *mut leanh::LeanObject,
    mut v_ik_4240_: *mut leanh::LeanObject,
    mut v_w_4241_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4242_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4242_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__6_spec__8___redArg(v_hi_4233_, v_pivot_4235_, v_as_4236_, v_i_4237_, v_k_4238_);
    return v___x_4242_;
}
pub unsafe fn l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__6_spec__8___boxed(
    mut v_n_4243_: *mut leanh::LeanObject,
    mut v_lo_4244_: *mut leanh::LeanObject,
    mut v_hi_4245_: *mut leanh::LeanObject,
    mut v_hhi_4246_: *mut leanh::LeanObject,
    mut v_pivot_4247_: *mut leanh::LeanObject,
    mut v_as_4248_: *mut leanh::LeanObject,
    mut v_i_4249_: *mut leanh::LeanObject,
    mut v_k_4250_: *mut leanh::LeanObject,
    mut v_ilo_4251_: *mut leanh::LeanObject,
    mut v_ik_4252_: *mut leanh::LeanObject,
    mut v_w_4253_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4254_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4254_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__6_spec__8(v_n_4243_, v_lo_4244_, v_hi_4245_, v_hhi_4246_, v_pivot_4247_, v_as_4248_, v_i_4249_, v_k_4250_, v_ilo_4251_, v_ik_4252_, v_w_4253_);
    leanh::lean_dec_ref(v_pivot_4247_);
    leanh::lean_dec(v_hi_4245_);
    leanh::lean_dec(v_lo_4244_);
    leanh::lean_dec(v_n_4243_);
    return v_res_4254_;
}
pub unsafe fn l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__9_spec__13(
    mut v_n_4255_: *mut leanh::LeanObject,
    mut v_lo_4256_: *mut leanh::LeanObject,
    mut v_hi_4257_: *mut leanh::LeanObject,
    mut v_hhi_4258_: *mut leanh::LeanObject,
    mut v_pivot_4259_: *mut leanh::LeanObject,
    mut v_as_4260_: *mut leanh::LeanObject,
    mut v_i_4261_: *mut leanh::LeanObject,
    mut v_k_4262_: *mut leanh::LeanObject,
    mut v_ilo_4263_: *mut leanh::LeanObject,
    mut v_ik_4264_: *mut leanh::LeanObject,
    mut v_w_4265_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4266_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4266_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__9_spec__13___redArg(v_hi_4257_, v_pivot_4259_, v_as_4260_, v_i_4261_, v_k_4262_);
    return v___x_4266_;
}
pub unsafe fn l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__9_spec__13___boxed(
    mut v_n_4267_: *mut leanh::LeanObject,
    mut v_lo_4268_: *mut leanh::LeanObject,
    mut v_hi_4269_: *mut leanh::LeanObject,
    mut v_hhi_4270_: *mut leanh::LeanObject,
    mut v_pivot_4271_: *mut leanh::LeanObject,
    mut v_as_4272_: *mut leanh::LeanObject,
    mut v_i_4273_: *mut leanh::LeanObject,
    mut v_k_4274_: *mut leanh::LeanObject,
    mut v_ilo_4275_: *mut leanh::LeanObject,
    mut v_ik_4276_: *mut leanh::LeanObject,
    mut v_w_4277_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4278_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4278_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__9_spec__13(v_n_4267_, v_lo_4268_, v_hi_4269_, v_hhi_4270_, v_pivot_4271_, v_as_4272_, v_i_4273_, v_k_4274_, v_ilo_4275_, v_ik_4276_, v_w_4277_);
    leanh::lean_dec_ref(v_pivot_4271_);
    leanh::lean_dec(v_hi_4269_);
    leanh::lean_dec(v_lo_4268_);
    leanh::lean_dec(v_n_4267_);
    return v_res_4278_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__3_spec__3_spec__4(
    mut v_00_u03b2_4279_: *mut leanh::LeanObject,
    mut v_x_4280_: *mut leanh::LeanObject,
    mut v_x_4281_: usize,
    mut v_x_4282_: usize,
    mut v_x_4283_: *mut leanh::LeanObject,
    mut v_x_4284_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4285_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4285_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__3_spec__3_spec__4___redArg(v_x_4280_, v_x_4281_, v_x_4282_, v_x_4283_, v_x_4284_);
    return v___x_4285_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__3_spec__3_spec__4___boxed(
    mut v_00_u03b2_4286_: *mut leanh::LeanObject,
    mut v_x_4287_: *mut leanh::LeanObject,
    mut v_x_4288_: *mut leanh::LeanObject,
    mut v_x_4289_: *mut leanh::LeanObject,
    mut v_x_4290_: *mut leanh::LeanObject,
    mut v_x_4291_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_x_20596__boxed_4292_: usize = 0;
    let mut v_x_20597__boxed_4293_: usize = 0;
    let mut v_res_4294_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_x_20596__boxed_4292_ = leanh::lean_unbox_usize(v_x_4288_);
    leanh::lean_dec(v_x_4288_);
    v_x_20597__boxed_4293_ = leanh::lean_unbox_usize(v_x_4289_);
    leanh::lean_dec(v_x_4289_);
    v_res_4294_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__3_spec__3_spec__4(v_00_u03b2_4286_, v_x_4287_, v_x_20596__boxed_4292_, v_x_20597__boxed_4293_, v_x_4290_, v_x_4291_);
    return v_res_4294_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_allDiffAuxAux___at___00__private_Init_Data_Array_Basic_0__Array_allDiffAux___at___00Array_allDiff___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__8_spec__11_spec__13(
    mut v_as_4295_: *mut leanh::LeanObject,
    mut v_a_4296_: *mut leanh::LeanObject,
    mut v_x_4297_: *mut leanh::LeanObject,
    mut v_x_4298_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_4299_: u8 = 0;
    v___x_4299_ = l___private_Init_Data_Array_Basic_0__Array_allDiffAuxAux___at___00__private_Init_Data_Array_Basic_0__Array_allDiffAux___at___00Array_allDiff___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__8_spec__11_spec__13___redArg(v_as_4295_, v_a_4296_, v_x_4297_);
    return v___x_4299_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_allDiffAuxAux___at___00__private_Init_Data_Array_Basic_0__Array_allDiffAux___at___00Array_allDiff___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__8_spec__11_spec__13___boxed(
    mut v_as_4300_: *mut leanh::LeanObject,
    mut v_a_4301_: *mut leanh::LeanObject,
    mut v_x_4302_: *mut leanh::LeanObject,
    mut v_x_4303_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4304_: u8 = 0;
    let mut v_r_4305_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4304_ = l___private_Init_Data_Array_Basic_0__Array_allDiffAuxAux___at___00__private_Init_Data_Array_Basic_0__Array_allDiffAux___at___00Array_allDiff___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__8_spec__11_spec__13(v_as_4300_, v_a_4301_, v_x_4302_, v_x_4303_);
    leanh::lean_dec_ref(v_a_4301_);
    leanh::lean_dec_ref(v_as_4300_);
    v_r_4305_ = leanh::lean_box((v_res_4304_) as usize);
    return v_r_4305_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__3_spec__3_spec__4_spec__12(
    mut v_00_u03b2_4306_: *mut leanh::LeanObject,
    mut v_n_4307_: *mut leanh::LeanObject,
    mut v_k_4308_: *mut leanh::LeanObject,
    mut v_v_4309_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4310_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4310_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__3_spec__3_spec__4_spec__12___redArg(v_n_4307_, v_k_4308_, v_v_4309_);
    return v___x_4310_;
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__3_spec__3_spec__4_spec__13(
    mut v_00_u03b2_4311_: *mut leanh::LeanObject,
    mut v_depth_4312_: usize,
    mut v_keys_4313_: *mut leanh::LeanObject,
    mut v_vals_4314_: *mut leanh::LeanObject,
    mut v_heq_4315_: *mut leanh::LeanObject,
    mut v_i_4316_: *mut leanh::LeanObject,
    mut v_entries_4317_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4318_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4318_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__3_spec__3_spec__4_spec__13___redArg(v_depth_4312_, v_keys_4313_, v_vals_4314_, v_i_4316_, v_entries_4317_);
    return v___x_4318_;
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__3_spec__3_spec__4_spec__13___boxed(
    mut v_00_u03b2_4319_: *mut leanh::LeanObject,
    mut v_depth_4320_: *mut leanh::LeanObject,
    mut v_keys_4321_: *mut leanh::LeanObject,
    mut v_vals_4322_: *mut leanh::LeanObject,
    mut v_heq_4323_: *mut leanh::LeanObject,
    mut v_i_4324_: *mut leanh::LeanObject,
    mut v_entries_4325_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_depth_boxed_4326_: usize = 0;
    let mut v_res_4327_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_depth_boxed_4326_ = leanh::lean_unbox_usize(v_depth_4320_);
    leanh::lean_dec(v_depth_4320_);
    v_res_4327_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__3_spec__3_spec__4_spec__13(v_00_u03b2_4319_, v_depth_boxed_4326_, v_keys_4321_, v_vals_4322_, v_heq_4323_, v_i_4324_, v_entries_4325_);
    leanh::lean_dec_ref(v_vals_4322_);
    leanh::lean_dec_ref(v_keys_4321_);
    return v_res_4327_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__3_spec__3_spec__4_spec__12_spec__16(
    mut v_00_u03b2_4328_: *mut leanh::LeanObject,
    mut v_x_4329_: *mut leanh::LeanObject,
    mut v_x_4330_: *mut leanh::LeanObject,
    mut v_x_4331_: *mut leanh::LeanObject,
    mut v_x_4332_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4333_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4333_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Conv_evalPattern_spec__3_spec__3_spec__4_spec__12_spec__16___redArg(v_x_4329_, v_x_4330_, v_x_4331_, v_x_4332_);
    return v___x_4333_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Conv_Pattern_0__Lean_Elab_Tactic_Conv_evalPattern___regBuiltin_Lean_Elab_Tactic_Conv_evalPattern__1()
-> *mut leanh::LeanObject {
    let mut v___x_4343_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4344_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4345_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4346_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4347_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4343_ = l_Lean_Elab_Tactic_tacticElabAttribute;
    v___x_4344_ = l_Lean_Elab_Tactic_Conv_evalPattern___closed__6;
    v___x_4345_ = l___private_Lean_Elab_Tactic_Conv_Pattern_0__Lean_Elab_Tactic_Conv_evalPattern___regBuiltin_Lean_Elab_Tactic_Conv_evalPattern__1___closed__2;
    v___x_4346_ = leanh::lean_alloc_closure(
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
    mut v_a_4348_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4349_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4349_ = l___private_Lean_Elab_Tactic_Conv_Pattern_0__Lean_Elab_Tactic_Conv_evalPattern___regBuiltin_Lean_Elab_Tactic_Conv_evalPattern__1();
    return v_res_4349_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Conv_Pattern_0__Lean_Elab_Tactic_Conv_evalPattern___regBuiltin_Lean_Elab_Tactic_Conv_evalPattern_declRange__3()
-> *mut leanh::LeanObject {
    let mut v___x_4376_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4377_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4378_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4376_ = l___private_Lean_Elab_Tactic_Conv_Pattern_0__Lean_Elab_Tactic_Conv_evalPattern___regBuiltin_Lean_Elab_Tactic_Conv_evalPattern__1___closed__2;
    v___x_4377_ = l___private_Lean_Elab_Tactic_Conv_Pattern_0__Lean_Elab_Tactic_Conv_evalPattern___regBuiltin_Lean_Elab_Tactic_Conv_evalPattern_declRange__3___closed__6;
    v___x_4378_ = l_Lean_addBuiltinDeclarationRanges(v___x_4376_, v___x_4377_);
    return v___x_4378_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Conv_Pattern_0__Lean_Elab_Tactic_Conv_evalPattern___regBuiltin_Lean_Elab_Tactic_Conv_evalPattern_declRange__3___boxed(
    mut v_a_4379_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4380_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4380_ = l___private_Lean_Elab_Tactic_Conv_Pattern_0__Lean_Elab_Tactic_Conv_evalPattern___regBuiltin_Lean_Elab_Tactic_Conv_evalPattern_declRange__3();
    return v_res_4380_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Elab_Tactic_Conv_Pattern(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Elab_Tactic_Simp(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_Tactic_Conv_Basic(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = l___private_Lean_Elab_Tactic_Conv_Pattern_0__Lean_Elab_Tactic_Conv_evalPattern___regBuiltin_Lean_Elab_Tactic_Conv_evalPattern__1();
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = l___private_Lean_Elab_Tactic_Conv_Pattern_0__Lean_Elab_Tactic_Conv_evalPattern___regBuiltin_Lean_Elab_Tactic_Conv_evalPattern_declRange__3();
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Elab_Tactic_Conv_Pattern(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Elab_Tactic_Conv_Pattern(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Elab_Tactic_Simp(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Lean_Elab_Tactic_Conv_Basic(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_Tactic_Conv_Pattern(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Elab_Tactic_Conv_Pattern(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return initialize_Lean_Elab_Tactic_Conv_Pattern(builtin);
}