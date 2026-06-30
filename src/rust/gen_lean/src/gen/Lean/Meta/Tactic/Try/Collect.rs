// Lean compiler output
// Module: Lean.Meta.Tactic.Try.Collect
// Imports: Init.Try Lean.Meta.Tactic.LibrarySearch Lean.Meta.Tactic.FunIndCollect
use crate::ffi::{
    lean_array_fget, lean_array_fset, lean_array_get, lean_array_get_size, lean_array_push,
    lean_array_set, lean_array_size, lean_array_uget, lean_array_uget_borrowed, lean_array_uset,
    lean_mk_array, lean_mk_empty_array_with_capacity, lean_name_eq, lean_nat_add, lean_nat_dec_eq,
    lean_nat_dec_le, lean_nat_dec_lt, lean_nat_div, lean_nat_mul, lean_nat_sub, lean_ptr_addr,
    lean_st_mk_ref, lean_st_ref_get, lean_st_ref_set, lean_st_ref_take, lean_uint64_mix_hash,
    lean_uint64_of_nat, lean_uint64_shift_right, lean_uint64_to_usize, lean_uint64_xor,
    lean_usize_add, lean_usize_dec_eq, lean_usize_dec_lt, lean_usize_land, lean_usize_of_nat,
    lean_usize_sub, lean_usize_to_uint64,
};
use crate::r#gen::Init::Prelude::{
    l_Lean_Name_append, l_Lean_Name_hasMacroScopes, l_Lean_replaceRef,
};
use crate::r#gen::Init::Try::{initialize_Init_Try, runtime_initialize_Init_Try};
use crate::r#gen::Lean::CoreM::l_Lean_Exception_isRuntime;
use crate::r#gen::Lean::Data::Name::{l_Lean_Name_isAnonymous, l_Lean_Name_isPrefixOf};
use crate::r#gen::Lean::Data::Options::l_Lean_Options_empty;
use crate::r#gen::Lean::Data::PersistentHashMap::l_Lean_PersistentHashMap_mkEmptyEntriesArray;
use crate::r#gen::Lean::Environment::{
    l_Lean_Environment_contains, l_Lean_Environment_find_x3f,
    l_Lean_Environment_getModuleIdxFor_x3f, l_Lean_Environment_header,
    l_Lean_Environment_setExporting, l_Lean_EnvironmentHeader_moduleNames,
};
use crate::r#gen::Lean::Exception::{
    l_Lean_Exception_isInterrupt, l_Lean_unknownIdentifierMessageTag,
};
use crate::r#gen::Lean::Expr::{
    l_Lean_Expr_getAppFn, l_Lean_Expr_getAppNumArgs, l_Lean_Expr_hasLooseBVars,
    l_Lean_Expr_sort___override,
};
use crate::r#gen::Lean::LocalContext::{
    l_Lean_LocalDecl_fvarId, l_Lean_LocalDecl_isAuxDecl, l_Lean_LocalDecl_type,
    l_Lean_LocalDecl_value_x3f,
};
use crate::r#gen::Lean::Message::{
    l_Lean_MessageData_note, l_Lean_MessageData_ofConstName, l_Lean_MessageData_ofName,
    l_Lean_stringToMessageData,
};
use crate::r#gen::Lean::Meta::Basic::{
    l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp, l_Lean_Meta_whnfD,
};
use crate::r#gen::Lean::Meta::Eqns::l_Lean_Meta_getEqnsFor_x3f;
use crate::r#gen::Lean::Meta::Tactic::FunIndCollect::{
    initialize_Lean_Meta_Tactic_FunIndCollect, l_Lean_Meta_FunInd_SeenCalls_push,
    runtime_initialize_Lean_Meta_Tactic_FunIndCollect,
};
use crate::r#gen::Lean::Meta::Tactic::FunIndInfo::l_Lean_Meta_getFunIndInfo_x3f;
use crate::r#gen::Lean::Meta::Tactic::Grind::Attr::{
    l_Lean_Meta_Grind_grindExt, l_Lean_Meta_Grind_isGlobalSplit___redArg,
};
use crate::r#gen::Lean::Meta::Tactic::Grind::EMatchTheorem::l_Lean_Meta_Grind_Extension_isEMatchTheorem___redArg;
use crate::r#gen::Lean::Meta::Tactic::Grind::Extension::{
    l_Lean_Meta_Grind_instBEqEMatchTheoremKind_beq,
    l_Lean_Meta_Grind_instHashableEMatchTheoremKind_hash,
};
use crate::r#gen::Lean::Meta::Tactic::LibrarySearch::{
    initialize_Lean_Meta_Tactic_LibrarySearch, l_Lean_Meta_LibrarySearch_libSearchFindDecls,
    runtime_initialize_Lean_Meta_Tactic_LibrarySearch,
};
use crate::r#gen::Lean::Meta::Tactic::Util::l_Lean_MVarId_getType;
use crate::r#gen::Lean::PrivateName::l_Lean_isPrivateName;
use crate::r#gen::Lean::ReservedNameAction::l_Lean_realizeGlobalConstNoOverloadCore;
use crate::r#gen::Lean::Util::PtrSet::l_Lean_mkPtrSet___redArg;
use crate::r#gen::Std::Data::DHashMap::Internal::Defs::{
    l_Std_DHashMap_Internal_Raw_u2080_contains___redArg,
    l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___redArg,
};
pub static l_Lean_Meta_Try_Collector_instInhabitedOrdSet_default___closed__0_value:
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
static mut l_Lean_Meta_Try_Collector_instInhabitedOrdSet_default___closed__0:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Try_Collector_instInhabitedOrdSet_default___closed__0_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Meta_Try_Collector_instInhabitedOrdSet_default___closed__1_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Try_Collector_instInhabitedOrdSet_default___closed__1:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Meta_Try_Collector_instInhabitedOrdSet_default___closed__2_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Try_Collector_instInhabitedOrdSet_default___closed__2:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Meta_Try_Collector_instInhabitedOrdSet_default___closed__3_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Try_Collector_instInhabitedOrdSet_default___closed__3:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Try_Collector_OrdSet_insert___at___00Lean_Meta_Try_Collector_saveConst_spec__0_spec__0___redArg___closed__0_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Try_Collector_OrdSet_insert___at___00Lean_Meta_Try_Collector_saveConst_spec__0_spec__0___redArg___closed__0: u64 = 0;
pub static l_Lean_Meta_Try_Collector_getEqDefDecl_x3f___redArg___closed__0_value:
    leanh::LeanStringObject<7> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 7,
    m_capacity: 7,
    m_length: 6,
    m_data: [101, 113, 95, 100, 101, 102, 0],
};
static mut l_Lean_Meta_Try_Collector_getEqDefDecl_x3f___redArg___closed__0:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Try_Collector_getEqDefDecl_x3f___redArg___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Meta_Try_Collector_getEqDefDecl_x3f___redArg___closed__1_value:
    leanh::LeanCtorObject<3> = leanh::LeanCtorObject {
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
        core::ptr::addr_of!(l_Lean_Meta_Try_Collector_getEqDefDecl_x3f___redArg___closed__0_value)
            as *mut leanh::LeanObject,
        17192571042771754225 as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_Try_Collector_getEqDefDecl_x3f___redArg___closed__1:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Try_Collector_getEqDefDecl_x3f___redArg___closed__1_value)
        as *mut leanh::LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Try_Collector_checkInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__0_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Try_Collector_checkInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__0: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Try_Collector_checkInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__1_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Try_Collector_checkInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__1: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Try_Collector_checkInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__2_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Try_Collector_checkInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__2: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Try_Collector_checkInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__3_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Try_Collector_checkInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__3: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Try_Collector_checkInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__4_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Try_Collector_checkInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__4: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Try_Collector_checkInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__5_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Try_Collector_checkInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__5: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Try_Collector_checkInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__6_value: leanh::LeanStringObject<24> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 24, m_capacity: 24, m_length: 23, m_data: [65, 32, 112, 114, 105, 118, 97, 116, 101, 32, 100, 101, 99, 108, 97, 114, 97, 116, 105, 111, 110, 32, 96, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Try_Collector_checkInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__6: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Try_Collector_checkInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__6_value) as *mut leanh::LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Try_Collector_checkInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__7_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Try_Collector_checkInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__7: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Try_Collector_checkInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__8_value: leanh::LeanStringObject<79> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 79, m_capacity: 79, m_length: 78, m_data: [96, 32, 40, 102, 114, 111, 109, 32, 116, 104, 101, 32, 99, 117, 114, 114, 101, 110, 116, 32, 109, 111, 100, 117, 108, 101, 41, 32, 101, 120, 105, 115, 116, 115, 32, 98, 117, 116, 32, 119, 111, 117, 108, 100, 32, 110, 101, 101, 100, 32, 116, 111, 32, 98, 101, 32, 112, 117, 98, 108, 105, 99, 32, 116, 111, 32, 97, 99, 99, 101, 115, 115, 32, 104, 101, 114, 101, 46, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Try_Collector_checkInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__8: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Try_Collector_checkInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__8_value) as *mut leanh::LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Try_Collector_checkInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__9_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Try_Collector_checkInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__9: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Try_Collector_checkInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__10_value: leanh::LeanStringObject<23> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 23, m_capacity: 23, m_length: 22, m_data: [65, 32, 112, 117, 98, 108, 105, 99, 32, 100, 101, 99, 108, 97, 114, 97, 116, 105, 111, 110, 32, 96, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Try_Collector_checkInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__10: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Try_Collector_checkInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__10_value) as *mut leanh::LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Try_Collector_checkInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__11_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Try_Collector_checkInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__11: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Try_Collector_checkInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__12_value: leanh::LeanStringObject<68> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 68, m_capacity: 68, m_length: 67, m_data: [96, 32, 101, 120, 105, 115, 116, 115, 32, 98, 117, 116, 32, 105, 115, 32, 105, 109, 112, 111, 114, 116, 101, 100, 32, 112, 114, 105, 118, 97, 116, 101, 108, 121, 59, 32, 99, 111, 110, 115, 105, 100, 101, 114, 32, 97, 100, 100, 105, 110, 103, 32, 96, 112, 117, 98, 108, 105, 99, 32, 105, 109, 112, 111, 114, 116, 32, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Try_Collector_checkInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__12: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Try_Collector_checkInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__12_value) as *mut leanh::LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Try_Collector_checkInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__13_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Try_Collector_checkInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__13: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Try_Collector_checkInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__14_value: leanh::LeanStringObject<3> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [96, 46, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Try_Collector_checkInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__14: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Try_Collector_checkInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__14_value) as *mut leanh::LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Try_Collector_checkInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__15_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Try_Collector_checkInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__15: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Try_Collector_checkInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__16_value: leanh::LeanStringObject<10> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [96, 32, 40, 102, 114, 111, 109, 32, 96, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Try_Collector_checkInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__16: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Try_Collector_checkInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__16_value) as *mut leanh::LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Try_Collector_checkInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__17_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Try_Collector_checkInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__17: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Try_Collector_checkInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__18_value: leanh::LeanStringObject<54> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 54, m_capacity: 54, m_length: 53, m_data: [96, 41, 32, 101, 120, 105, 115, 116, 115, 32, 98, 117, 116, 32, 119, 111, 117, 108, 100, 32, 110, 101, 101, 100, 32, 116, 111, 32, 98, 101, 32, 112, 117, 98, 108, 105, 99, 32, 116, 111, 32, 97, 99, 99, 101, 115, 115, 32, 104, 101, 114, 101, 46, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Try_Collector_checkInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__18: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Try_Collector_checkInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__18_value) as *mut leanh::LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Try_Collector_checkInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__19_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Try_Collector_checkInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__19: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Try_Collector_checkInductive_spec__0_spec__0_spec__1___redArg___closed__0_value: leanh::LeanStringObject<19> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 19, m_capacity: 19, m_length: 18, m_data: [85, 110, 107, 110, 111, 119, 110, 32, 99, 111, 110, 115, 116, 97, 110, 116, 32, 96, 0]};
static mut l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Try_Collector_checkInductive_spec__0_spec__0_spec__1___redArg___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Try_Collector_checkInductive_spec__0_spec__0_spec__1___redArg___closed__0_value) as *mut leanh::LeanObject;
static mut l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Try_Collector_checkInductive_spec__0_spec__0_spec__1___redArg___closed__1_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Try_Collector_checkInductive_spec__0_spec__0_spec__1___redArg___closed__1: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Try_Collector_checkInductive_spec__0_spec__0_spec__1___redArg___closed__2_value: leanh::LeanStringObject<2> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [96, 0]};
static mut l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Try_Collector_checkInductive_spec__0_spec__0_spec__1___redArg___closed__2: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Try_Collector_checkInductive_spec__0_spec__0_spec__1___redArg___closed__2_value) as *mut leanh::LeanObject;
static mut l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Try_Collector_checkInductive_spec__0_spec__0_spec__1___redArg___closed__3_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Try_Collector_checkInductive_spec__0_spec__0_spec__1___redArg___closed__3: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Meta_Try_Collector_visit___closed__0_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Try_Collector_visit___closed__0: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Meta_Try_Collector_main___closed__0_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Try_Collector_main___closed__0: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_Try_Collector_main___closed__1_value: leanh::LeanArrayObject<0> =
    leanh::LeanArrayObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<usize>() * 2
                + core::mem::size_of::<*mut leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 246,
        },
        m_size: 0,
        m_capacity: 0,
        m_data: [],
    };
static mut l_Lean_Meta_Try_Collector_main___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Try_Collector_main___closed__1_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Meta_Try_Collector_main___closed__2_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Try_Collector_main___closed__2: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Meta_Try_Collector_main___closed__3_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Try_Collector_main___closed__3: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Meta_Try_Collector_main___closed__4_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Try_Collector_main___closed__4: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Meta_Try_Collector_main___closed__5_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Try_Collector_main___closed__5: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Meta_Try_Collector_main___closed__6_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Try_Collector_main___closed__6: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub unsafe fn _init_l_Lean_Meta_Try_Collector_instInhabitedOrdSet_default___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_2769_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2770_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2771_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2769_ = leanh::lean_box(0);
    v___x_2770_ = leanh::lean_unsigned_to_nat(16);
    v___x_2771_ = lean_mk_array(v___x_2770_, v___x_2769_);
    return v___x_2771_;
}
pub unsafe fn _init_l_Lean_Meta_Try_Collector_instInhabitedOrdSet_default___closed__2()
-> *mut leanh::LeanObject {
    let mut v___x_2772_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2773_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2774_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2772_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Try_Collector_instInhabitedOrdSet_default___closed__1),
        core::ptr::addr_of_mut!(
            l_Lean_Meta_Try_Collector_instInhabitedOrdSet_default___closed__1_once
        ),
        _init_l_Lean_Meta_Try_Collector_instInhabitedOrdSet_default___closed__1,
    );
    v___x_2773_ = leanh::lean_unsigned_to_nat(0);
    v___x_2774_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_2774_, 0, v___x_2773_);
    leanh::lean_ctor_set(v___x_2774_, 1, v___x_2772_);
    return v___x_2774_;
}
pub unsafe fn _init_l_Lean_Meta_Try_Collector_instInhabitedOrdSet_default___closed__3()
-> *mut leanh::LeanObject {
    let mut v___x_2775_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2776_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2777_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2775_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Try_Collector_instInhabitedOrdSet_default___closed__2),
        core::ptr::addr_of_mut!(
            l_Lean_Meta_Try_Collector_instInhabitedOrdSet_default___closed__2_once
        ),
        _init_l_Lean_Meta_Try_Collector_instInhabitedOrdSet_default___closed__2,
    );
    v___x_2776_ = l_Lean_Meta_Try_Collector_instInhabitedOrdSet_default___closed__0;
    v___x_2777_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_2777_, 0, v___x_2776_);
    leanh::lean_ctor_set(v___x_2777_, 1, v___x_2775_);
    return v___x_2777_;
}
pub unsafe fn l_Lean_Meta_Try_Collector_instInhabitedOrdSet_default(
    mut v_00_u03b1_2778_: *mut leanh::LeanObject,
    mut v_inst_2779_: *mut leanh::LeanObject,
    mut v_inst_2780_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2781_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2781_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Try_Collector_instInhabitedOrdSet_default___closed__3),
        core::ptr::addr_of_mut!(
            l_Lean_Meta_Try_Collector_instInhabitedOrdSet_default___closed__3_once
        ),
        _init_l_Lean_Meta_Try_Collector_instInhabitedOrdSet_default___closed__3,
    );
    return v___x_2781_;
}
pub unsafe fn l_Lean_Meta_Try_Collector_instInhabitedOrdSet_default___boxed(
    mut v_00_u03b1_2782_: *mut leanh::LeanObject,
    mut v_inst_2783_: *mut leanh::LeanObject,
    mut v_inst_2784_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2785_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2785_ = l_Lean_Meta_Try_Collector_instInhabitedOrdSet_default(
        v_00_u03b1_2782_,
        v_inst_2783_,
        v_inst_2784_,
    );
    leanh::lean_dec_ref(v_inst_2784_);
    leanh::lean_dec_ref(v_inst_2783_);
    return v_res_2785_;
}
pub unsafe fn l_Lean_Meta_Try_Collector_instInhabitedOrdSet___redArg(
    mut v_a_2786_: *mut leanh::LeanObject,
    mut v_a_2787_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2788_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2788_ = l_Lean_Meta_Try_Collector_instInhabitedOrdSet_default(
        leanh::lean_box(0),
        v_a_2786_,
        v_a_2787_,
    );
    return v___x_2788_;
}
pub unsafe fn l_Lean_Meta_Try_Collector_instInhabitedOrdSet___redArg___boxed(
    mut v_a_2789_: *mut leanh::LeanObject,
    mut v_a_2790_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2791_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2791_ = l_Lean_Meta_Try_Collector_instInhabitedOrdSet___redArg(v_a_2789_, v_a_2790_);
    leanh::lean_dec_ref(v_a_2790_);
    leanh::lean_dec_ref(v_a_2789_);
    return v_res_2791_;
}
pub unsafe fn l_Lean_Meta_Try_Collector_instInhabitedOrdSet(
    mut v_a_2792_: *mut leanh::LeanObject,
    mut v_a_2793_: *mut leanh::LeanObject,
    mut v_a_2794_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2795_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2795_ = l_Lean_Meta_Try_Collector_instInhabitedOrdSet_default(
        leanh::lean_box(0),
        v_a_2793_,
        v_a_2794_,
    );
    return v___x_2795_;
}
pub unsafe fn l_Lean_Meta_Try_Collector_instInhabitedOrdSet___boxed(
    mut v_a_2796_: *mut leanh::LeanObject,
    mut v_a_2797_: *mut leanh::LeanObject,
    mut v_a_2798_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2799_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2799_ = l_Lean_Meta_Try_Collector_instInhabitedOrdSet(v_a_2796_, v_a_2797_, v_a_2798_);
    leanh::lean_dec_ref(v_a_2798_);
    leanh::lean_dec_ref(v_a_2797_);
    return v_res_2799_;
}
pub unsafe fn l_Lean_Meta_Try_Collector_OrdSet_insert___redArg(
    mut v_x_2800_: *mut leanh::LeanObject,
    mut v_x_2801_: *mut leanh::LeanObject,
    mut v_s_2802_: *mut leanh::LeanObject,
    mut v_a_2803_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_elems_2804_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_set_2805_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2806_: u8 = 0;
    let mut v___x_2808_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2809_: u8 = 0;
    let mut v___x_2810_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2811_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2812_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2814_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2815_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2816_: u8 = 0;
    let mut v_unused_2817_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2818_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_elems_2804_ = leanh::lean_ctor_get(v_s_2802_, 0);
                v_set_2805_ = leanh::lean_ctor_get(v_s_2802_, 1);
                leanh::lean_inc(v_a_2803_);
                leanh::lean_inc_ref(v_x_2800_);
                leanh::lean_inc_ref(v_x_2801_);
                v___x_2806_ = l_Std_DHashMap_Internal_Raw_u2080_contains___redArg(
                    v_x_2801_,
                    v_x_2800_,
                    v_set_2805_,
                    v_a_2803_,
                );
                if v___x_2806_ == 0 {
                    leanh::lean_inc_ref(v_set_2805_);
                    leanh::lean_inc_ref(v_elems_2804_);
                    v_isSharedCheck_2816_ = (!leanh::lean_is_exclusive(v_s_2802_)) as u8;
                    if v_isSharedCheck_2816_ == 0 {
                        v_unused_2817_ = leanh::lean_ctor_get(v_s_2802_, 1);
                        leanh::lean_dec(v_unused_2817_);
                        v_unused_2818_ = leanh::lean_ctor_get(v_s_2802_, 0);
                        leanh::lean_dec(v_unused_2818_);
                        v___x_2808_ = v_s_2802_;
                        v_isShared_2809_ = v_isSharedCheck_2816_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_dec(v_s_2802_);
                        v___x_2808_ = leanh::lean_box(0);
                        v_isShared_2809_ = v_isSharedCheck_2816_;
                        state = 1;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v_a_2803_);
                    leanh::lean_dec_ref(v_x_2801_);
                    leanh::lean_dec_ref(v_x_2800_);
                    return v_s_2802_;
                }
            }
            1 => {
                leanh::lean_inc(v_a_2803_);
                v___x_2810_ = lean_array_push(v_elems_2804_, v_a_2803_);
                v___x_2811_ = leanh::lean_box(0);
                v___x_2812_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___redArg(
                    v_x_2801_,
                    v_x_2800_,
                    v_set_2805_,
                    v_a_2803_,
                    v___x_2811_,
                );
                if v_isShared_2809_ == 0 {
                    leanh::lean_ctor_set(v___x_2808_, 1, v___x_2812_);
                    leanh::lean_ctor_set(v___x_2808_, 0, v___x_2810_);
                    v___x_2814_ = v___x_2808_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2815_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2815_, 0, v___x_2810_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2815_, 1, v___x_2812_);
                    v___x_2814_ = v_reuseFailAlloc_2815_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2814_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Try_Collector_OrdSet_insert(
    mut v_00_u03b1_2819_: *mut leanh::LeanObject,
    mut v_x_2820_: *mut leanh::LeanObject,
    mut v_x_2821_: *mut leanh::LeanObject,
    mut v_s_2822_: *mut leanh::LeanObject,
    mut v_a_2823_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2824_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2824_ = l_Lean_Meta_Try_Collector_OrdSet_insert___redArg(
        v_x_2820_, v_x_2821_, v_s_2822_, v_a_2823_,
    );
    return v___x_2824_;
}
pub unsafe fn l_Lean_Meta_Try_Collector_OrdSet_isEmpty___redArg(
    mut v_s_2825_: *mut leanh::LeanObject,
) -> u8 {
    let mut v_elems_2826_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2827_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2828_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2829_: u8 = 0;
    v_elems_2826_ = leanh::lean_ctor_get(v_s_2825_, 0);
    v___x_2827_ = lean_array_get_size(v_elems_2826_);
    v___x_2828_ = leanh::lean_unsigned_to_nat(0);
    v___x_2829_ = lean_nat_dec_eq(v___x_2827_, v___x_2828_);
    return v___x_2829_;
}
pub unsafe fn l_Lean_Meta_Try_Collector_OrdSet_isEmpty___redArg___boxed(
    mut v_s_2830_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2831_: u8 = 0;
    let mut v_r_2832_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2831_ = l_Lean_Meta_Try_Collector_OrdSet_isEmpty___redArg(v_s_2830_);
    leanh::lean_dec_ref(v_s_2830_);
    v_r_2832_ = leanh::lean_box((v_res_2831_) as usize);
    return v_r_2832_;
}
pub unsafe fn l_Lean_Meta_Try_Collector_OrdSet_isEmpty(
    mut v_00_u03b1_2833_: *mut leanh::LeanObject,
    mut v_x_2834_: *mut leanh::LeanObject,
    mut v_x_2835_: *mut leanh::LeanObject,
    mut v_s_2836_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_2837_: u8 = 0;
    v___x_2837_ = l_Lean_Meta_Try_Collector_OrdSet_isEmpty___redArg(v_s_2836_);
    return v___x_2837_;
}
pub unsafe fn l_Lean_Meta_Try_Collector_OrdSet_isEmpty___boxed(
    mut v_00_u03b1_2838_: *mut leanh::LeanObject,
    mut v_x_2839_: *mut leanh::LeanObject,
    mut v_x_2840_: *mut leanh::LeanObject,
    mut v_s_2841_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2842_: u8 = 0;
    let mut v_r_2843_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2842_ =
        l_Lean_Meta_Try_Collector_OrdSet_isEmpty(v_00_u03b1_2838_, v_x_2839_, v_x_2840_, v_s_2841_);
    leanh::lean_dec_ref(v_s_2841_);
    leanh::lean_dec_ref(v_x_2840_);
    leanh::lean_dec_ref(v_x_2839_);
    v_r_2843_ = leanh::lean_box((v_res_2842_) as usize);
    return v_r_2843_;
}
pub unsafe fn l_Lean_Meta_Try_Collector_getConfig___redArg(
    mut v_a_2844_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2846_: *mut leanh::LeanObject = core::ptr::null_mut();
    leanh::lean_inc_ref(v_a_2844_);
    v___x_2846_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_2846_, 0, v_a_2844_);
    return v___x_2846_;
}
pub unsafe fn l_Lean_Meta_Try_Collector_getConfig___redArg___boxed(
    mut v_a_2847_: *mut leanh::LeanObject,
    mut v_a_2848_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2849_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2849_ = l_Lean_Meta_Try_Collector_getConfig___redArg(v_a_2847_);
    leanh::lean_dec_ref(v_a_2847_);
    return v_res_2849_;
}
pub unsafe fn l_Lean_Meta_Try_Collector_getConfig(
    mut v_a_2850_: *mut leanh::LeanObject,
    mut v_a_2851_: *mut leanh::LeanObject,
    mut v_a_2852_: *mut leanh::LeanObject,
    mut v_a_2853_: *mut leanh::LeanObject,
    mut v_a_2854_: *mut leanh::LeanObject,
    mut v_a_2855_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2857_: *mut leanh::LeanObject = core::ptr::null_mut();
    leanh::lean_inc_ref(v_a_2850_);
    v___x_2857_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_2857_, 0, v_a_2850_);
    return v___x_2857_;
}
pub unsafe fn l_Lean_Meta_Try_Collector_getConfig___boxed(
    mut v_a_2858_: *mut leanh::LeanObject,
    mut v_a_2859_: *mut leanh::LeanObject,
    mut v_a_2860_: *mut leanh::LeanObject,
    mut v_a_2861_: *mut leanh::LeanObject,
    mut v_a_2862_: *mut leanh::LeanObject,
    mut v_a_2863_: *mut leanh::LeanObject,
    mut v_a_2864_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2865_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2865_ = l_Lean_Meta_Try_Collector_getConfig(
        v_a_2858_, v_a_2859_, v_a_2860_, v_a_2861_, v_a_2862_, v_a_2863_,
    );
    leanh::lean_dec(v_a_2863_);
    leanh::lean_dec_ref(v_a_2862_);
    leanh::lean_dec(v_a_2861_);
    leanh::lean_dec_ref(v_a_2860_);
    leanh::lean_dec(v_a_2859_);
    leanh::lean_dec_ref(v_a_2858_);
    return v_res_2865_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Try_Collector_OrdSet_insert___at___00Lean_Meta_Try_Collector_saveConst_spec__0_spec__0_spec__1___redArg(
    mut v_a_2866_: *mut leanh::LeanObject,
    mut v_x_2867_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_2868_: u8 = 0;
    let mut v_key_2869_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_2870_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2871_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_2867_) == 0 {
                    v___x_2868_ = 0;
                    return v___x_2868_;
                } else {
                    v_key_2869_ = leanh::lean_ctor_get(v_x_2867_, 0);
                    v_tail_2870_ = leanh::lean_ctor_get(v_x_2867_, 2);
                    v___x_2871_ = lean_name_eq(v_key_2869_, v_a_2866_);
                    if v___x_2871_ == 0 {
                        v_x_2867_ = v_tail_2870_;
                        state = 0;
                        continue;
                    } else {
                        return v___x_2871_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Try_Collector_OrdSet_insert___at___00Lean_Meta_Try_Collector_saveConst_spec__0_spec__0_spec__1___redArg___boxed(
    mut v_a_2873_: *mut leanh::LeanObject,
    mut v_x_2874_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2875_: u8 = 0;
    let mut v_r_2876_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2875_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Try_Collector_OrdSet_insert___at___00Lean_Meta_Try_Collector_saveConst_spec__0_spec__0_spec__1___redArg(v_a_2873_, v_x_2874_);
    leanh::lean_dec(v_x_2874_);
    leanh::lean_dec(v_a_2873_);
    v_r_2876_ = leanh::lean_box((v_res_2875_) as usize);
    return v_r_2876_;
}
pub unsafe fn _init_l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Try_Collector_OrdSet_insert___at___00Lean_Meta_Try_Collector_saveConst_spec__0_spec__0___redArg___closed__0()
-> u64 {
    let mut v___x_2877_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2878_: u64 = 0;
    v___x_2877_ = leanh::lean_unsigned_to_nat(1723);
    v___x_2878_ = lean_uint64_of_nat(v___x_2877_);
    return v___x_2878_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Try_Collector_OrdSet_insert___at___00Lean_Meta_Try_Collector_saveConst_spec__0_spec__0___redArg(
    mut v_m_2879_: *mut leanh::LeanObject,
    mut v_a_2880_: *mut leanh::LeanObject,
) -> u8 {
    let mut v_buckets_2881_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2882_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2884_: u64 = 0;
    let mut v___x_2885_: u64 = 0;
    let mut v___x_2886_: u64 = 0;
    let mut v_fold_2887_: u64 = 0;
    let mut v___x_2888_: u64 = 0;
    let mut v___x_2889_: u64 = 0;
    let mut v___x_2890_: u64 = 0;
    let mut v___x_2891_: usize = 0;
    let mut v___x_2892_: usize = 0;
    let mut v___x_2893_: usize = 0;
    let mut v___x_2894_: usize = 0;
    let mut v___x_2895_: usize = 0;
    let mut v___x_2896_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2897_: u8 = 0;
    let mut v___x_2898_: u64 = 0;
    let mut v_hash_2899_: u64 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_buckets_2881_ = leanh::lean_ctor_get(v_m_2879_, 1);
                v___x_2882_ = lean_array_get_size(v_buckets_2881_);
                if leanh::lean_obj_tag(v_a_2880_) == 0 {
                    v___x_2898_ = leanh::lean_uint64_once(core::ptr::addr_of_mut!(l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Try_Collector_OrdSet_insert___at___00Lean_Meta_Try_Collector_saveConst_spec__0_spec__0___redArg___closed__0), core::ptr::addr_of_mut!(l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Try_Collector_OrdSet_insert___at___00Lean_Meta_Try_Collector_saveConst_spec__0_spec__0___redArg___closed__0_once), _init_l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Try_Collector_OrdSet_insert___at___00Lean_Meta_Try_Collector_saveConst_spec__0_spec__0___redArg___closed__0);
                    v___y_2884_ = v___x_2898_;
                    state = 1;
                    continue;
                } else {
                    v_hash_2899_ = leanh::lean_ctor_get_uint64(
                        v_a_2880_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 2) as u32,
                    );
                    v___y_2884_ = v_hash_2899_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_2885_ = 32u64;
                v___x_2886_ = lean_uint64_shift_right(v___y_2884_, v___x_2885_);
                v_fold_2887_ = lean_uint64_xor(v___y_2884_, v___x_2886_);
                v___x_2888_ = 16u64;
                v___x_2889_ = lean_uint64_shift_right(v_fold_2887_, v___x_2888_);
                v___x_2890_ = lean_uint64_xor(v_fold_2887_, v___x_2889_);
                v___x_2891_ = lean_uint64_to_usize(v___x_2890_);
                v___x_2892_ = lean_usize_of_nat(v___x_2882_);
                v___x_2893_ = 1usize;
                v___x_2894_ = lean_usize_sub(v___x_2892_, v___x_2893_);
                v___x_2895_ = lean_usize_land(v___x_2891_, v___x_2894_);
                v___x_2896_ = lean_array_uget_borrowed(v_buckets_2881_, v___x_2895_);
                v___x_2897_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Try_Collector_OrdSet_insert___at___00Lean_Meta_Try_Collector_saveConst_spec__0_spec__0_spec__1___redArg(v_a_2880_, v___x_2896_);
                return v___x_2897_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Try_Collector_OrdSet_insert___at___00Lean_Meta_Try_Collector_saveConst_spec__0_spec__0___redArg___boxed(
    mut v_m_2900_: *mut leanh::LeanObject,
    mut v_a_2901_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2902_: u8 = 0;
    let mut v_r_2903_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2902_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Try_Collector_OrdSet_insert___at___00Lean_Meta_Try_Collector_saveConst_spec__0_spec__0___redArg(v_m_2900_, v_a_2901_);
    leanh::lean_dec(v_a_2901_);
    leanh::lean_dec_ref(v_m_2900_);
    v_r_2903_ = leanh::lean_box((v_res_2902_) as usize);
    return v_r_2903_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Try_Collector_OrdSet_insert___at___00Lean_Meta_Try_Collector_saveConst_spec__0_spec__1_spec__3_spec__4_spec__5___redArg(
    mut v_x_2904_: *mut leanh::LeanObject,
    mut v_x_2905_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_key_2906_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_2907_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_2908_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2910_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2911_: u8 = 0;
    let mut v___x_2912_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2914_: u64 = 0;
    let mut v___x_2915_: u64 = 0;
    let mut v___x_2916_: u64 = 0;
    let mut v_fold_2917_: u64 = 0;
    let mut v___x_2918_: u64 = 0;
    let mut v___x_2919_: u64 = 0;
    let mut v___x_2920_: u64 = 0;
    let mut v___x_2921_: usize = 0;
    let mut v___x_2922_: usize = 0;
    let mut v___x_2923_: usize = 0;
    let mut v___x_2924_: usize = 0;
    let mut v___x_2925_: usize = 0;
    let mut v___x_2926_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2928_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2929_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2931_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2932_: u64 = 0;
    let mut v_hash_2933_: u64 = 0;
    let mut v_isSharedCheck_2934_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_2905_) == 0 {
                    return v_x_2904_;
                } else {
                    v_key_2906_ = leanh::lean_ctor_get(v_x_2905_, 0);
                    v_value_2907_ = leanh::lean_ctor_get(v_x_2905_, 1);
                    v_tail_2908_ = leanh::lean_ctor_get(v_x_2905_, 2);
                    v_isSharedCheck_2934_ = (!leanh::lean_is_exclusive(v_x_2905_)) as u8;
                    if v_isSharedCheck_2934_ == 0 {
                        v___x_2910_ = v_x_2905_;
                        v_isShared_2911_ = v_isSharedCheck_2934_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_tail_2908_);
                        leanh::lean_inc(v_value_2907_);
                        leanh::lean_inc(v_key_2906_);
                        leanh::lean_dec(v_x_2905_);
                        v___x_2910_ = leanh::lean_box(0);
                        v_isShared_2911_ = v_isSharedCheck_2934_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_2912_ = lean_array_get_size(v_x_2904_);
                if leanh::lean_obj_tag(v_key_2906_) == 0 {
                    v___x_2932_ = leanh::lean_uint64_once(core::ptr::addr_of_mut!(l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Try_Collector_OrdSet_insert___at___00Lean_Meta_Try_Collector_saveConst_spec__0_spec__0___redArg___closed__0), core::ptr::addr_of_mut!(l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Try_Collector_OrdSet_insert___at___00Lean_Meta_Try_Collector_saveConst_spec__0_spec__0___redArg___closed__0_once), _init_l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Try_Collector_OrdSet_insert___at___00Lean_Meta_Try_Collector_saveConst_spec__0_spec__0___redArg___closed__0);
                    v___y_2914_ = v___x_2932_;
                    state = 2;
                    continue;
                } else {
                    v_hash_2933_ = leanh::lean_ctor_get_uint64(
                        v_key_2906_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 2) as u32,
                    );
                    v___y_2914_ = v_hash_2933_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_2915_ = 32u64;
                v___x_2916_ = lean_uint64_shift_right(v___y_2914_, v___x_2915_);
                v_fold_2917_ = lean_uint64_xor(v___y_2914_, v___x_2916_);
                v___x_2918_ = 16u64;
                v___x_2919_ = lean_uint64_shift_right(v_fold_2917_, v___x_2918_);
                v___x_2920_ = lean_uint64_xor(v_fold_2917_, v___x_2919_);
                v___x_2921_ = lean_uint64_to_usize(v___x_2920_);
                v___x_2922_ = lean_usize_of_nat(v___x_2912_);
                v___x_2923_ = 1usize;
                v___x_2924_ = lean_usize_sub(v___x_2922_, v___x_2923_);
                v___x_2925_ = lean_usize_land(v___x_2921_, v___x_2924_);
                v___x_2926_ = lean_array_uget_borrowed(v_x_2904_, v___x_2925_);
                leanh::lean_inc(v___x_2926_);
                if v_isShared_2911_ == 0 {
                    leanh::lean_ctor_set(v___x_2910_, 2, v___x_2926_);
                    v___x_2928_ = v___x_2910_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2931_ = leanh::lean_alloc_ctor(1, 3, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2931_, 0, v_key_2906_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2931_, 1, v_value_2907_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2931_, 2, v___x_2926_);
                    v___x_2928_ = v_reuseFailAlloc_2931_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_2929_ = lean_array_uset(v_x_2904_, v___x_2925_, v___x_2928_);
                v_x_2904_ = v___x_2929_;
                v_x_2905_ = v_tail_2908_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Try_Collector_OrdSet_insert___at___00Lean_Meta_Try_Collector_saveConst_spec__0_spec__1_spec__3_spec__4___redArg(
    mut v_i_2935_: *mut leanh::LeanObject,
    mut v_source_2936_: *mut leanh::LeanObject,
    mut v_target_2937_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2938_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2939_: u8 = 0;
    let mut v_es_2940_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2941_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_source_2942_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_target_2943_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2944_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2945_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2938_ = lean_array_get_size(v_source_2936_);
                v___x_2939_ = lean_nat_dec_lt(v_i_2935_, v___x_2938_);
                if v___x_2939_ == 0 {
                    leanh::lean_dec_ref(v_source_2936_);
                    leanh::lean_dec(v_i_2935_);
                    return v_target_2937_;
                } else {
                    v_es_2940_ = lean_array_fget(v_source_2936_, v_i_2935_);
                    v___x_2941_ = leanh::lean_box(0);
                    v_source_2942_ = lean_array_fset(v_source_2936_, v_i_2935_, v___x_2941_);
                    v_target_2943_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Try_Collector_OrdSet_insert___at___00Lean_Meta_Try_Collector_saveConst_spec__0_spec__1_spec__3_spec__4_spec__5___redArg(v_target_2937_, v_es_2940_);
                    v___x_2944_ = leanh::lean_unsigned_to_nat(1);
                    v___x_2945_ = lean_nat_add(v_i_2935_, v___x_2944_);
                    leanh::lean_dec(v_i_2935_);
                    v_i_2935_ = v___x_2945_;
                    v_source_2936_ = v_source_2942_;
                    v_target_2937_ = v_target_2943_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Try_Collector_OrdSet_insert___at___00Lean_Meta_Try_Collector_saveConst_spec__0_spec__1_spec__3___redArg(
    mut v_data_2947_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2948_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2949_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_nbuckets_2950_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2951_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2952_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2953_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2954_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2948_ = lean_array_get_size(v_data_2947_);
    v___x_2949_ = leanh::lean_unsigned_to_nat(2);
    v_nbuckets_2950_ = lean_nat_mul(v___x_2948_, v___x_2949_);
    v___x_2951_ = leanh::lean_unsigned_to_nat(0);
    v___x_2952_ = leanh::lean_box(0);
    v___x_2953_ = lean_mk_array(v_nbuckets_2950_, v___x_2952_);
    v___x_2954_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Try_Collector_OrdSet_insert___at___00Lean_Meta_Try_Collector_saveConst_spec__0_spec__1_spec__3_spec__4___redArg(v___x_2951_, v_data_2947_, v___x_2953_);
    return v___x_2954_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Try_Collector_OrdSet_insert___at___00Lean_Meta_Try_Collector_saveConst_spec__0_spec__1___redArg(
    mut v_m_2955_: *mut leanh::LeanObject,
    mut v_a_2956_: *mut leanh::LeanObject,
    mut v_b_2957_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_size_2958_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_2959_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2960_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2962_: u64 = 0;
    let mut v___x_2963_: u64 = 0;
    let mut v___x_2964_: u64 = 0;
    let mut v_fold_2965_: u64 = 0;
    let mut v___x_2966_: u64 = 0;
    let mut v___x_2967_: u64 = 0;
    let mut v___x_2968_: u64 = 0;
    let mut v___x_2969_: usize = 0;
    let mut v___x_2970_: usize = 0;
    let mut v___x_2971_: usize = 0;
    let mut v___x_2972_: usize = 0;
    let mut v___x_2973_: usize = 0;
    let mut v_bkt_2974_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2975_: u8 = 0;
    let mut v___x_2977_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2978_: u8 = 0;
    let mut v___x_2979_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_x27_2980_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2981_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_x27_2982_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2983_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2984_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2985_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2986_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2987_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2988_: u8 = 0;
    let mut v_val_2989_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2991_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2992_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2994_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2995_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2996_: u8 = 0;
    let mut v_unused_2997_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2998_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2999_: u64 = 0;
    let mut v_hash_3000_: u64 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_size_2958_ = leanh::lean_ctor_get(v_m_2955_, 0);
                v_buckets_2959_ = leanh::lean_ctor_get(v_m_2955_, 1);
                v___x_2960_ = lean_array_get_size(v_buckets_2959_);
                if leanh::lean_obj_tag(v_a_2956_) == 0 {
                    v___x_2999_ = leanh::lean_uint64_once(core::ptr::addr_of_mut!(l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Try_Collector_OrdSet_insert___at___00Lean_Meta_Try_Collector_saveConst_spec__0_spec__0___redArg___closed__0), core::ptr::addr_of_mut!(l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Try_Collector_OrdSet_insert___at___00Lean_Meta_Try_Collector_saveConst_spec__0_spec__0___redArg___closed__0_once), _init_l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Try_Collector_OrdSet_insert___at___00Lean_Meta_Try_Collector_saveConst_spec__0_spec__0___redArg___closed__0);
                    v___y_2962_ = v___x_2999_;
                    state = 1;
                    continue;
                } else {
                    v_hash_3000_ = leanh::lean_ctor_get_uint64(
                        v_a_2956_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 2) as u32,
                    );
                    v___y_2962_ = v_hash_3000_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_2963_ = 32u64;
                v___x_2964_ = lean_uint64_shift_right(v___y_2962_, v___x_2963_);
                v_fold_2965_ = lean_uint64_xor(v___y_2962_, v___x_2964_);
                v___x_2966_ = 16u64;
                v___x_2967_ = lean_uint64_shift_right(v_fold_2965_, v___x_2966_);
                v___x_2968_ = lean_uint64_xor(v_fold_2965_, v___x_2967_);
                v___x_2969_ = lean_uint64_to_usize(v___x_2968_);
                v___x_2970_ = lean_usize_of_nat(v___x_2960_);
                v___x_2971_ = 1usize;
                v___x_2972_ = lean_usize_sub(v___x_2970_, v___x_2971_);
                v___x_2973_ = lean_usize_land(v___x_2969_, v___x_2972_);
                v_bkt_2974_ = lean_array_uget_borrowed(v_buckets_2959_, v___x_2973_);
                v___x_2975_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Try_Collector_OrdSet_insert___at___00Lean_Meta_Try_Collector_saveConst_spec__0_spec__0_spec__1___redArg(v_a_2956_, v_bkt_2974_);
                if v___x_2975_ == 0 {
                    leanh::lean_inc_ref(v_buckets_2959_);
                    leanh::lean_inc(v_size_2958_);
                    v_isSharedCheck_2996_ = (!leanh::lean_is_exclusive(v_m_2955_)) as u8;
                    if v_isSharedCheck_2996_ == 0 {
                        v_unused_2997_ = leanh::lean_ctor_get(v_m_2955_, 1);
                        leanh::lean_dec(v_unused_2997_);
                        v_unused_2998_ = leanh::lean_ctor_get(v_m_2955_, 0);
                        leanh::lean_dec(v_unused_2998_);
                        v___x_2977_ = v_m_2955_;
                        v_isShared_2978_ = v_isSharedCheck_2996_;
                        state = 2;
                        continue;
                    } else {
                        leanh::lean_dec(v_m_2955_);
                        v___x_2977_ = leanh::lean_box(0);
                        v_isShared_2978_ = v_isSharedCheck_2996_;
                        state = 2;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v_b_2957_);
                    leanh::lean_dec(v_a_2956_);
                    return v_m_2955_;
                }
            }
            2 => {
                v___x_2979_ = leanh::lean_unsigned_to_nat(1);
                v_size_x27_2980_ = lean_nat_add(v_size_2958_, v___x_2979_);
                leanh::lean_dec(v_size_2958_);
                leanh::lean_inc(v_bkt_2974_);
                v___x_2981_ = leanh::lean_alloc_ctor(1, 3, (0) as u32);
                leanh::lean_ctor_set(v___x_2981_, 0, v_a_2956_);
                leanh::lean_ctor_set(v___x_2981_, 1, v_b_2957_);
                leanh::lean_ctor_set(v___x_2981_, 2, v_bkt_2974_);
                v_buckets_x27_2982_ = lean_array_uset(v_buckets_2959_, v___x_2973_, v___x_2981_);
                v___x_2983_ = leanh::lean_unsigned_to_nat(4);
                v___x_2984_ = lean_nat_mul(v_size_x27_2980_, v___x_2983_);
                v___x_2985_ = leanh::lean_unsigned_to_nat(3);
                v___x_2986_ = lean_nat_div(v___x_2984_, v___x_2985_);
                leanh::lean_dec(v___x_2984_);
                v___x_2987_ = lean_array_get_size(v_buckets_x27_2982_);
                v___x_2988_ = lean_nat_dec_le(v___x_2986_, v___x_2987_);
                leanh::lean_dec(v___x_2986_);
                if v___x_2988_ == 0 {
                    v_val_2989_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Try_Collector_OrdSet_insert___at___00Lean_Meta_Try_Collector_saveConst_spec__0_spec__1_spec__3___redArg(v_buckets_x27_2982_);
                    if v_isShared_2978_ == 0 {
                        leanh::lean_ctor_set(v___x_2977_, 1, v_val_2989_);
                        leanh::lean_ctor_set(v___x_2977_, 0, v_size_x27_2980_);
                        v___x_2991_ = v___x_2977_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_2992_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2992_, 0, v_size_x27_2980_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2992_, 1, v_val_2989_);
                        v___x_2991_ = v_reuseFailAlloc_2992_;
                        state = 3;
                        continue;
                    }
                } else {
                    if v_isShared_2978_ == 0 {
                        leanh::lean_ctor_set(v___x_2977_, 1, v_buckets_x27_2982_);
                        leanh::lean_ctor_set(v___x_2977_, 0, v_size_x27_2980_);
                        v___x_2994_ = v___x_2977_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_2995_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2995_, 0, v_size_x27_2980_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2995_, 1, v_buckets_x27_2982_);
                        v___x_2994_ = v_reuseFailAlloc_2995_;
                        state = 4;
                        continue;
                    }
                }
            }
            3 => {
                return v___x_2991_;
            }
            4 => {
                return v___x_2994_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Try_Collector_OrdSet_insert___at___00Lean_Meta_Try_Collector_saveConst_spec__0(
    mut v_s_3001_: *mut leanh::LeanObject,
    mut v_a_3002_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_elems_3003_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_set_3004_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3005_: u8 = 0;
    let mut v___x_3007_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3008_: u8 = 0;
    let mut v___x_3009_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3010_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3011_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3013_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3014_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3015_: u8 = 0;
    let mut v_unused_3016_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3017_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_elems_3003_ = leanh::lean_ctor_get(v_s_3001_, 0);
                v_set_3004_ = leanh::lean_ctor_get(v_s_3001_, 1);
                v___x_3005_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Try_Collector_OrdSet_insert___at___00Lean_Meta_Try_Collector_saveConst_spec__0_spec__0___redArg(v_set_3004_, v_a_3002_);
                if v___x_3005_ == 0 {
                    leanh::lean_inc_ref(v_set_3004_);
                    leanh::lean_inc_ref(v_elems_3003_);
                    v_isSharedCheck_3015_ = (!leanh::lean_is_exclusive(v_s_3001_)) as u8;
                    if v_isSharedCheck_3015_ == 0 {
                        v_unused_3016_ = leanh::lean_ctor_get(v_s_3001_, 1);
                        leanh::lean_dec(v_unused_3016_);
                        v_unused_3017_ = leanh::lean_ctor_get(v_s_3001_, 0);
                        leanh::lean_dec(v_unused_3017_);
                        v___x_3007_ = v_s_3001_;
                        v_isShared_3008_ = v_isSharedCheck_3015_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_dec(v_s_3001_);
                        v___x_3007_ = leanh::lean_box(0);
                        v_isShared_3008_ = v_isSharedCheck_3015_;
                        state = 1;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v_a_3002_);
                    return v_s_3001_;
                }
            }
            1 => {
                leanh::lean_inc(v_a_3002_);
                v___x_3009_ = lean_array_push(v_elems_3003_, v_a_3002_);
                v___x_3010_ = leanh::lean_box(0);
                v___x_3011_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Try_Collector_OrdSet_insert___at___00Lean_Meta_Try_Collector_saveConst_spec__0_spec__1___redArg(v_set_3004_, v_a_3002_, v___x_3010_);
                if v_isShared_3008_ == 0 {
                    leanh::lean_ctor_set(v___x_3007_, 1, v___x_3011_);
                    leanh::lean_ctor_set(v___x_3007_, 0, v___x_3009_);
                    v___x_3013_ = v___x_3007_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3014_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3014_, 0, v___x_3009_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3014_, 1, v___x_3011_);
                    v___x_3013_ = v_reuseFailAlloc_3014_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3013_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Try_Collector_saveConst___redArg(
    mut v_declName_3018_: *mut leanh::LeanObject,
    mut v_a_3019_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3021_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_allConsts_3022_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unfoldCandidates_3023_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_eqnCandidates_3024_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_funIndCandidates_3025_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_indCandidates_3026_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_libSearchResults_3027_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3029_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3030_: u8 = 0;
    let mut v___x_3031_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3033_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3034_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3035_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3036_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3037_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3038_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3021_ = lean_st_ref_take(v_a_3019_);
                v_allConsts_3022_ = leanh::lean_ctor_get(v___x_3021_, 0);
                v_unfoldCandidates_3023_ = leanh::lean_ctor_get(v___x_3021_, 1);
                v_eqnCandidates_3024_ = leanh::lean_ctor_get(v___x_3021_, 2);
                v_funIndCandidates_3025_ = leanh::lean_ctor_get(v___x_3021_, 3);
                v_indCandidates_3026_ = leanh::lean_ctor_get(v___x_3021_, 4);
                v_libSearchResults_3027_ = leanh::lean_ctor_get(v___x_3021_, 5);
                v_isSharedCheck_3038_ = (!leanh::lean_is_exclusive(v___x_3021_)) as u8;
                if v_isSharedCheck_3038_ == 0 {
                    v___x_3029_ = v___x_3021_;
                    v_isShared_3030_ = v_isSharedCheck_3038_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_libSearchResults_3027_);
                    leanh::lean_inc(v_indCandidates_3026_);
                    leanh::lean_inc(v_funIndCandidates_3025_);
                    leanh::lean_inc(v_eqnCandidates_3024_);
                    leanh::lean_inc(v_unfoldCandidates_3023_);
                    leanh::lean_inc(v_allConsts_3022_);
                    leanh::lean_dec(v___x_3021_);
                    v___x_3029_ = leanh::lean_box(0);
                    v_isShared_3030_ = v_isSharedCheck_3038_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_3031_ = l_Lean_Meta_Try_Collector_OrdSet_insert___at___00Lean_Meta_Try_Collector_saveConst_spec__0(v_allConsts_3022_, v_declName_3018_);
                if v_isShared_3030_ == 0 {
                    leanh::lean_ctor_set(v___x_3029_, 0, v___x_3031_);
                    v___x_3033_ = v___x_3029_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3037_ = leanh::lean_alloc_ctor(0, 6, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3037_, 0, v___x_3031_);
                    leanh::lean_ctor_set(
                        v_reuseFailAlloc_3037_,
                        1,
                        v_unfoldCandidates_3023_,
                    );
                    leanh::lean_ctor_set(v_reuseFailAlloc_3037_, 2, v_eqnCandidates_3024_);
                    leanh::lean_ctor_set(
                        v_reuseFailAlloc_3037_,
                        3,
                        v_funIndCandidates_3025_,
                    );
                    leanh::lean_ctor_set(v_reuseFailAlloc_3037_, 4, v_indCandidates_3026_);
                    leanh::lean_ctor_set(
                        v_reuseFailAlloc_3037_,
                        5,
                        v_libSearchResults_3027_,
                    );
                    v___x_3033_ = v_reuseFailAlloc_3037_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_3034_ = lean_st_ref_set(v_a_3019_, v___x_3033_);
                v___x_3035_ = leanh::lean_box(0);
                v___x_3036_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_3036_, 0, v___x_3035_);
                return v___x_3036_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Try_Collector_saveConst___redArg___boxed(
    mut v_declName_3039_: *mut leanh::LeanObject,
    mut v_a_3040_: *mut leanh::LeanObject,
    mut v_a_3041_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3042_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3042_ = l_Lean_Meta_Try_Collector_saveConst___redArg(v_declName_3039_, v_a_3040_);
    leanh::lean_dec(v_a_3040_);
    return v_res_3042_;
}
pub unsafe fn l_Lean_Meta_Try_Collector_saveConst(
    mut v_declName_3043_: *mut leanh::LeanObject,
    mut v_a_3044_: *mut leanh::LeanObject,
    mut v_a_3045_: *mut leanh::LeanObject,
    mut v_a_3046_: *mut leanh::LeanObject,
    mut v_a_3047_: *mut leanh::LeanObject,
    mut v_a_3048_: *mut leanh::LeanObject,
    mut v_a_3049_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3051_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3051_ = l_Lean_Meta_Try_Collector_saveConst___redArg(v_declName_3043_, v_a_3045_);
    return v___x_3051_;
}
pub unsafe fn l_Lean_Meta_Try_Collector_saveConst___boxed(
    mut v_declName_3052_: *mut leanh::LeanObject,
    mut v_a_3053_: *mut leanh::LeanObject,
    mut v_a_3054_: *mut leanh::LeanObject,
    mut v_a_3055_: *mut leanh::LeanObject,
    mut v_a_3056_: *mut leanh::LeanObject,
    mut v_a_3057_: *mut leanh::LeanObject,
    mut v_a_3058_: *mut leanh::LeanObject,
    mut v_a_3059_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3060_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3060_ = l_Lean_Meta_Try_Collector_saveConst(
        v_declName_3052_,
        v_a_3053_,
        v_a_3054_,
        v_a_3055_,
        v_a_3056_,
        v_a_3057_,
        v_a_3058_,
    );
    leanh::lean_dec(v_a_3058_);
    leanh::lean_dec_ref(v_a_3057_);
    leanh::lean_dec(v_a_3056_);
    leanh::lean_dec_ref(v_a_3055_);
    leanh::lean_dec(v_a_3054_);
    leanh::lean_dec_ref(v_a_3053_);
    return v_res_3060_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Try_Collector_OrdSet_insert___at___00Lean_Meta_Try_Collector_saveConst_spec__0_spec__0(
    mut v_00_u03b2_3061_: *mut leanh::LeanObject,
    mut v_m_3062_: *mut leanh::LeanObject,
    mut v_a_3063_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_3064_: u8 = 0;
    v___x_3064_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Try_Collector_OrdSet_insert___at___00Lean_Meta_Try_Collector_saveConst_spec__0_spec__0___redArg(v_m_3062_, v_a_3063_);
    return v___x_3064_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Try_Collector_OrdSet_insert___at___00Lean_Meta_Try_Collector_saveConst_spec__0_spec__0___boxed(
    mut v_00_u03b2_3065_: *mut leanh::LeanObject,
    mut v_m_3066_: *mut leanh::LeanObject,
    mut v_a_3067_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3068_: u8 = 0;
    let mut v_r_3069_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3068_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Try_Collector_OrdSet_insert___at___00Lean_Meta_Try_Collector_saveConst_spec__0_spec__0(v_00_u03b2_3065_, v_m_3066_, v_a_3067_);
    leanh::lean_dec(v_a_3067_);
    leanh::lean_dec_ref(v_m_3066_);
    v_r_3069_ = leanh::lean_box((v_res_3068_) as usize);
    return v_r_3069_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Try_Collector_OrdSet_insert___at___00Lean_Meta_Try_Collector_saveConst_spec__0_spec__1(
    mut v_00_u03b2_3070_: *mut leanh::LeanObject,
    mut v_m_3071_: *mut leanh::LeanObject,
    mut v_a_3072_: *mut leanh::LeanObject,
    mut v_b_3073_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3074_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3074_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Try_Collector_OrdSet_insert___at___00Lean_Meta_Try_Collector_saveConst_spec__0_spec__1___redArg(v_m_3071_, v_a_3072_, v_b_3073_);
    return v___x_3074_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Try_Collector_OrdSet_insert___at___00Lean_Meta_Try_Collector_saveConst_spec__0_spec__0_spec__1(
    mut v_00_u03b2_3075_: *mut leanh::LeanObject,
    mut v_a_3076_: *mut leanh::LeanObject,
    mut v_x_3077_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_3078_: u8 = 0;
    v___x_3078_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Try_Collector_OrdSet_insert___at___00Lean_Meta_Try_Collector_saveConst_spec__0_spec__0_spec__1___redArg(v_a_3076_, v_x_3077_);
    return v___x_3078_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Try_Collector_OrdSet_insert___at___00Lean_Meta_Try_Collector_saveConst_spec__0_spec__0_spec__1___boxed(
    mut v_00_u03b2_3079_: *mut leanh::LeanObject,
    mut v_a_3080_: *mut leanh::LeanObject,
    mut v_x_3081_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3082_: u8 = 0;
    let mut v_r_3083_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3082_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Try_Collector_OrdSet_insert___at___00Lean_Meta_Try_Collector_saveConst_spec__0_spec__0_spec__1(v_00_u03b2_3079_, v_a_3080_, v_x_3081_);
    leanh::lean_dec(v_x_3081_);
    leanh::lean_dec(v_a_3080_);
    v_r_3083_ = leanh::lean_box((v_res_3082_) as usize);
    return v_r_3083_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Try_Collector_OrdSet_insert___at___00Lean_Meta_Try_Collector_saveConst_spec__0_spec__1_spec__3(
    mut v_00_u03b2_3084_: *mut leanh::LeanObject,
    mut v_data_3085_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3086_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3086_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Try_Collector_OrdSet_insert___at___00Lean_Meta_Try_Collector_saveConst_spec__0_spec__1_spec__3___redArg(v_data_3085_);
    return v___x_3086_;
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Try_Collector_OrdSet_insert___at___00Lean_Meta_Try_Collector_saveConst_spec__0_spec__1_spec__3_spec__4(
    mut v_00_u03b2_3087_: *mut leanh::LeanObject,
    mut v_i_3088_: *mut leanh::LeanObject,
    mut v_source_3089_: *mut leanh::LeanObject,
    mut v_target_3090_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3091_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3091_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Try_Collector_OrdSet_insert___at___00Lean_Meta_Try_Collector_saveConst_spec__0_spec__1_spec__3_spec__4___redArg(v_i_3088_, v_source_3089_, v_target_3090_);
    return v___x_3091_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Try_Collector_OrdSet_insert___at___00Lean_Meta_Try_Collector_saveConst_spec__0_spec__1_spec__3_spec__4_spec__5(
    mut v_00_u03b2_3092_: *mut leanh::LeanObject,
    mut v_x_3093_: *mut leanh::LeanObject,
    mut v_x_3094_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3095_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3095_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Try_Collector_OrdSet_insert___at___00Lean_Meta_Try_Collector_saveConst_spec__0_spec__1_spec__3_spec__4_spec__5___redArg(v_x_3093_, v_x_3094_);
    return v___x_3095_;
}
pub unsafe fn l_Lean_Meta_Try_Collector_inCurrentModule___redArg(
    mut v_declName_3096_: *mut leanh::LeanObject,
    mut v_a_3097_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3099_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_3100_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3101_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3102_: u8 = 0;
    let mut v___x_3103_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3104_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3106_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3107_: u8 = 0;
    let mut v___x_3108_: u8 = 0;
    let mut v___x_3109_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3111_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3112_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3113_: u8 = 0;
    let mut v_unused_3114_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3099_ = lean_st_ref_get(v_a_3097_);
                v_env_3100_ = leanh::lean_ctor_get(v___x_3099_, 0);
                leanh::lean_inc_ref(v_env_3100_);
                leanh::lean_dec(v___x_3099_);
                v___x_3101_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_3100_, v_declName_3096_);
                leanh::lean_dec_ref(v_env_3100_);
                if leanh::lean_obj_tag(v___x_3101_) == 0 {
                    v___x_3102_ = 1;
                    v___x_3103_ = leanh::lean_box((v___x_3102_) as usize);
                    v___x_3104_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_3104_, 0, v___x_3103_);
                    return v___x_3104_;
                } else {
                    v_isSharedCheck_3113_ = (!leanh::lean_is_exclusive(v___x_3101_)) as u8;
                    if v_isSharedCheck_3113_ == 0 {
                        v_unused_3114_ = leanh::lean_ctor_get(v___x_3101_, 0);
                        leanh::lean_dec(v_unused_3114_);
                        v___x_3106_ = v___x_3101_;
                        v_isShared_3107_ = v_isSharedCheck_3113_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_dec(v___x_3101_);
                        v___x_3106_ = leanh::lean_box(0);
                        v_isShared_3107_ = v_isSharedCheck_3113_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_3108_ = 0;
                v___x_3109_ = leanh::lean_box((v___x_3108_) as usize);
                if v_isShared_3107_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_3106_, 0);
                    leanh::lean_ctor_set(v___x_3106_, 0, v___x_3109_);
                    v___x_3111_ = v___x_3106_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3112_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3112_, 0, v___x_3109_);
                    v___x_3111_ = v_reuseFailAlloc_3112_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3111_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Try_Collector_inCurrentModule___redArg___boxed(
    mut v_declName_3115_: *mut leanh::LeanObject,
    mut v_a_3116_: *mut leanh::LeanObject,
    mut v_a_3117_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3118_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3118_ = l_Lean_Meta_Try_Collector_inCurrentModule___redArg(v_declName_3115_, v_a_3116_);
    leanh::lean_dec(v_a_3116_);
    leanh::lean_dec(v_declName_3115_);
    return v_res_3118_;
}
pub unsafe fn l_Lean_Meta_Try_Collector_inCurrentModule(
    mut v_declName_3119_: *mut leanh::LeanObject,
    mut v_a_3120_: *mut leanh::LeanObject,
    mut v_a_3121_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3123_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3123_ = l_Lean_Meta_Try_Collector_inCurrentModule___redArg(v_declName_3119_, v_a_3121_);
    return v___x_3123_;
}
pub unsafe fn l_Lean_Meta_Try_Collector_inCurrentModule___boxed(
    mut v_declName_3124_: *mut leanh::LeanObject,
    mut v_a_3125_: *mut leanh::LeanObject,
    mut v_a_3126_: *mut leanh::LeanObject,
    mut v_a_3127_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3128_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3128_ = l_Lean_Meta_Try_Collector_inCurrentModule(v_declName_3124_, v_a_3125_, v_a_3126_);
    leanh::lean_dec(v_a_3126_);
    leanh::lean_dec_ref(v_a_3125_);
    leanh::lean_dec(v_declName_3124_);
    return v_res_3128_;
}
pub unsafe fn l_Lean_Meta_Try_Collector_isEligible___redArg(
    mut v_declName_3129_: *mut leanh::LeanObject,
    mut v_a_3130_: *mut leanh::LeanObject,
    mut v_a_3131_: *mut leanh::LeanObject,
    mut v_a_3132_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3134_: u8 = 0;
    v___x_3134_ = l_Lean_Name_hasMacroScopes(v_declName_3129_);
    if v___x_3134_ == 0 {
        let mut v_main_3135_: u8 = 0;
        v_main_3135_ = leanh::lean_ctor_get_uint8(
            v_a_3130_,
            (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
        );
        if v_main_3135_ == 0 {
            let mut v_name_3136_: u8 = 0;
            v_name_3136_ = leanh::lean_ctor_get_uint8(
                v_a_3130_,
                (core::mem::size_of::<*mut leanh::LeanObject>() * 1 + 1) as u32,
            );
            if v_name_3136_ == 0 {
                let mut v___x_3137_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_3138_: *mut leanh::LeanObject = core::ptr::null_mut();
                v___x_3137_ = leanh::lean_box((v_name_3136_) as usize);
                v___x_3138_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_3138_, 0, v___x_3137_);
                return v___x_3138_;
            } else {
                let mut v_currNamespace_3139_: *mut leanh::LeanObject =
                    core::ptr::null_mut();
                let mut v___x_3140_: u8 = 0;
                let mut v___x_3141_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_3142_: *mut leanh::LeanObject = core::ptr::null_mut();
                v_currNamespace_3139_ = leanh::lean_ctor_get(v_a_3131_, 6);
                v___x_3140_ = l_Lean_Name_isPrefixOf(v_currNamespace_3139_, v_declName_3129_);
                v___x_3141_ = leanh::lean_box((v___x_3140_) as usize);
                v___x_3142_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_3142_, 0, v___x_3141_);
                return v___x_3142_;
            }
        } else {
            let mut v___x_3143_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_3143_ =
                l_Lean_Meta_Try_Collector_inCurrentModule___redArg(v_declName_3129_, v_a_3132_);
            return v___x_3143_;
        }
    } else {
        let mut v___x_3144_: u8 = 0;
        let mut v___x_3145_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3146_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_3144_ = 0;
        v___x_3145_ = leanh::lean_box((v___x_3144_) as usize);
        v___x_3146_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
        leanh::lean_ctor_set(v___x_3146_, 0, v___x_3145_);
        return v___x_3146_;
    }
}
pub unsafe fn l_Lean_Meta_Try_Collector_isEligible___redArg___boxed(
    mut v_declName_3147_: *mut leanh::LeanObject,
    mut v_a_3148_: *mut leanh::LeanObject,
    mut v_a_3149_: *mut leanh::LeanObject,
    mut v_a_3150_: *mut leanh::LeanObject,
    mut v_a_3151_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3152_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3152_ = l_Lean_Meta_Try_Collector_isEligible___redArg(
        v_declName_3147_,
        v_a_3148_,
        v_a_3149_,
        v_a_3150_,
    );
    leanh::lean_dec(v_a_3150_);
    leanh::lean_dec_ref(v_a_3149_);
    leanh::lean_dec_ref(v_a_3148_);
    leanh::lean_dec(v_declName_3147_);
    return v_res_3152_;
}
pub unsafe fn l_Lean_Meta_Try_Collector_isEligible(
    mut v_declName_3153_: *mut leanh::LeanObject,
    mut v_a_3154_: *mut leanh::LeanObject,
    mut v_a_3155_: *mut leanh::LeanObject,
    mut v_a_3156_: *mut leanh::LeanObject,
    mut v_a_3157_: *mut leanh::LeanObject,
    mut v_a_3158_: *mut leanh::LeanObject,
    mut v_a_3159_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3161_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3161_ = l_Lean_Meta_Try_Collector_isEligible___redArg(
        v_declName_3153_,
        v_a_3154_,
        v_a_3158_,
        v_a_3159_,
    );
    return v___x_3161_;
}
pub unsafe fn l_Lean_Meta_Try_Collector_isEligible___boxed(
    mut v_declName_3162_: *mut leanh::LeanObject,
    mut v_a_3163_: *mut leanh::LeanObject,
    mut v_a_3164_: *mut leanh::LeanObject,
    mut v_a_3165_: *mut leanh::LeanObject,
    mut v_a_3166_: *mut leanh::LeanObject,
    mut v_a_3167_: *mut leanh::LeanObject,
    mut v_a_3168_: *mut leanh::LeanObject,
    mut v_a_3169_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3170_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3170_ = l_Lean_Meta_Try_Collector_isEligible(
        v_declName_3162_,
        v_a_3163_,
        v_a_3164_,
        v_a_3165_,
        v_a_3166_,
        v_a_3167_,
        v_a_3168_,
    );
    leanh::lean_dec(v_a_3168_);
    leanh::lean_dec_ref(v_a_3167_);
    leanh::lean_dec(v_a_3166_);
    leanh::lean_dec_ref(v_a_3165_);
    leanh::lean_dec(v_a_3164_);
    leanh::lean_dec_ref(v_a_3163_);
    leanh::lean_dec(v_declName_3162_);
    return v_res_3170_;
}
pub unsafe fn l_Lean_Meta_Try_Collector_saveEqnCandidate(
    mut v_declName_3171_: *mut leanh::LeanObject,
    mut v_a_3172_: *mut leanh::LeanObject,
    mut v_a_3173_: *mut leanh::LeanObject,
    mut v_a_3174_: *mut leanh::LeanObject,
    mut v_a_3175_: *mut leanh::LeanObject,
    mut v_a_3176_: *mut leanh::LeanObject,
    mut v_a_3177_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3179_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3180_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3182_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3183_: u8 = 0;
    let mut v___x_3184_: u8 = 0;
    let mut v___x_3185_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3187_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3188_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3189_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3190_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3192_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3193_: u8 = 0;
    let mut v_val_3194_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3195_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3196_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3197_: u8 = 0;
    let mut v___x_3198_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3199_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3200_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3201_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3202_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3204_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3205_: u8 = 0;
    let mut v___x_3206_: u8 = 0;
    let mut v___x_3207_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_allConsts_3208_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unfoldCandidates_3209_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_eqnCandidates_3210_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_funIndCandidates_3211_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_indCandidates_3212_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_libSearchResults_3213_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3215_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3216_: u8 = 0;
    let mut v___x_3217_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3219_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3220_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3221_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3223_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3224_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3225_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3226_: u8 = 0;
    let mut v___x_3227_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3229_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3230_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3231_: u8 = 0;
    let mut v_a_3232_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3234_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3235_: u8 = 0;
    let mut v___x_3237_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3238_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3239_: u8 = 0;
    let mut v___x_3240_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3242_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3243_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3244_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3246_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3247_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3248_: u8 = 0;
    let mut v_a_3249_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3251_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3252_: u8 = 0;
    let mut v___x_3254_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3255_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3256_: u8 = 0;
    let mut v_isSharedCheck_3257_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3179_ = l_Lean_Meta_Try_Collector_isEligible___redArg(
                    v_declName_3171_,
                    v_a_3172_,
                    v_a_3176_,
                    v_a_3177_,
                );
                v_a_3180_ = leanh::lean_ctor_get(v___x_3179_, 0);
                v_isSharedCheck_3257_ = (!leanh::lean_is_exclusive(v___x_3179_)) as u8;
                if v_isSharedCheck_3257_ == 0 {
                    v___x_3182_ = v___x_3179_;
                    v_isShared_3183_ = v_isSharedCheck_3257_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_a_3180_);
                    leanh::lean_dec(v___x_3179_);
                    v___x_3182_ = leanh::lean_box(0);
                    v_isShared_3183_ = v_isSharedCheck_3257_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_3184_ = (leanh::lean_unbox(v_a_3180_) as u8);
                leanh::lean_dec(v_a_3180_);
                if v___x_3184_ == 0 {
                    leanh::lean_dec(v_declName_3171_);
                    v___x_3185_ = leanh::lean_box(0);
                    if v_isShared_3183_ == 0 {
                        leanh::lean_ctor_set(v___x_3182_, 0, v___x_3185_);
                        v___x_3187_ = v___x_3182_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_3188_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_3188_, 0, v___x_3185_);
                        v___x_3187_ = v_reuseFailAlloc_3188_;
                        state = 2;
                        continue;
                    }
                } else {
                    leanh::lean_del_object(v___x_3182_);
                    leanh::lean_inc(v_declName_3171_);
                    v___x_3189_ = l_Lean_Meta_getEqnsFor_x3f(
                        v_declName_3171_,
                        v_a_3174_,
                        v_a_3175_,
                        v_a_3176_,
                        v_a_3177_,
                    );
                    if leanh::lean_obj_tag(v___x_3189_) == 0 {
                        v_a_3190_ = leanh::lean_ctor_get(v___x_3189_, 0);
                        v_isSharedCheck_3248_ =
                            (!leanh::lean_is_exclusive(v___x_3189_)) as u8;
                        if v_isSharedCheck_3248_ == 0 {
                            v___x_3192_ = v___x_3189_;
                            v_isShared_3193_ = v_isSharedCheck_3248_;
                            state = 3;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_3190_);
                            leanh::lean_dec(v___x_3189_);
                            v___x_3192_ = leanh::lean_box(0);
                            v_isShared_3193_ = v_isSharedCheck_3248_;
                            state = 3;
                            continue;
                        }
                    } else {
                        leanh::lean_dec(v_declName_3171_);
                        v_a_3249_ = leanh::lean_ctor_get(v___x_3189_, 0);
                        v_isSharedCheck_3256_ =
                            (!leanh::lean_is_exclusive(v___x_3189_)) as u8;
                        if v_isSharedCheck_3256_ == 0 {
                            v___x_3251_ = v___x_3189_;
                            v_isShared_3252_ = v_isSharedCheck_3256_;
                            state = 13;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_3249_);
                            leanh::lean_dec(v___x_3189_);
                            v___x_3251_ = leanh::lean_box(0);
                            v_isShared_3252_ = v_isSharedCheck_3256_;
                            state = 13;
                            continue;
                        }
                    }
                }
            }
            2 => {
                return v___x_3187_;
            }
            3 => {
                if leanh::lean_obj_tag(v_a_3190_) == 1 {
                    v_val_3194_ = leanh::lean_ctor_get(v_a_3190_, 0);
                    leanh::lean_inc(v_val_3194_);
                    leanh::lean_dec_ref_known(v_a_3190_, 1);
                    v___x_3195_ = lean_array_get_size(v_val_3194_);
                    v___x_3196_ = leanh::lean_unsigned_to_nat(0);
                    v___x_3197_ = lean_nat_dec_eq(v___x_3195_, v___x_3196_);
                    if v___x_3197_ == 0 {
                        leanh::lean_del_object(v___x_3192_);
                        v___x_3198_ = l_Lean_Meta_Grind_grindExt;
                        v___x_3199_ = leanh::lean_box(0);
                        v___x_3200_ = lean_array_get(v___x_3199_, v_val_3194_, v___x_3196_);
                        leanh::lean_dec(v_val_3194_);
                        v___x_3201_ = l_Lean_Meta_Grind_Extension_isEMatchTheorem___redArg(
                            v___x_3198_,
                            v___x_3200_,
                            v_a_3177_,
                        );
                        if leanh::lean_obj_tag(v___x_3201_) == 0 {
                            v_a_3202_ = leanh::lean_ctor_get(v___x_3201_, 0);
                            v_isSharedCheck_3231_ =
                                (!leanh::lean_is_exclusive(v___x_3201_)) as u8;
                            if v_isSharedCheck_3231_ == 0 {
                                v___x_3204_ = v___x_3201_;
                                v_isShared_3205_ = v_isSharedCheck_3231_;
                                state = 4;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_3202_);
                                leanh::lean_dec(v___x_3201_);
                                v___x_3204_ = leanh::lean_box(0);
                                v_isShared_3205_ = v_isSharedCheck_3231_;
                                state = 4;
                                continue;
                            }
                        } else {
                            leanh::lean_dec(v_declName_3171_);
                            v_a_3232_ = leanh::lean_ctor_get(v___x_3201_, 0);
                            v_isSharedCheck_3239_ =
                                (!leanh::lean_is_exclusive(v___x_3201_)) as u8;
                            if v_isSharedCheck_3239_ == 0 {
                                v___x_3234_ = v___x_3201_;
                                v_isShared_3235_ = v_isSharedCheck_3239_;
                                state = 9;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_3232_);
                                leanh::lean_dec(v___x_3201_);
                                v___x_3234_ = leanh::lean_box(0);
                                v_isShared_3235_ = v_isSharedCheck_3239_;
                                state = 9;
                                continue;
                            }
                        }
                    } else {
                        leanh::lean_dec(v_val_3194_);
                        leanh::lean_dec(v_declName_3171_);
                        v___x_3240_ = leanh::lean_box(0);
                        if v_isShared_3193_ == 0 {
                            leanh::lean_ctor_set(v___x_3192_, 0, v___x_3240_);
                            v___x_3242_ = v___x_3192_;
                            state = 11;
                            continue;
                        } else {
                            v_reuseFailAlloc_3243_ =
                                leanh::lean_alloc_ctor(0, 1, (0) as u32);
                            leanh::lean_ctor_set(v_reuseFailAlloc_3243_, 0, v___x_3240_);
                            v___x_3242_ = v_reuseFailAlloc_3243_;
                            state = 11;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_dec(v_a_3190_);
                    leanh::lean_dec(v_declName_3171_);
                    v___x_3244_ = leanh::lean_box(0);
                    if v_isShared_3193_ == 0 {
                        leanh::lean_ctor_set(v___x_3192_, 0, v___x_3244_);
                        v___x_3246_ = v___x_3192_;
                        state = 12;
                        continue;
                    } else {
                        v_reuseFailAlloc_3247_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_3247_, 0, v___x_3244_);
                        v___x_3246_ = v_reuseFailAlloc_3247_;
                        state = 12;
                        continue;
                    }
                }
            }
            4 => {
                v___x_3206_ = (leanh::lean_unbox(v_a_3202_) as u8);
                leanh::lean_dec(v_a_3202_);
                if v___x_3206_ == 0 {
                    v___x_3207_ = lean_st_ref_take(v_a_3173_);
                    v_allConsts_3208_ = leanh::lean_ctor_get(v___x_3207_, 0);
                    v_unfoldCandidates_3209_ = leanh::lean_ctor_get(v___x_3207_, 1);
                    v_eqnCandidates_3210_ = leanh::lean_ctor_get(v___x_3207_, 2);
                    v_funIndCandidates_3211_ = leanh::lean_ctor_get(v___x_3207_, 3);
                    v_indCandidates_3212_ = leanh::lean_ctor_get(v___x_3207_, 4);
                    v_libSearchResults_3213_ = leanh::lean_ctor_get(v___x_3207_, 5);
                    v_isSharedCheck_3226_ = (!leanh::lean_is_exclusive(v___x_3207_)) as u8;
                    if v_isSharedCheck_3226_ == 0 {
                        v___x_3215_ = v___x_3207_;
                        v_isShared_3216_ = v_isSharedCheck_3226_;
                        state = 5;
                        continue;
                    } else {
                        leanh::lean_inc(v_libSearchResults_3213_);
                        leanh::lean_inc(v_indCandidates_3212_);
                        leanh::lean_inc(v_funIndCandidates_3211_);
                        leanh::lean_inc(v_eqnCandidates_3210_);
                        leanh::lean_inc(v_unfoldCandidates_3209_);
                        leanh::lean_inc(v_allConsts_3208_);
                        leanh::lean_dec(v___x_3207_);
                        v___x_3215_ = leanh::lean_box(0);
                        v_isShared_3216_ = v_isSharedCheck_3226_;
                        state = 5;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v_declName_3171_);
                    v___x_3227_ = leanh::lean_box(0);
                    if v_isShared_3205_ == 0 {
                        leanh::lean_ctor_set(v___x_3204_, 0, v___x_3227_);
                        v___x_3229_ = v___x_3204_;
                        state = 8;
                        continue;
                    } else {
                        v_reuseFailAlloc_3230_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_3230_, 0, v___x_3227_);
                        v___x_3229_ = v_reuseFailAlloc_3230_;
                        state = 8;
                        continue;
                    }
                }
            }
            5 => {
                v___x_3217_ = l_Lean_Meta_Try_Collector_OrdSet_insert___at___00Lean_Meta_Try_Collector_saveConst_spec__0(v_eqnCandidates_3210_, v_declName_3171_);
                if v_isShared_3216_ == 0 {
                    leanh::lean_ctor_set(v___x_3215_, 2, v___x_3217_);
                    v___x_3219_ = v___x_3215_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_3225_ = leanh::lean_alloc_ctor(0, 6, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3225_, 0, v_allConsts_3208_);
                    leanh::lean_ctor_set(
                        v_reuseFailAlloc_3225_,
                        1,
                        v_unfoldCandidates_3209_,
                    );
                    leanh::lean_ctor_set(v_reuseFailAlloc_3225_, 2, v___x_3217_);
                    leanh::lean_ctor_set(
                        v_reuseFailAlloc_3225_,
                        3,
                        v_funIndCandidates_3211_,
                    );
                    leanh::lean_ctor_set(v_reuseFailAlloc_3225_, 4, v_indCandidates_3212_);
                    leanh::lean_ctor_set(
                        v_reuseFailAlloc_3225_,
                        5,
                        v_libSearchResults_3213_,
                    );
                    v___x_3219_ = v_reuseFailAlloc_3225_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                v___x_3220_ = lean_st_ref_set(v_a_3173_, v___x_3219_);
                v___x_3221_ = leanh::lean_box(0);
                if v_isShared_3205_ == 0 {
                    leanh::lean_ctor_set(v___x_3204_, 0, v___x_3221_);
                    v___x_3223_ = v___x_3204_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_3224_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3224_, 0, v___x_3221_);
                    v___x_3223_ = v_reuseFailAlloc_3224_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_3223_;
            }
            8 => {
                return v___x_3229_;
            }
            9 => {
                if v_isShared_3235_ == 0 {
                    v___x_3237_ = v___x_3234_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_3238_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3238_, 0, v_a_3232_);
                    v___x_3237_ = v_reuseFailAlloc_3238_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_3237_;
            }
            11 => {
                return v___x_3242_;
            }
            12 => {
                return v___x_3246_;
            }
            13 => {
                if v_isShared_3252_ == 0 {
                    v___x_3254_ = v___x_3251_;
                    state = 14;
                    continue;
                } else {
                    v_reuseFailAlloc_3255_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3255_, 0, v_a_3249_);
                    v___x_3254_ = v_reuseFailAlloc_3255_;
                    state = 14;
                    continue;
                }
            }
            14 => {
                return v___x_3254_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Try_Collector_saveEqnCandidate___boxed(
    mut v_declName_3258_: *mut leanh::LeanObject,
    mut v_a_3259_: *mut leanh::LeanObject,
    mut v_a_3260_: *mut leanh::LeanObject,
    mut v_a_3261_: *mut leanh::LeanObject,
    mut v_a_3262_: *mut leanh::LeanObject,
    mut v_a_3263_: *mut leanh::LeanObject,
    mut v_a_3264_: *mut leanh::LeanObject,
    mut v_a_3265_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3266_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3266_ = l_Lean_Meta_Try_Collector_saveEqnCandidate(
        v_declName_3258_,
        v_a_3259_,
        v_a_3260_,
        v_a_3261_,
        v_a_3262_,
        v_a_3263_,
        v_a_3264_,
    );
    leanh::lean_dec(v_a_3264_);
    leanh::lean_dec_ref(v_a_3263_);
    leanh::lean_dec(v_a_3262_);
    leanh::lean_dec_ref(v_a_3261_);
    leanh::lean_dec(v_a_3260_);
    leanh::lean_dec_ref(v_a_3259_);
    return v_res_3266_;
}
pub unsafe fn l_Lean_Meta_Try_Collector_getEqDefDecl_x3f___redArg(
    mut v_declName_3270_: *mut leanh::LeanObject,
    mut v_a_3271_: *mut leanh::LeanObject,
    mut v_a_3272_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3274_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_declName_3275_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3276_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3277_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3278_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3280_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3281_: u8 = 0;
    let mut v___x_3282_: u8 = 0;
    let mut v___x_3283_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3284_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3286_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3287_: u8 = 0;
    let mut v___x_3288_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3290_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3291_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3292_: u8 = 0;
    let mut v_a_3293_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3295_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3296_: u8 = 0;
    let mut v___y_3298_: u8 = 0;
    let mut v___x_3299_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3301_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3302_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3304_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3305_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3306_: u8 = 0;
    let mut v___x_3307_: u8 = 0;
    let mut v_isSharedCheck_3308_: u8 = 0;
    let mut v___x_3309_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3311_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3312_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3313_: u8 = 0;
    let mut v_a_3314_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3316_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3317_: u8 = 0;
    let mut v___x_3319_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3320_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3321_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3274_ = l_Lean_Meta_Try_Collector_getEqDefDecl_x3f___redArg___closed__1;
                v_declName_3275_ = l_Lean_Name_append(v_declName_3270_, v___x_3274_);
                v___x_3276_ = l_Lean_Meta_Grind_grindExt;
                leanh::lean_inc(v_declName_3275_);
                v___x_3277_ = l_Lean_Meta_Grind_Extension_isEMatchTheorem___redArg(
                    v___x_3276_,
                    v_declName_3275_,
                    v_a_3272_,
                );
                if leanh::lean_obj_tag(v___x_3277_) == 0 {
                    v_a_3278_ = leanh::lean_ctor_get(v___x_3277_, 0);
                    v_isSharedCheck_3313_ = (!leanh::lean_is_exclusive(v___x_3277_)) as u8;
                    if v_isSharedCheck_3313_ == 0 {
                        v___x_3280_ = v___x_3277_;
                        v_isShared_3281_ = v_isSharedCheck_3313_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_3278_);
                        leanh::lean_dec(v___x_3277_);
                        v___x_3280_ = leanh::lean_box(0);
                        v_isShared_3281_ = v_isSharedCheck_3313_;
                        state = 1;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v_declName_3275_);
                    v_a_3314_ = leanh::lean_ctor_get(v___x_3277_, 0);
                    v_isSharedCheck_3321_ = (!leanh::lean_is_exclusive(v___x_3277_)) as u8;
                    if v_isSharedCheck_3321_ == 0 {
                        v___x_3316_ = v___x_3277_;
                        v_isShared_3317_ = v_isSharedCheck_3321_;
                        state = 9;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_3314_);
                        leanh::lean_dec(v___x_3277_);
                        v___x_3316_ = leanh::lean_box(0);
                        v_isShared_3317_ = v_isSharedCheck_3321_;
                        state = 9;
                        continue;
                    }
                }
            }
            1 => {
                v___x_3282_ = (leanh::lean_unbox(v_a_3278_) as u8);
                leanh::lean_dec(v_a_3278_);
                if v___x_3282_ == 0 {
                    leanh::lean_del_object(v___x_3280_);
                    v___x_3283_ = l_Lean_realizeGlobalConstNoOverloadCore(
                        v_declName_3275_,
                        v_a_3271_,
                        v_a_3272_,
                    );
                    if leanh::lean_obj_tag(v___x_3283_) == 0 {
                        v_a_3284_ = leanh::lean_ctor_get(v___x_3283_, 0);
                        v_isSharedCheck_3292_ =
                            (!leanh::lean_is_exclusive(v___x_3283_)) as u8;
                        if v_isSharedCheck_3292_ == 0 {
                            v___x_3286_ = v___x_3283_;
                            v_isShared_3287_ = v_isSharedCheck_3292_;
                            state = 2;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_3284_);
                            leanh::lean_dec(v___x_3283_);
                            v___x_3286_ = leanh::lean_box(0);
                            v_isShared_3287_ = v_isSharedCheck_3292_;
                            state = 2;
                            continue;
                        }
                    } else {
                        v_a_3293_ = leanh::lean_ctor_get(v___x_3283_, 0);
                        v_isSharedCheck_3308_ =
                            (!leanh::lean_is_exclusive(v___x_3283_)) as u8;
                        if v_isSharedCheck_3308_ == 0 {
                            v___x_3295_ = v___x_3283_;
                            v_isShared_3296_ = v_isSharedCheck_3308_;
                            state = 4;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_3293_);
                            leanh::lean_dec(v___x_3283_);
                            v___x_3295_ = leanh::lean_box(0);
                            v_isShared_3296_ = v_isSharedCheck_3308_;
                            state = 4;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_dec(v_declName_3275_);
                    v___x_3309_ = leanh::lean_box(0);
                    if v_isShared_3281_ == 0 {
                        leanh::lean_ctor_set(v___x_3280_, 0, v___x_3309_);
                        v___x_3311_ = v___x_3280_;
                        state = 8;
                        continue;
                    } else {
                        v_reuseFailAlloc_3312_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_3312_, 0, v___x_3309_);
                        v___x_3311_ = v_reuseFailAlloc_3312_;
                        state = 8;
                        continue;
                    }
                }
            }
            2 => {
                v___x_3288_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_3288_, 0, v_a_3284_);
                if v_isShared_3287_ == 0 {
                    leanh::lean_ctor_set(v___x_3286_, 0, v___x_3288_);
                    v___x_3290_ = v___x_3286_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_3291_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3291_, 0, v___x_3288_);
                    v___x_3290_ = v_reuseFailAlloc_3291_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_3290_;
            }
            4 => {
                v___x_3306_ = l_Lean_Exception_isInterrupt(v_a_3293_);
                if v___x_3306_ == 0 {
                    leanh::lean_inc(v_a_3293_);
                    v___x_3307_ = l_Lean_Exception_isRuntime(v_a_3293_);
                    v___y_3298_ = v___x_3307_;
                    state = 5;
                    continue;
                } else {
                    v___y_3298_ = v___x_3306_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                if v___y_3298_ == 0 {
                    leanh::lean_dec(v_a_3293_);
                    v___x_3299_ = leanh::lean_box(0);
                    if v_isShared_3296_ == 0 {
                        leanh::lean_ctor_set_tag(v___x_3295_, 0);
                        leanh::lean_ctor_set(v___x_3295_, 0, v___x_3299_);
                        v___x_3301_ = v___x_3295_;
                        state = 6;
                        continue;
                    } else {
                        v_reuseFailAlloc_3302_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_3302_, 0, v___x_3299_);
                        v___x_3301_ = v_reuseFailAlloc_3302_;
                        state = 6;
                        continue;
                    }
                } else {
                    if v_isShared_3296_ == 0 {
                        v___x_3304_ = v___x_3295_;
                        state = 7;
                        continue;
                    } else {
                        v_reuseFailAlloc_3305_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_3305_, 0, v_a_3293_);
                        v___x_3304_ = v_reuseFailAlloc_3305_;
                        state = 7;
                        continue;
                    }
                }
            }
            6 => {
                return v___x_3301_;
            }
            7 => {
                return v___x_3304_;
            }
            8 => {
                return v___x_3311_;
            }
            9 => {
                if v_isShared_3317_ == 0 {
                    v___x_3319_ = v___x_3316_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_3320_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3320_, 0, v_a_3314_);
                    v___x_3319_ = v_reuseFailAlloc_3320_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_3319_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Try_Collector_getEqDefDecl_x3f___redArg___boxed(
    mut v_declName_3322_: *mut leanh::LeanObject,
    mut v_a_3323_: *mut leanh::LeanObject,
    mut v_a_3324_: *mut leanh::LeanObject,
    mut v_a_3325_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3326_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3326_ =
        l_Lean_Meta_Try_Collector_getEqDefDecl_x3f___redArg(v_declName_3322_, v_a_3323_, v_a_3324_);
    leanh::lean_dec(v_a_3324_);
    leanh::lean_dec_ref(v_a_3323_);
    return v_res_3326_;
}
pub unsafe fn l_Lean_Meta_Try_Collector_getEqDefDecl_x3f(
    mut v_declName_3327_: *mut leanh::LeanObject,
    mut v_a_3328_: *mut leanh::LeanObject,
    mut v_a_3329_: *mut leanh::LeanObject,
    mut v_a_3330_: *mut leanh::LeanObject,
    mut v_a_3331_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3333_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3333_ =
        l_Lean_Meta_Try_Collector_getEqDefDecl_x3f___redArg(v_declName_3327_, v_a_3330_, v_a_3331_);
    return v___x_3333_;
}
pub unsafe fn l_Lean_Meta_Try_Collector_getEqDefDecl_x3f___boxed(
    mut v_declName_3334_: *mut leanh::LeanObject,
    mut v_a_3335_: *mut leanh::LeanObject,
    mut v_a_3336_: *mut leanh::LeanObject,
    mut v_a_3337_: *mut leanh::LeanObject,
    mut v_a_3338_: *mut leanh::LeanObject,
    mut v_a_3339_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3340_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3340_ = l_Lean_Meta_Try_Collector_getEqDefDecl_x3f(
        v_declName_3334_,
        v_a_3335_,
        v_a_3336_,
        v_a_3337_,
        v_a_3338_,
    );
    leanh::lean_dec(v_a_3338_);
    leanh::lean_dec_ref(v_a_3337_);
    leanh::lean_dec(v_a_3336_);
    leanh::lean_dec_ref(v_a_3335_);
    return v_res_3340_;
}
pub unsafe fn l_Lean_Meta_Try_Collector_saveUnfoldCandidate___redArg(
    mut v_declName_3341_: *mut leanh::LeanObject,
    mut v_a_3342_: *mut leanh::LeanObject,
    mut v_a_3343_: *mut leanh::LeanObject,
    mut v_a_3344_: *mut leanh::LeanObject,
    mut v_a_3345_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3347_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3348_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3350_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3351_: u8 = 0;
    let mut v___x_3352_: u8 = 0;
    let mut v___x_3353_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3355_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3356_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3357_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3358_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3360_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3361_: u8 = 0;
    let mut v_val_3362_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3363_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_allConsts_3364_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unfoldCandidates_3365_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_eqnCandidates_3366_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_funIndCandidates_3367_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_indCandidates_3368_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_libSearchResults_3369_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3371_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3372_: u8 = 0;
    let mut v___x_3373_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3375_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3376_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3377_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3379_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3380_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3381_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3382_: u8 = 0;
    let mut v___x_3383_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3385_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3386_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3387_: u8 = 0;
    let mut v_a_3388_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3390_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3391_: u8 = 0;
    let mut v___x_3393_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3394_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3395_: u8 = 0;
    let mut v_isSharedCheck_3396_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3347_ = l_Lean_Meta_Try_Collector_isEligible___redArg(
                    v_declName_3341_,
                    v_a_3342_,
                    v_a_3344_,
                    v_a_3345_,
                );
                v_a_3348_ = leanh::lean_ctor_get(v___x_3347_, 0);
                v_isSharedCheck_3396_ = (!leanh::lean_is_exclusive(v___x_3347_)) as u8;
                if v_isSharedCheck_3396_ == 0 {
                    v___x_3350_ = v___x_3347_;
                    v_isShared_3351_ = v_isSharedCheck_3396_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_a_3348_);
                    leanh::lean_dec(v___x_3347_);
                    v___x_3350_ = leanh::lean_box(0);
                    v_isShared_3351_ = v_isSharedCheck_3396_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_3352_ = (leanh::lean_unbox(v_a_3348_) as u8);
                leanh::lean_dec(v_a_3348_);
                if v___x_3352_ == 0 {
                    leanh::lean_dec(v_declName_3341_);
                    v___x_3353_ = leanh::lean_box(0);
                    if v_isShared_3351_ == 0 {
                        leanh::lean_ctor_set(v___x_3350_, 0, v___x_3353_);
                        v___x_3355_ = v___x_3350_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_3356_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_3356_, 0, v___x_3353_);
                        v___x_3355_ = v_reuseFailAlloc_3356_;
                        state = 2;
                        continue;
                    }
                } else {
                    leanh::lean_del_object(v___x_3350_);
                    v___x_3357_ = l_Lean_Meta_Try_Collector_getEqDefDecl_x3f___redArg(
                        v_declName_3341_,
                        v_a_3344_,
                        v_a_3345_,
                    );
                    if leanh::lean_obj_tag(v___x_3357_) == 0 {
                        v_a_3358_ = leanh::lean_ctor_get(v___x_3357_, 0);
                        v_isSharedCheck_3387_ =
                            (!leanh::lean_is_exclusive(v___x_3357_)) as u8;
                        if v_isSharedCheck_3387_ == 0 {
                            v___x_3360_ = v___x_3357_;
                            v_isShared_3361_ = v_isSharedCheck_3387_;
                            state = 3;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_3358_);
                            leanh::lean_dec(v___x_3357_);
                            v___x_3360_ = leanh::lean_box(0);
                            v_isShared_3361_ = v_isSharedCheck_3387_;
                            state = 3;
                            continue;
                        }
                    } else {
                        v_a_3388_ = leanh::lean_ctor_get(v___x_3357_, 0);
                        v_isSharedCheck_3395_ =
                            (!leanh::lean_is_exclusive(v___x_3357_)) as u8;
                        if v_isSharedCheck_3395_ == 0 {
                            v___x_3390_ = v___x_3357_;
                            v_isShared_3391_ = v_isSharedCheck_3395_;
                            state = 8;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_3388_);
                            leanh::lean_dec(v___x_3357_);
                            v___x_3390_ = leanh::lean_box(0);
                            v_isShared_3391_ = v_isSharedCheck_3395_;
                            state = 8;
                            continue;
                        }
                    }
                }
            }
            2 => {
                return v___x_3355_;
            }
            3 => {
                if leanh::lean_obj_tag(v_a_3358_) == 1 {
                    v_val_3362_ = leanh::lean_ctor_get(v_a_3358_, 0);
                    leanh::lean_inc(v_val_3362_);
                    leanh::lean_dec_ref_known(v_a_3358_, 1);
                    v___x_3363_ = lean_st_ref_take(v_a_3343_);
                    v_allConsts_3364_ = leanh::lean_ctor_get(v___x_3363_, 0);
                    v_unfoldCandidates_3365_ = leanh::lean_ctor_get(v___x_3363_, 1);
                    v_eqnCandidates_3366_ = leanh::lean_ctor_get(v___x_3363_, 2);
                    v_funIndCandidates_3367_ = leanh::lean_ctor_get(v___x_3363_, 3);
                    v_indCandidates_3368_ = leanh::lean_ctor_get(v___x_3363_, 4);
                    v_libSearchResults_3369_ = leanh::lean_ctor_get(v___x_3363_, 5);
                    v_isSharedCheck_3382_ = (!leanh::lean_is_exclusive(v___x_3363_)) as u8;
                    if v_isSharedCheck_3382_ == 0 {
                        v___x_3371_ = v___x_3363_;
                        v_isShared_3372_ = v_isSharedCheck_3382_;
                        state = 4;
                        continue;
                    } else {
                        leanh::lean_inc(v_libSearchResults_3369_);
                        leanh::lean_inc(v_indCandidates_3368_);
                        leanh::lean_inc(v_funIndCandidates_3367_);
                        leanh::lean_inc(v_eqnCandidates_3366_);
                        leanh::lean_inc(v_unfoldCandidates_3365_);
                        leanh::lean_inc(v_allConsts_3364_);
                        leanh::lean_dec(v___x_3363_);
                        v___x_3371_ = leanh::lean_box(0);
                        v_isShared_3372_ = v_isSharedCheck_3382_;
                        state = 4;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v_a_3358_);
                    v___x_3383_ = leanh::lean_box(0);
                    if v_isShared_3361_ == 0 {
                        leanh::lean_ctor_set(v___x_3360_, 0, v___x_3383_);
                        v___x_3385_ = v___x_3360_;
                        state = 7;
                        continue;
                    } else {
                        v_reuseFailAlloc_3386_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_3386_, 0, v___x_3383_);
                        v___x_3385_ = v_reuseFailAlloc_3386_;
                        state = 7;
                        continue;
                    }
                }
            }
            4 => {
                v___x_3373_ = l_Lean_Meta_Try_Collector_OrdSet_insert___at___00Lean_Meta_Try_Collector_saveConst_spec__0(v_unfoldCandidates_3365_, v_val_3362_);
                if v_isShared_3372_ == 0 {
                    leanh::lean_ctor_set(v___x_3371_, 1, v___x_3373_);
                    v___x_3375_ = v___x_3371_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_3381_ = leanh::lean_alloc_ctor(0, 6, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3381_, 0, v_allConsts_3364_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3381_, 1, v___x_3373_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3381_, 2, v_eqnCandidates_3366_);
                    leanh::lean_ctor_set(
                        v_reuseFailAlloc_3381_,
                        3,
                        v_funIndCandidates_3367_,
                    );
                    leanh::lean_ctor_set(v_reuseFailAlloc_3381_, 4, v_indCandidates_3368_);
                    leanh::lean_ctor_set(
                        v_reuseFailAlloc_3381_,
                        5,
                        v_libSearchResults_3369_,
                    );
                    v___x_3375_ = v_reuseFailAlloc_3381_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v___x_3376_ = lean_st_ref_set(v_a_3343_, v___x_3375_);
                v___x_3377_ = leanh::lean_box(0);
                if v_isShared_3361_ == 0 {
                    leanh::lean_ctor_set(v___x_3360_, 0, v___x_3377_);
                    v___x_3379_ = v___x_3360_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_3380_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3380_, 0, v___x_3377_);
                    v___x_3379_ = v_reuseFailAlloc_3380_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_3379_;
            }
            7 => {
                return v___x_3385_;
            }
            8 => {
                if v_isShared_3391_ == 0 {
                    v___x_3393_ = v___x_3390_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_3394_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3394_, 0, v_a_3388_);
                    v___x_3393_ = v_reuseFailAlloc_3394_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_3393_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Try_Collector_saveUnfoldCandidate___redArg___boxed(
    mut v_declName_3397_: *mut leanh::LeanObject,
    mut v_a_3398_: *mut leanh::LeanObject,
    mut v_a_3399_: *mut leanh::LeanObject,
    mut v_a_3400_: *mut leanh::LeanObject,
    mut v_a_3401_: *mut leanh::LeanObject,
    mut v_a_3402_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3403_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3403_ = l_Lean_Meta_Try_Collector_saveUnfoldCandidate___redArg(
        v_declName_3397_,
        v_a_3398_,
        v_a_3399_,
        v_a_3400_,
        v_a_3401_,
    );
    leanh::lean_dec(v_a_3401_);
    leanh::lean_dec_ref(v_a_3400_);
    leanh::lean_dec(v_a_3399_);
    leanh::lean_dec_ref(v_a_3398_);
    return v_res_3403_;
}
pub unsafe fn l_Lean_Meta_Try_Collector_saveUnfoldCandidate(
    mut v_declName_3404_: *mut leanh::LeanObject,
    mut v_a_3405_: *mut leanh::LeanObject,
    mut v_a_3406_: *mut leanh::LeanObject,
    mut v_a_3407_: *mut leanh::LeanObject,
    mut v_a_3408_: *mut leanh::LeanObject,
    mut v_a_3409_: *mut leanh::LeanObject,
    mut v_a_3410_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3412_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3412_ = l_Lean_Meta_Try_Collector_saveUnfoldCandidate___redArg(
        v_declName_3404_,
        v_a_3405_,
        v_a_3406_,
        v_a_3409_,
        v_a_3410_,
    );
    return v___x_3412_;
}
pub unsafe fn l_Lean_Meta_Try_Collector_saveUnfoldCandidate___boxed(
    mut v_declName_3413_: *mut leanh::LeanObject,
    mut v_a_3414_: *mut leanh::LeanObject,
    mut v_a_3415_: *mut leanh::LeanObject,
    mut v_a_3416_: *mut leanh::LeanObject,
    mut v_a_3417_: *mut leanh::LeanObject,
    mut v_a_3418_: *mut leanh::LeanObject,
    mut v_a_3419_: *mut leanh::LeanObject,
    mut v_a_3420_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3421_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3421_ = l_Lean_Meta_Try_Collector_saveUnfoldCandidate(
        v_declName_3413_,
        v_a_3414_,
        v_a_3415_,
        v_a_3416_,
        v_a_3417_,
        v_a_3418_,
        v_a_3419_,
    );
    leanh::lean_dec(v_a_3419_);
    leanh::lean_dec_ref(v_a_3418_);
    leanh::lean_dec(v_a_3417_);
    leanh::lean_dec_ref(v_a_3416_);
    leanh::lean_dec(v_a_3415_);
    leanh::lean_dec_ref(v_a_3414_);
    return v_res_3421_;
}
pub unsafe fn l_Lean_Meta_Try_Collector_visitConst___redArg(
    mut v_declName_3422_: *mut leanh::LeanObject,
    mut v_a_3423_: *mut leanh::LeanObject,
    mut v_a_3424_: *mut leanh::LeanObject,
    mut v_a_3425_: *mut leanh::LeanObject,
    mut v_a_3426_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3428_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3429_: *mut leanh::LeanObject = core::ptr::null_mut();
    leanh::lean_inc(v_declName_3422_);
    v___x_3428_ = l_Lean_Meta_Try_Collector_saveConst___redArg(v_declName_3422_, v_a_3424_);
    leanh::lean_dec_ref(v___x_3428_);
    v___x_3429_ = l_Lean_Meta_Try_Collector_saveUnfoldCandidate___redArg(
        v_declName_3422_,
        v_a_3423_,
        v_a_3424_,
        v_a_3425_,
        v_a_3426_,
    );
    return v___x_3429_;
}
pub unsafe fn l_Lean_Meta_Try_Collector_visitConst___redArg___boxed(
    mut v_declName_3430_: *mut leanh::LeanObject,
    mut v_a_3431_: *mut leanh::LeanObject,
    mut v_a_3432_: *mut leanh::LeanObject,
    mut v_a_3433_: *mut leanh::LeanObject,
    mut v_a_3434_: *mut leanh::LeanObject,
    mut v_a_3435_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3436_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3436_ = l_Lean_Meta_Try_Collector_visitConst___redArg(
        v_declName_3430_,
        v_a_3431_,
        v_a_3432_,
        v_a_3433_,
        v_a_3434_,
    );
    leanh::lean_dec(v_a_3434_);
    leanh::lean_dec_ref(v_a_3433_);
    leanh::lean_dec(v_a_3432_);
    leanh::lean_dec_ref(v_a_3431_);
    return v_res_3436_;
}
pub unsafe fn l_Lean_Meta_Try_Collector_visitConst(
    mut v_declName_3437_: *mut leanh::LeanObject,
    mut v_a_3438_: *mut leanh::LeanObject,
    mut v_a_3439_: *mut leanh::LeanObject,
    mut v_a_3440_: *mut leanh::LeanObject,
    mut v_a_3441_: *mut leanh::LeanObject,
    mut v_a_3442_: *mut leanh::LeanObject,
    mut v_a_3443_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3445_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3445_ = l_Lean_Meta_Try_Collector_visitConst___redArg(
        v_declName_3437_,
        v_a_3438_,
        v_a_3439_,
        v_a_3442_,
        v_a_3443_,
    );
    return v___x_3445_;
}
pub unsafe fn l_Lean_Meta_Try_Collector_visitConst___boxed(
    mut v_declName_3446_: *mut leanh::LeanObject,
    mut v_a_3447_: *mut leanh::LeanObject,
    mut v_a_3448_: *mut leanh::LeanObject,
    mut v_a_3449_: *mut leanh::LeanObject,
    mut v_a_3450_: *mut leanh::LeanObject,
    mut v_a_3451_: *mut leanh::LeanObject,
    mut v_a_3452_: *mut leanh::LeanObject,
    mut v_a_3453_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3454_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3454_ = l_Lean_Meta_Try_Collector_visitConst(
        v_declName_3446_,
        v_a_3447_,
        v_a_3448_,
        v_a_3449_,
        v_a_3450_,
        v_a_3451_,
        v_a_3452_,
    );
    leanh::lean_dec(v_a_3452_);
    leanh::lean_dec_ref(v_a_3451_);
    leanh::lean_dec(v_a_3450_);
    leanh::lean_dec_ref(v_a_3449_);
    leanh::lean_dec(v_a_3448_);
    leanh::lean_dec_ref(v_a_3447_);
    return v_res_3454_;
}
pub unsafe fn l_Lean_Meta_Try_Collector_saveFunInd(
    mut v_e_3455_: *mut leanh::LeanObject,
    mut v_declName_3456_: *mut leanh::LeanObject,
    mut v_args_3457_: *mut leanh::LeanObject,
    mut v_a_3458_: *mut leanh::LeanObject,
    mut v_a_3459_: *mut leanh::LeanObject,
    mut v_a_3460_: *mut leanh::LeanObject,
    mut v_a_3461_: *mut leanh::LeanObject,
    mut v_a_3462_: *mut leanh::LeanObject,
    mut v_a_3463_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3465_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3466_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3468_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3469_: u8 = 0;
    let mut v___x_3470_: u8 = 0;
    let mut v___x_3471_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3473_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3474_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3475_: u8 = 0;
    let mut v___x_3476_: u8 = 0;
    let mut v___x_3477_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3478_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3480_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3481_: u8 = 0;
    let mut v_val_3482_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3483_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_funIndCandidates_3484_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3485_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3486_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3488_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3489_: u8 = 0;
    let mut v___x_3490_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_allConsts_3491_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unfoldCandidates_3492_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_eqnCandidates_3493_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_indCandidates_3494_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_libSearchResults_3495_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3497_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3498_: u8 = 0;
    let mut v___x_3500_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3501_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3502_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3504_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3505_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3506_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3507_: u8 = 0;
    let mut v_unused_3508_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3509_: u8 = 0;
    let mut v_a_3510_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3512_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3513_: u8 = 0;
    let mut v___x_3515_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3516_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3517_: u8 = 0;
    let mut v___x_3518_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3520_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3521_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3522_: u8 = 0;
    let mut v_a_3523_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3525_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3526_: u8 = 0;
    let mut v___x_3528_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3529_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3530_: u8 = 0;
    let mut v_isSharedCheck_3531_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3465_ = l_Lean_Meta_Try_Collector_isEligible___redArg(
                    v_declName_3456_,
                    v_a_3458_,
                    v_a_3462_,
                    v_a_3463_,
                );
                v_a_3466_ = leanh::lean_ctor_get(v___x_3465_, 0);
                v_isSharedCheck_3531_ = (!leanh::lean_is_exclusive(v___x_3465_)) as u8;
                if v_isSharedCheck_3531_ == 0 {
                    v___x_3468_ = v___x_3465_;
                    v_isShared_3469_ = v_isSharedCheck_3531_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_a_3466_);
                    leanh::lean_dec(v___x_3465_);
                    v___x_3468_ = leanh::lean_box(0);
                    v_isShared_3469_ = v_isSharedCheck_3531_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_3470_ = (leanh::lean_unbox(v_a_3466_) as u8);
                if v___x_3470_ == 0 {
                    leanh::lean_dec(v_a_3466_);
                    leanh::lean_dec(v_declName_3456_);
                    leanh::lean_dec_ref(v_e_3455_);
                    v___x_3471_ = leanh::lean_box(0);
                    if v_isShared_3469_ == 0 {
                        leanh::lean_ctor_set(v___x_3468_, 0, v___x_3471_);
                        v___x_3473_ = v___x_3468_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_3474_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_3474_, 0, v___x_3471_);
                        v___x_3473_ = v_reuseFailAlloc_3474_;
                        state = 2;
                        continue;
                    }
                } else {
                    leanh::lean_del_object(v___x_3468_);
                    v___x_3475_ = 0;
                    v___x_3476_ = (leanh::lean_unbox(v_a_3466_) as u8);
                    leanh::lean_dec(v_a_3466_);
                    v___x_3477_ = l_Lean_Meta_getFunIndInfo_x3f(
                        v___x_3475_,
                        v___x_3476_,
                        v_declName_3456_,
                        v_a_3462_,
                        v_a_3463_,
                    );
                    if leanh::lean_obj_tag(v___x_3477_) == 0 {
                        v_a_3478_ = leanh::lean_ctor_get(v___x_3477_, 0);
                        v_isSharedCheck_3522_ =
                            (!leanh::lean_is_exclusive(v___x_3477_)) as u8;
                        if v_isSharedCheck_3522_ == 0 {
                            v___x_3480_ = v___x_3477_;
                            v_isShared_3481_ = v_isSharedCheck_3522_;
                            state = 3;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_3478_);
                            leanh::lean_dec(v___x_3477_);
                            v___x_3480_ = leanh::lean_box(0);
                            v_isShared_3481_ = v_isSharedCheck_3522_;
                            state = 3;
                            continue;
                        }
                    } else {
                        leanh::lean_dec_ref(v_e_3455_);
                        v_a_3523_ = leanh::lean_ctor_get(v___x_3477_, 0);
                        v_isSharedCheck_3530_ =
                            (!leanh::lean_is_exclusive(v___x_3477_)) as u8;
                        if v_isSharedCheck_3530_ == 0 {
                            v___x_3525_ = v___x_3477_;
                            v_isShared_3526_ = v_isSharedCheck_3530_;
                            state = 11;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_3523_);
                            leanh::lean_dec(v___x_3477_);
                            v___x_3525_ = leanh::lean_box(0);
                            v_isShared_3526_ = v_isSharedCheck_3530_;
                            state = 11;
                            continue;
                        }
                    }
                }
            }
            2 => {
                return v___x_3473_;
            }
            3 => {
                if leanh::lean_obj_tag(v_a_3478_) == 1 {
                    leanh::lean_del_object(v___x_3480_);
                    v_val_3482_ = leanh::lean_ctor_get(v_a_3478_, 0);
                    leanh::lean_inc(v_val_3482_);
                    leanh::lean_dec_ref_known(v_a_3478_, 1);
                    v___x_3483_ = lean_st_ref_get(v_a_3459_);
                    v_funIndCandidates_3484_ = leanh::lean_ctor_get(v___x_3483_, 3);
                    leanh::lean_inc_ref(v_funIndCandidates_3484_);
                    leanh::lean_dec(v___x_3483_);
                    v___x_3485_ = l_Lean_Meta_FunInd_SeenCalls_push(
                        v_e_3455_,
                        v_val_3482_,
                        v_args_3457_,
                        v_funIndCandidates_3484_,
                        v_a_3460_,
                        v_a_3461_,
                        v_a_3462_,
                        v_a_3463_,
                    );
                    if leanh::lean_obj_tag(v___x_3485_) == 0 {
                        v_a_3486_ = leanh::lean_ctor_get(v___x_3485_, 0);
                        v_isSharedCheck_3509_ =
                            (!leanh::lean_is_exclusive(v___x_3485_)) as u8;
                        if v_isSharedCheck_3509_ == 0 {
                            v___x_3488_ = v___x_3485_;
                            v_isShared_3489_ = v_isSharedCheck_3509_;
                            state = 4;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_3486_);
                            leanh::lean_dec(v___x_3485_);
                            v___x_3488_ = leanh::lean_box(0);
                            v_isShared_3489_ = v_isSharedCheck_3509_;
                            state = 4;
                            continue;
                        }
                    } else {
                        v_a_3510_ = leanh::lean_ctor_get(v___x_3485_, 0);
                        v_isSharedCheck_3517_ =
                            (!leanh::lean_is_exclusive(v___x_3485_)) as u8;
                        if v_isSharedCheck_3517_ == 0 {
                            v___x_3512_ = v___x_3485_;
                            v_isShared_3513_ = v_isSharedCheck_3517_;
                            state = 8;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_3510_);
                            leanh::lean_dec(v___x_3485_);
                            v___x_3512_ = leanh::lean_box(0);
                            v_isShared_3513_ = v_isSharedCheck_3517_;
                            state = 8;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_dec(v_a_3478_);
                    leanh::lean_dec_ref(v_e_3455_);
                    v___x_3518_ = leanh::lean_box(0);
                    if v_isShared_3481_ == 0 {
                        leanh::lean_ctor_set(v___x_3480_, 0, v___x_3518_);
                        v___x_3520_ = v___x_3480_;
                        state = 10;
                        continue;
                    } else {
                        v_reuseFailAlloc_3521_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_3521_, 0, v___x_3518_);
                        v___x_3520_ = v_reuseFailAlloc_3521_;
                        state = 10;
                        continue;
                    }
                }
            }
            4 => {
                v___x_3490_ = lean_st_ref_take(v_a_3459_);
                v_allConsts_3491_ = leanh::lean_ctor_get(v___x_3490_, 0);
                v_unfoldCandidates_3492_ = leanh::lean_ctor_get(v___x_3490_, 1);
                v_eqnCandidates_3493_ = leanh::lean_ctor_get(v___x_3490_, 2);
                v_indCandidates_3494_ = leanh::lean_ctor_get(v___x_3490_, 4);
                v_libSearchResults_3495_ = leanh::lean_ctor_get(v___x_3490_, 5);
                v_isSharedCheck_3507_ = (!leanh::lean_is_exclusive(v___x_3490_)) as u8;
                if v_isSharedCheck_3507_ == 0 {
                    v_unused_3508_ = leanh::lean_ctor_get(v___x_3490_, 3);
                    leanh::lean_dec(v_unused_3508_);
                    v___x_3497_ = v___x_3490_;
                    v_isShared_3498_ = v_isSharedCheck_3507_;
                    state = 5;
                    continue;
                } else {
                    leanh::lean_inc(v_libSearchResults_3495_);
                    leanh::lean_inc(v_indCandidates_3494_);
                    leanh::lean_inc(v_eqnCandidates_3493_);
                    leanh::lean_inc(v_unfoldCandidates_3492_);
                    leanh::lean_inc(v_allConsts_3491_);
                    leanh::lean_dec(v___x_3490_);
                    v___x_3497_ = leanh::lean_box(0);
                    v_isShared_3498_ = v_isSharedCheck_3507_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                if v_isShared_3498_ == 0 {
                    leanh::lean_ctor_set(v___x_3497_, 3, v_a_3486_);
                    v___x_3500_ = v___x_3497_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_3506_ = leanh::lean_alloc_ctor(0, 6, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3506_, 0, v_allConsts_3491_);
                    leanh::lean_ctor_set(
                        v_reuseFailAlloc_3506_,
                        1,
                        v_unfoldCandidates_3492_,
                    );
                    leanh::lean_ctor_set(v_reuseFailAlloc_3506_, 2, v_eqnCandidates_3493_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3506_, 3, v_a_3486_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3506_, 4, v_indCandidates_3494_);
                    leanh::lean_ctor_set(
                        v_reuseFailAlloc_3506_,
                        5,
                        v_libSearchResults_3495_,
                    );
                    v___x_3500_ = v_reuseFailAlloc_3506_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                v___x_3501_ = lean_st_ref_set(v_a_3459_, v___x_3500_);
                v___x_3502_ = leanh::lean_box(0);
                if v_isShared_3489_ == 0 {
                    leanh::lean_ctor_set(v___x_3488_, 0, v___x_3502_);
                    v___x_3504_ = v___x_3488_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_3505_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3505_, 0, v___x_3502_);
                    v___x_3504_ = v_reuseFailAlloc_3505_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_3504_;
            }
            8 => {
                if v_isShared_3513_ == 0 {
                    v___x_3515_ = v___x_3512_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_3516_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3516_, 0, v_a_3510_);
                    v___x_3515_ = v_reuseFailAlloc_3516_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_3515_;
            }
            10 => {
                return v___x_3520_;
            }
            11 => {
                if v_isShared_3526_ == 0 {
                    v___x_3528_ = v___x_3525_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_3529_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3529_, 0, v_a_3523_);
                    v___x_3528_ = v_reuseFailAlloc_3529_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                return v___x_3528_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Try_Collector_saveFunInd___boxed(
    mut v_e_3532_: *mut leanh::LeanObject,
    mut v_declName_3533_: *mut leanh::LeanObject,
    mut v_args_3534_: *mut leanh::LeanObject,
    mut v_a_3535_: *mut leanh::LeanObject,
    mut v_a_3536_: *mut leanh::LeanObject,
    mut v_a_3537_: *mut leanh::LeanObject,
    mut v_a_3538_: *mut leanh::LeanObject,
    mut v_a_3539_: *mut leanh::LeanObject,
    mut v_a_3540_: *mut leanh::LeanObject,
    mut v_a_3541_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3542_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3542_ = l_Lean_Meta_Try_Collector_saveFunInd(
        v_e_3532_,
        v_declName_3533_,
        v_args_3534_,
        v_a_3535_,
        v_a_3536_,
        v_a_3537_,
        v_a_3538_,
        v_a_3539_,
        v_a_3540_,
    );
    leanh::lean_dec(v_a_3540_);
    leanh::lean_dec_ref(v_a_3539_);
    leanh::lean_dec(v_a_3538_);
    leanh::lean_dec_ref(v_a_3537_);
    leanh::lean_dec(v_a_3536_);
    leanh::lean_dec_ref(v_a_3535_);
    leanh::lean_dec_ref(v_args_3534_);
    return v_res_3542_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Try_Collector_OrdSet_insert___at___00Lean_Meta_Try_Collector_saveLibSearchCandidates_spec__0_spec__0_spec__1___redArg(
    mut v_a_3543_: *mut leanh::LeanObject,
    mut v_x_3544_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_3545_: u8 = 0;
    let mut v_key_3546_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_3547_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3549_: u8 = 0;
    let mut v_fst_3551_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3552_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_3553_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3554_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3555_: u8 = 0;
    let mut v___x_3556_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_3544_) == 0 {
                    v___x_3545_ = 0;
                    return v___x_3545_;
                } else {
                    v_key_3546_ = leanh::lean_ctor_get(v_x_3544_, 0);
                    v_tail_3547_ = leanh::lean_ctor_get(v_x_3544_, 2);
                    v_fst_3551_ = leanh::lean_ctor_get(v_key_3546_, 0);
                    v_snd_3552_ = leanh::lean_ctor_get(v_key_3546_, 1);
                    v_fst_3553_ = leanh::lean_ctor_get(v_a_3543_, 0);
                    v_snd_3554_ = leanh::lean_ctor_get(v_a_3543_, 1);
                    v___x_3555_ = lean_name_eq(v_fst_3551_, v_fst_3553_);
                    if v___x_3555_ == 0 {
                        v___y_3549_ = v___x_3555_;
                        state = 1;
                        continue;
                    } else {
                        v___x_3556_ = l_Lean_Meta_Grind_instBEqEMatchTheoremKind_beq(
                            v_snd_3552_,
                            v_snd_3554_,
                        );
                        v___y_3549_ = v___x_3556_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v___y_3549_ == 0 {
                    v_x_3544_ = v_tail_3547_;
                    state = 0;
                    continue;
                } else {
                    return v___y_3549_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Try_Collector_OrdSet_insert___at___00Lean_Meta_Try_Collector_saveLibSearchCandidates_spec__0_spec__0_spec__1___redArg___boxed(
    mut v_a_3557_: *mut leanh::LeanObject,
    mut v_x_3558_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3559_: u8 = 0;
    let mut v_r_3560_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3559_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Try_Collector_OrdSet_insert___at___00Lean_Meta_Try_Collector_saveLibSearchCandidates_spec__0_spec__0_spec__1___redArg(v_a_3557_, v_x_3558_);
    leanh::lean_dec(v_x_3558_);
    leanh::lean_dec_ref(v_a_3557_);
    v_r_3560_ = leanh::lean_box((v_res_3559_) as usize);
    return v_r_3560_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Try_Collector_OrdSet_insert___at___00Lean_Meta_Try_Collector_saveLibSearchCandidates_spec__0_spec__0___redArg(
    mut v_m_3561_: *mut leanh::LeanObject,
    mut v_a_3562_: *mut leanh::LeanObject,
) -> u8 {
    let mut v_buckets_3563_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_3564_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3565_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3566_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3568_: u64 = 0;
    let mut v___x_3569_: u64 = 0;
    let mut v___x_3570_: u64 = 0;
    let mut v___x_3571_: u64 = 0;
    let mut v___x_3572_: u64 = 0;
    let mut v_fold_3573_: u64 = 0;
    let mut v___x_3574_: u64 = 0;
    let mut v___x_3575_: u64 = 0;
    let mut v___x_3576_: u64 = 0;
    let mut v___x_3577_: usize = 0;
    let mut v___x_3578_: usize = 0;
    let mut v___x_3579_: usize = 0;
    let mut v___x_3580_: usize = 0;
    let mut v___x_3581_: usize = 0;
    let mut v___x_3582_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3583_: u8 = 0;
    let mut v___x_3584_: u64 = 0;
    let mut v_hash_3585_: u64 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_buckets_3563_ = leanh::lean_ctor_get(v_m_3561_, 1);
                v_fst_3564_ = leanh::lean_ctor_get(v_a_3562_, 0);
                v_snd_3565_ = leanh::lean_ctor_get(v_a_3562_, 1);
                v___x_3566_ = lean_array_get_size(v_buckets_3563_);
                if leanh::lean_obj_tag(v_fst_3564_) == 0 {
                    v___x_3584_ = leanh::lean_uint64_once(core::ptr::addr_of_mut!(l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Try_Collector_OrdSet_insert___at___00Lean_Meta_Try_Collector_saveConst_spec__0_spec__0___redArg___closed__0), core::ptr::addr_of_mut!(l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Try_Collector_OrdSet_insert___at___00Lean_Meta_Try_Collector_saveConst_spec__0_spec__0___redArg___closed__0_once), _init_l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Try_Collector_OrdSet_insert___at___00Lean_Meta_Try_Collector_saveConst_spec__0_spec__0___redArg___closed__0);
                    v___y_3568_ = v___x_3584_;
                    state = 1;
                    continue;
                } else {
                    v_hash_3585_ = leanh::lean_ctor_get_uint64(
                        v_fst_3564_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 2) as u32,
                    );
                    v___y_3568_ = v_hash_3585_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_3569_ = l_Lean_Meta_Grind_instHashableEMatchTheoremKind_hash(v_snd_3565_);
                v___x_3570_ = lean_uint64_mix_hash(v___y_3568_, v___x_3569_);
                v___x_3571_ = 32u64;
                v___x_3572_ = lean_uint64_shift_right(v___x_3570_, v___x_3571_);
                v_fold_3573_ = lean_uint64_xor(v___x_3570_, v___x_3572_);
                v___x_3574_ = 16u64;
                v___x_3575_ = lean_uint64_shift_right(v_fold_3573_, v___x_3574_);
                v___x_3576_ = lean_uint64_xor(v_fold_3573_, v___x_3575_);
                v___x_3577_ = lean_uint64_to_usize(v___x_3576_);
                v___x_3578_ = lean_usize_of_nat(v___x_3566_);
                v___x_3579_ = 1usize;
                v___x_3580_ = lean_usize_sub(v___x_3578_, v___x_3579_);
                v___x_3581_ = lean_usize_land(v___x_3577_, v___x_3580_);
                v___x_3582_ = lean_array_uget_borrowed(v_buckets_3563_, v___x_3581_);
                v___x_3583_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Try_Collector_OrdSet_insert___at___00Lean_Meta_Try_Collector_saveLibSearchCandidates_spec__0_spec__0_spec__1___redArg(v_a_3562_, v___x_3582_);
                return v___x_3583_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Try_Collector_OrdSet_insert___at___00Lean_Meta_Try_Collector_saveLibSearchCandidates_spec__0_spec__0___redArg___boxed(
    mut v_m_3586_: *mut leanh::LeanObject,
    mut v_a_3587_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3588_: u8 = 0;
    let mut v_r_3589_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3588_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Try_Collector_OrdSet_insert___at___00Lean_Meta_Try_Collector_saveLibSearchCandidates_spec__0_spec__0___redArg(v_m_3586_, v_a_3587_);
    leanh::lean_dec_ref(v_a_3587_);
    leanh::lean_dec_ref(v_m_3586_);
    v_r_3589_ = leanh::lean_box((v_res_3588_) as usize);
    return v_r_3589_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Try_Collector_OrdSet_insert___at___00Lean_Meta_Try_Collector_saveLibSearchCandidates_spec__0_spec__1_spec__3_spec__5_spec__6___redArg(
    mut v_x_3590_: *mut leanh::LeanObject,
    mut v_x_3591_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_key_3592_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_3593_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_3594_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3596_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3597_: u8 = 0;
    let mut v_fst_3598_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3599_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3600_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3602_: u64 = 0;
    let mut v___x_3603_: u64 = 0;
    let mut v___x_3604_: u64 = 0;
    let mut v___x_3605_: u64 = 0;
    let mut v___x_3606_: u64 = 0;
    let mut v_fold_3607_: u64 = 0;
    let mut v___x_3608_: u64 = 0;
    let mut v___x_3609_: u64 = 0;
    let mut v___x_3610_: u64 = 0;
    let mut v___x_3611_: usize = 0;
    let mut v___x_3612_: usize = 0;
    let mut v___x_3613_: usize = 0;
    let mut v___x_3614_: usize = 0;
    let mut v___x_3615_: usize = 0;
    let mut v___x_3616_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3618_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3619_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3621_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3622_: u64 = 0;
    let mut v_hash_3623_: u64 = 0;
    let mut v_isSharedCheck_3624_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_3591_) == 0 {
                    return v_x_3590_;
                } else {
                    v_key_3592_ = leanh::lean_ctor_get(v_x_3591_, 0);
                    v_value_3593_ = leanh::lean_ctor_get(v_x_3591_, 1);
                    v_tail_3594_ = leanh::lean_ctor_get(v_x_3591_, 2);
                    v_isSharedCheck_3624_ = (!leanh::lean_is_exclusive(v_x_3591_)) as u8;
                    if v_isSharedCheck_3624_ == 0 {
                        v___x_3596_ = v_x_3591_;
                        v_isShared_3597_ = v_isSharedCheck_3624_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_tail_3594_);
                        leanh::lean_inc(v_value_3593_);
                        leanh::lean_inc(v_key_3592_);
                        leanh::lean_dec(v_x_3591_);
                        v___x_3596_ = leanh::lean_box(0);
                        v_isShared_3597_ = v_isSharedCheck_3624_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_fst_3598_ = leanh::lean_ctor_get(v_key_3592_, 0);
                v_snd_3599_ = leanh::lean_ctor_get(v_key_3592_, 1);
                v___x_3600_ = lean_array_get_size(v_x_3590_);
                if leanh::lean_obj_tag(v_fst_3598_) == 0 {
                    v___x_3622_ = leanh::lean_uint64_once(core::ptr::addr_of_mut!(l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Try_Collector_OrdSet_insert___at___00Lean_Meta_Try_Collector_saveConst_spec__0_spec__0___redArg___closed__0), core::ptr::addr_of_mut!(l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Try_Collector_OrdSet_insert___at___00Lean_Meta_Try_Collector_saveConst_spec__0_spec__0___redArg___closed__0_once), _init_l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Try_Collector_OrdSet_insert___at___00Lean_Meta_Try_Collector_saveConst_spec__0_spec__0___redArg___closed__0);
                    v___y_3602_ = v___x_3622_;
                    state = 2;
                    continue;
                } else {
                    v_hash_3623_ = leanh::lean_ctor_get_uint64(
                        v_fst_3598_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 2) as u32,
                    );
                    v___y_3602_ = v_hash_3623_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_3603_ = l_Lean_Meta_Grind_instHashableEMatchTheoremKind_hash(v_snd_3599_);
                v___x_3604_ = lean_uint64_mix_hash(v___y_3602_, v___x_3603_);
                v___x_3605_ = 32u64;
                v___x_3606_ = lean_uint64_shift_right(v___x_3604_, v___x_3605_);
                v_fold_3607_ = lean_uint64_xor(v___x_3604_, v___x_3606_);
                v___x_3608_ = 16u64;
                v___x_3609_ = lean_uint64_shift_right(v_fold_3607_, v___x_3608_);
                v___x_3610_ = lean_uint64_xor(v_fold_3607_, v___x_3609_);
                v___x_3611_ = lean_uint64_to_usize(v___x_3610_);
                v___x_3612_ = lean_usize_of_nat(v___x_3600_);
                v___x_3613_ = 1usize;
                v___x_3614_ = lean_usize_sub(v___x_3612_, v___x_3613_);
                v___x_3615_ = lean_usize_land(v___x_3611_, v___x_3614_);
                v___x_3616_ = lean_array_uget_borrowed(v_x_3590_, v___x_3615_);
                leanh::lean_inc(v___x_3616_);
                if v_isShared_3597_ == 0 {
                    leanh::lean_ctor_set(v___x_3596_, 2, v___x_3616_);
                    v___x_3618_ = v___x_3596_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_3621_ = leanh::lean_alloc_ctor(1, 3, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3621_, 0, v_key_3592_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3621_, 1, v_value_3593_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3621_, 2, v___x_3616_);
                    v___x_3618_ = v_reuseFailAlloc_3621_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_3619_ = lean_array_uset(v_x_3590_, v___x_3615_, v___x_3618_);
                v_x_3590_ = v___x_3619_;
                v_x_3591_ = v_tail_3594_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Try_Collector_OrdSet_insert___at___00Lean_Meta_Try_Collector_saveLibSearchCandidates_spec__0_spec__1_spec__3_spec__5___redArg(
    mut v_i_3625_: *mut leanh::LeanObject,
    mut v_source_3626_: *mut leanh::LeanObject,
    mut v_target_3627_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3628_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3629_: u8 = 0;
    let mut v_es_3630_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3631_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_source_3632_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_target_3633_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3634_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3635_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3628_ = lean_array_get_size(v_source_3626_);
                v___x_3629_ = lean_nat_dec_lt(v_i_3625_, v___x_3628_);
                if v___x_3629_ == 0 {
                    leanh::lean_dec_ref(v_source_3626_);
                    leanh::lean_dec(v_i_3625_);
                    return v_target_3627_;
                } else {
                    v_es_3630_ = lean_array_fget(v_source_3626_, v_i_3625_);
                    v___x_3631_ = leanh::lean_box(0);
                    v_source_3632_ = lean_array_fset(v_source_3626_, v_i_3625_, v___x_3631_);
                    v_target_3633_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Try_Collector_OrdSet_insert___at___00Lean_Meta_Try_Collector_saveLibSearchCandidates_spec__0_spec__1_spec__3_spec__5_spec__6___redArg(v_target_3627_, v_es_3630_);
                    v___x_3634_ = leanh::lean_unsigned_to_nat(1);
                    v___x_3635_ = lean_nat_add(v_i_3625_, v___x_3634_);
                    leanh::lean_dec(v_i_3625_);
                    v_i_3625_ = v___x_3635_;
                    v_source_3626_ = v_source_3632_;
                    v_target_3627_ = v_target_3633_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Try_Collector_OrdSet_insert___at___00Lean_Meta_Try_Collector_saveLibSearchCandidates_spec__0_spec__1_spec__3___redArg(
    mut v_data_3637_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3638_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3639_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_nbuckets_3640_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3641_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3642_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3643_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3644_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3638_ = lean_array_get_size(v_data_3637_);
    v___x_3639_ = leanh::lean_unsigned_to_nat(2);
    v_nbuckets_3640_ = lean_nat_mul(v___x_3638_, v___x_3639_);
    v___x_3641_ = leanh::lean_unsigned_to_nat(0);
    v___x_3642_ = leanh::lean_box(0);
    v___x_3643_ = lean_mk_array(v_nbuckets_3640_, v___x_3642_);
    v___x_3644_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Try_Collector_OrdSet_insert___at___00Lean_Meta_Try_Collector_saveLibSearchCandidates_spec__0_spec__1_spec__3_spec__5___redArg(v___x_3641_, v_data_3637_, v___x_3643_);
    return v___x_3644_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Try_Collector_OrdSet_insert___at___00Lean_Meta_Try_Collector_saveLibSearchCandidates_spec__0_spec__1___redArg(
    mut v_m_3645_: *mut leanh::LeanObject,
    mut v_a_3646_: *mut leanh::LeanObject,
    mut v_b_3647_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_size_3648_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_3649_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_3650_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3651_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3652_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3654_: u64 = 0;
    let mut v___x_3655_: u64 = 0;
    let mut v___x_3656_: u64 = 0;
    let mut v___x_3657_: u64 = 0;
    let mut v___x_3658_: u64 = 0;
    let mut v_fold_3659_: u64 = 0;
    let mut v___x_3660_: u64 = 0;
    let mut v___x_3661_: u64 = 0;
    let mut v___x_3662_: u64 = 0;
    let mut v___x_3663_: usize = 0;
    let mut v___x_3664_: usize = 0;
    let mut v___x_3665_: usize = 0;
    let mut v___x_3666_: usize = 0;
    let mut v___x_3667_: usize = 0;
    let mut v_bkt_3668_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3669_: u8 = 0;
    let mut v___x_3671_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3672_: u8 = 0;
    let mut v___x_3673_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_x27_3674_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3675_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_x27_3676_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3677_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3678_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3679_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3680_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3681_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3682_: u8 = 0;
    let mut v_val_3683_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3685_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3686_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3688_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3689_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3690_: u8 = 0;
    let mut v_unused_3691_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3692_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3693_: u64 = 0;
    let mut v_hash_3694_: u64 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_size_3648_ = leanh::lean_ctor_get(v_m_3645_, 0);
                v_buckets_3649_ = leanh::lean_ctor_get(v_m_3645_, 1);
                v_fst_3650_ = leanh::lean_ctor_get(v_a_3646_, 0);
                v_snd_3651_ = leanh::lean_ctor_get(v_a_3646_, 1);
                v___x_3652_ = lean_array_get_size(v_buckets_3649_);
                if leanh::lean_obj_tag(v_fst_3650_) == 0 {
                    v___x_3693_ = leanh::lean_uint64_once(core::ptr::addr_of_mut!(l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Try_Collector_OrdSet_insert___at___00Lean_Meta_Try_Collector_saveConst_spec__0_spec__0___redArg___closed__0), core::ptr::addr_of_mut!(l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Try_Collector_OrdSet_insert___at___00Lean_Meta_Try_Collector_saveConst_spec__0_spec__0___redArg___closed__0_once), _init_l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Try_Collector_OrdSet_insert___at___00Lean_Meta_Try_Collector_saveConst_spec__0_spec__0___redArg___closed__0);
                    v___y_3654_ = v___x_3693_;
                    state = 1;
                    continue;
                } else {
                    v_hash_3694_ = leanh::lean_ctor_get_uint64(
                        v_fst_3650_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 2) as u32,
                    );
                    v___y_3654_ = v_hash_3694_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_3655_ = l_Lean_Meta_Grind_instHashableEMatchTheoremKind_hash(v_snd_3651_);
                v___x_3656_ = lean_uint64_mix_hash(v___y_3654_, v___x_3655_);
                v___x_3657_ = 32u64;
                v___x_3658_ = lean_uint64_shift_right(v___x_3656_, v___x_3657_);
                v_fold_3659_ = lean_uint64_xor(v___x_3656_, v___x_3658_);
                v___x_3660_ = 16u64;
                v___x_3661_ = lean_uint64_shift_right(v_fold_3659_, v___x_3660_);
                v___x_3662_ = lean_uint64_xor(v_fold_3659_, v___x_3661_);
                v___x_3663_ = lean_uint64_to_usize(v___x_3662_);
                v___x_3664_ = lean_usize_of_nat(v___x_3652_);
                v___x_3665_ = 1usize;
                v___x_3666_ = lean_usize_sub(v___x_3664_, v___x_3665_);
                v___x_3667_ = lean_usize_land(v___x_3663_, v___x_3666_);
                v_bkt_3668_ = lean_array_uget_borrowed(v_buckets_3649_, v___x_3667_);
                v___x_3669_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Try_Collector_OrdSet_insert___at___00Lean_Meta_Try_Collector_saveLibSearchCandidates_spec__0_spec__0_spec__1___redArg(v_a_3646_, v_bkt_3668_);
                if v___x_3669_ == 0 {
                    leanh::lean_inc_ref(v_buckets_3649_);
                    leanh::lean_inc(v_size_3648_);
                    v_isSharedCheck_3690_ = (!leanh::lean_is_exclusive(v_m_3645_)) as u8;
                    if v_isSharedCheck_3690_ == 0 {
                        v_unused_3691_ = leanh::lean_ctor_get(v_m_3645_, 1);
                        leanh::lean_dec(v_unused_3691_);
                        v_unused_3692_ = leanh::lean_ctor_get(v_m_3645_, 0);
                        leanh::lean_dec(v_unused_3692_);
                        v___x_3671_ = v_m_3645_;
                        v_isShared_3672_ = v_isSharedCheck_3690_;
                        state = 2;
                        continue;
                    } else {
                        leanh::lean_dec(v_m_3645_);
                        v___x_3671_ = leanh::lean_box(0);
                        v_isShared_3672_ = v_isSharedCheck_3690_;
                        state = 2;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v_b_3647_);
                    leanh::lean_dec_ref(v_a_3646_);
                    return v_m_3645_;
                }
            }
            2 => {
                v___x_3673_ = leanh::lean_unsigned_to_nat(1);
                v_size_x27_3674_ = lean_nat_add(v_size_3648_, v___x_3673_);
                leanh::lean_dec(v_size_3648_);
                leanh::lean_inc(v_bkt_3668_);
                v___x_3675_ = leanh::lean_alloc_ctor(1, 3, (0) as u32);
                leanh::lean_ctor_set(v___x_3675_, 0, v_a_3646_);
                leanh::lean_ctor_set(v___x_3675_, 1, v_b_3647_);
                leanh::lean_ctor_set(v___x_3675_, 2, v_bkt_3668_);
                v_buckets_x27_3676_ = lean_array_uset(v_buckets_3649_, v___x_3667_, v___x_3675_);
                v___x_3677_ = leanh::lean_unsigned_to_nat(4);
                v___x_3678_ = lean_nat_mul(v_size_x27_3674_, v___x_3677_);
                v___x_3679_ = leanh::lean_unsigned_to_nat(3);
                v___x_3680_ = lean_nat_div(v___x_3678_, v___x_3679_);
                leanh::lean_dec(v___x_3678_);
                v___x_3681_ = lean_array_get_size(v_buckets_x27_3676_);
                v___x_3682_ = lean_nat_dec_le(v___x_3680_, v___x_3681_);
                leanh::lean_dec(v___x_3680_);
                if v___x_3682_ == 0 {
                    v_val_3683_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Try_Collector_OrdSet_insert___at___00Lean_Meta_Try_Collector_saveLibSearchCandidates_spec__0_spec__1_spec__3___redArg(v_buckets_x27_3676_);
                    if v_isShared_3672_ == 0 {
                        leanh::lean_ctor_set(v___x_3671_, 1, v_val_3683_);
                        leanh::lean_ctor_set(v___x_3671_, 0, v_size_x27_3674_);
                        v___x_3685_ = v___x_3671_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_3686_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_3686_, 0, v_size_x27_3674_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_3686_, 1, v_val_3683_);
                        v___x_3685_ = v_reuseFailAlloc_3686_;
                        state = 3;
                        continue;
                    }
                } else {
                    if v_isShared_3672_ == 0 {
                        leanh::lean_ctor_set(v___x_3671_, 1, v_buckets_x27_3676_);
                        leanh::lean_ctor_set(v___x_3671_, 0, v_size_x27_3674_);
                        v___x_3688_ = v___x_3671_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_3689_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_3689_, 0, v_size_x27_3674_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_3689_, 1, v_buckets_x27_3676_);
                        v___x_3688_ = v_reuseFailAlloc_3689_;
                        state = 4;
                        continue;
                    }
                }
            }
            3 => {
                return v___x_3685_;
            }
            4 => {
                return v___x_3688_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Try_Collector_OrdSet_insert___at___00Lean_Meta_Try_Collector_saveLibSearchCandidates_spec__0(
    mut v_s_3695_: *mut leanh::LeanObject,
    mut v_a_3696_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_elems_3697_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_set_3698_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3699_: u8 = 0;
    let mut v___x_3701_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3702_: u8 = 0;
    let mut v___x_3703_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3704_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3705_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3707_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3708_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3709_: u8 = 0;
    let mut v_unused_3710_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3711_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_elems_3697_ = leanh::lean_ctor_get(v_s_3695_, 0);
                v_set_3698_ = leanh::lean_ctor_get(v_s_3695_, 1);
                v___x_3699_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Try_Collector_OrdSet_insert___at___00Lean_Meta_Try_Collector_saveLibSearchCandidates_spec__0_spec__0___redArg(v_set_3698_, v_a_3696_);
                if v___x_3699_ == 0 {
                    leanh::lean_inc_ref(v_set_3698_);
                    leanh::lean_inc_ref(v_elems_3697_);
                    v_isSharedCheck_3709_ = (!leanh::lean_is_exclusive(v_s_3695_)) as u8;
                    if v_isSharedCheck_3709_ == 0 {
                        v_unused_3710_ = leanh::lean_ctor_get(v_s_3695_, 1);
                        leanh::lean_dec(v_unused_3710_);
                        v_unused_3711_ = leanh::lean_ctor_get(v_s_3695_, 0);
                        leanh::lean_dec(v_unused_3711_);
                        v___x_3701_ = v_s_3695_;
                        v_isShared_3702_ = v_isSharedCheck_3709_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_dec(v_s_3695_);
                        v___x_3701_ = leanh::lean_box(0);
                        v_isShared_3702_ = v_isSharedCheck_3709_;
                        state = 1;
                        continue;
                    }
                } else {
                    leanh::lean_dec_ref(v_a_3696_);
                    return v_s_3695_;
                }
            }
            1 => {
                leanh::lean_inc_ref(v_a_3696_);
                v___x_3703_ = lean_array_push(v_elems_3697_, v_a_3696_);
                v___x_3704_ = leanh::lean_box(0);
                v___x_3705_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Try_Collector_OrdSet_insert___at___00Lean_Meta_Try_Collector_saveLibSearchCandidates_spec__0_spec__1___redArg(v_set_3698_, v_a_3696_, v___x_3704_);
                if v_isShared_3702_ == 0 {
                    leanh::lean_ctor_set(v___x_3701_, 1, v___x_3705_);
                    leanh::lean_ctor_set(v___x_3701_, 0, v___x_3703_);
                    v___x_3707_ = v___x_3701_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3708_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3708_, 0, v___x_3703_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3708_, 1, v___x_3705_);
                    v___x_3707_ = v_reuseFailAlloc_3708_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3707_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Try_Collector_saveLibSearchCandidates_spec__1___redArg(
    mut v_as_3712_: *mut leanh::LeanObject,
    mut v_sz_3713_: usize,
    mut v_i_3714_: usize,
    mut v_b_3715_: *mut leanh::LeanObject,
    mut v___y_3716_: *mut leanh::LeanObject,
    mut v___y_3717_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_a_3720_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3721_: usize = 0;
    let mut v___x_3722_: usize = 0;
    let mut v___x_3724_: u8 = 0;
    let mut v___x_3725_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3726_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_3727_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3728_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3730_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3731_: u8 = 0;
    let mut v___x_3732_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3733_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3734_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3735_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3737_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3738_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_allConsts_3739_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unfoldCandidates_3740_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_eqnCandidates_3741_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_funIndCandidates_3742_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_indCandidates_3743_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_libSearchResults_3744_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3746_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3747_: u8 = 0;
    let mut v___x_3749_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3750_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3752_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3753_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3754_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3755_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3756_: u8 = 0;
    let mut v___x_3757_: u8 = 0;
    let mut v___x_3758_: u8 = 0;
    let mut v___x_3759_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3760_: u8 = 0;
    let mut v___x_3761_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3762_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3763_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3765_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3766_: u8 = 0;
    let mut v___x_3768_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3769_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3770_: u8 = 0;
    let mut v_isSharedCheck_3771_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3724_ = lean_usize_dec_lt(v_i_3714_, v_sz_3713_);
                if v___x_3724_ == 0 {
                    v___x_3725_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_3725_, 0, v_b_3715_);
                    return v___x_3725_;
                } else {
                    v_a_3726_ = lean_array_uget(v_as_3712_, v_i_3714_);
                    v_fst_3727_ = leanh::lean_ctor_get(v_a_3726_, 0);
                    v_snd_3728_ = leanh::lean_ctor_get(v_a_3726_, 1);
                    v_isSharedCheck_3771_ = (!leanh::lean_is_exclusive(v_a_3726_)) as u8;
                    if v_isSharedCheck_3771_ == 0 {
                        v___x_3730_ = v_a_3726_;
                        v_isShared_3731_ = v_isSharedCheck_3771_;
                        state = 2;
                        continue;
                    } else {
                        leanh::lean_inc(v_snd_3728_);
                        leanh::lean_inc(v_fst_3727_);
                        leanh::lean_dec(v_a_3726_);
                        v___x_3730_ = leanh::lean_box(0);
                        v_isShared_3731_ = v_isSharedCheck_3771_;
                        state = 2;
                        continue;
                    }
                }
            }
            1 => {
                v___x_3721_ = 1usize;
                v___x_3722_ = lean_usize_add(v_i_3714_, v___x_3721_);
                v_i_3714_ = v___x_3722_;
                v_b_3715_ = v_a_3720_;
                state = 0;
                continue;
            }
            2 => {
                v___x_3732_ = l_Lean_Meta_Grind_grindExt;
                leanh::lean_inc(v_fst_3727_);
                v___x_3733_ = l_Lean_Meta_Grind_Extension_isEMatchTheorem___redArg(
                    v___x_3732_,
                    v_fst_3727_,
                    v___y_3717_,
                );
                if leanh::lean_obj_tag(v___x_3733_) == 0 {
                    v_a_3734_ = leanh::lean_ctor_get(v___x_3733_, 0);
                    leanh::lean_inc(v_a_3734_);
                    leanh::lean_dec_ref_known(v___x_3733_, 1);
                    v___x_3735_ = leanh::lean_box(0);
                    v___x_3757_ = (leanh::lean_unbox(v_a_3734_) as u8);
                    if v___x_3757_ == 0 {
                        v___x_3758_ = (leanh::lean_unbox(v_snd_3728_) as u8);
                        leanh::lean_dec(v_snd_3728_);
                        match v___x_3758_ {
                            0 => {
                                v___x_3759_ = leanh::lean_alloc_ctor(8, 0, (1) as u32);
                                v___x_3760_ = (leanh::lean_unbox(v_a_3734_) as u8);
                                leanh::lean_dec(v_a_3734_);
                                leanh::lean_ctor_set_uint8(
                                    v___x_3759_,
                                    0 as u32,
                                    v___x_3760_,
                                );
                                v___y_3737_ = v___x_3759_;
                                state = 3;
                                continue;
                            }
                            1 => {
                                leanh::lean_dec(v_a_3734_);
                                v___x_3761_ = leanh::lean_box(6);
                                v___y_3737_ = v___x_3761_;
                                state = 3;
                                continue;
                            }
                            _ => {
                                leanh::lean_dec(v_a_3734_);
                                v___x_3762_ = leanh::lean_box(7);
                                v___y_3737_ = v___x_3762_;
                                state = 3;
                                continue;
                            }
                        }
                    } else {
                        leanh::lean_dec(v_a_3734_);
                        leanh::lean_del_object(v___x_3730_);
                        leanh::lean_dec(v_snd_3728_);
                        leanh::lean_dec(v_fst_3727_);
                        v_a_3720_ = v___x_3735_;
                        state = 1;
                        continue;
                    }
                } else {
                    leanh::lean_del_object(v___x_3730_);
                    leanh::lean_dec(v_snd_3728_);
                    leanh::lean_dec(v_fst_3727_);
                    v_a_3763_ = leanh::lean_ctor_get(v___x_3733_, 0);
                    v_isSharedCheck_3770_ = (!leanh::lean_is_exclusive(v___x_3733_)) as u8;
                    if v_isSharedCheck_3770_ == 0 {
                        v___x_3765_ = v___x_3733_;
                        v_isShared_3766_ = v_isSharedCheck_3770_;
                        state = 7;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_3763_);
                        leanh::lean_dec(v___x_3733_);
                        v___x_3765_ = leanh::lean_box(0);
                        v_isShared_3766_ = v_isSharedCheck_3770_;
                        state = 7;
                        continue;
                    }
                }
            }
            3 => {
                v___x_3738_ = lean_st_ref_take(v___y_3716_);
                v_allConsts_3739_ = leanh::lean_ctor_get(v___x_3738_, 0);
                v_unfoldCandidates_3740_ = leanh::lean_ctor_get(v___x_3738_, 1);
                v_eqnCandidates_3741_ = leanh::lean_ctor_get(v___x_3738_, 2);
                v_funIndCandidates_3742_ = leanh::lean_ctor_get(v___x_3738_, 3);
                v_indCandidates_3743_ = leanh::lean_ctor_get(v___x_3738_, 4);
                v_libSearchResults_3744_ = leanh::lean_ctor_get(v___x_3738_, 5);
                v_isSharedCheck_3756_ = (!leanh::lean_is_exclusive(v___x_3738_)) as u8;
                if v_isSharedCheck_3756_ == 0 {
                    v___x_3746_ = v___x_3738_;
                    v_isShared_3747_ = v_isSharedCheck_3756_;
                    state = 4;
                    continue;
                } else {
                    leanh::lean_inc(v_libSearchResults_3744_);
                    leanh::lean_inc(v_indCandidates_3743_);
                    leanh::lean_inc(v_funIndCandidates_3742_);
                    leanh::lean_inc(v_eqnCandidates_3741_);
                    leanh::lean_inc(v_unfoldCandidates_3740_);
                    leanh::lean_inc(v_allConsts_3739_);
                    leanh::lean_dec(v___x_3738_);
                    v___x_3746_ = leanh::lean_box(0);
                    v_isShared_3747_ = v_isSharedCheck_3756_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                if v_isShared_3731_ == 0 {
                    leanh::lean_ctor_set(v___x_3730_, 1, v___y_3737_);
                    v___x_3749_ = v___x_3730_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_3755_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3755_, 0, v_fst_3727_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3755_, 1, v___y_3737_);
                    v___x_3749_ = v_reuseFailAlloc_3755_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v___x_3750_ = l_Lean_Meta_Try_Collector_OrdSet_insert___at___00Lean_Meta_Try_Collector_saveLibSearchCandidates_spec__0(v_libSearchResults_3744_, v___x_3749_);
                if v_isShared_3747_ == 0 {
                    leanh::lean_ctor_set(v___x_3746_, 5, v___x_3750_);
                    v___x_3752_ = v___x_3746_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_3754_ = leanh::lean_alloc_ctor(0, 6, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3754_, 0, v_allConsts_3739_);
                    leanh::lean_ctor_set(
                        v_reuseFailAlloc_3754_,
                        1,
                        v_unfoldCandidates_3740_,
                    );
                    leanh::lean_ctor_set(v_reuseFailAlloc_3754_, 2, v_eqnCandidates_3741_);
                    leanh::lean_ctor_set(
                        v_reuseFailAlloc_3754_,
                        3,
                        v_funIndCandidates_3742_,
                    );
                    leanh::lean_ctor_set(v_reuseFailAlloc_3754_, 4, v_indCandidates_3743_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3754_, 5, v___x_3750_);
                    v___x_3752_ = v_reuseFailAlloc_3754_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                v___x_3753_ = lean_st_ref_set(v___y_3716_, v___x_3752_);
                v_a_3720_ = v___x_3735_;
                state = 1;
                continue;
            }
            7 => {
                if v_isShared_3766_ == 0 {
                    v___x_3768_ = v___x_3765_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_3769_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3769_, 0, v_a_3763_);
                    v___x_3768_ = v_reuseFailAlloc_3769_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_3768_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Try_Collector_saveLibSearchCandidates_spec__1___redArg___boxed(
    mut v_as_3772_: *mut leanh::LeanObject,
    mut v_sz_3773_: *mut leanh::LeanObject,
    mut v_i_3774_: *mut leanh::LeanObject,
    mut v_b_3775_: *mut leanh::LeanObject,
    mut v___y_3776_: *mut leanh::LeanObject,
    mut v___y_3777_: *mut leanh::LeanObject,
    mut v___y_3778_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_sz_boxed_3779_: usize = 0;
    let mut v_i_boxed_3780_: usize = 0;
    let mut v_res_3781_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_3779_ = leanh::lean_unbox_usize(v_sz_3773_);
    leanh::lean_dec(v_sz_3773_);
    v_i_boxed_3780_ = leanh::lean_unbox_usize(v_i_3774_);
    leanh::lean_dec(v_i_3774_);
    v_res_3781_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Try_Collector_saveLibSearchCandidates_spec__1___redArg(v_as_3772_, v_sz_boxed_3779_, v_i_boxed_3780_, v_b_3775_, v___y_3776_, v___y_3777_);
    leanh::lean_dec(v___y_3777_);
    leanh::lean_dec(v___y_3776_);
    leanh::lean_dec_ref(v_as_3772_);
    return v_res_3781_;
}
pub unsafe fn l_Lean_Meta_Try_Collector_saveLibSearchCandidates(
    mut v_e_3782_: *mut leanh::LeanObject,
    mut v_a_3783_: *mut leanh::LeanObject,
    mut v_a_3784_: *mut leanh::LeanObject,
    mut v_a_3785_: *mut leanh::LeanObject,
    mut v_a_3786_: *mut leanh::LeanObject,
    mut v_a_3787_: *mut leanh::LeanObject,
    mut v_a_3788_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_harder_3790_: u8 = 0;
    let mut v___x_3791_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3792_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3793_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3794_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3795_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_3796_: usize = 0;
    let mut v___x_3797_: usize = 0;
    let mut v___x_3798_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3800_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3801_: u8 = 0;
    let mut v___x_3803_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3804_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3805_: u8 = 0;
    let mut v_unused_3806_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3807_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3809_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3810_: u8 = 0;
    let mut v___x_3812_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3813_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3814_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_harder_3790_ = leanh::lean_ctor_get_uint8(
                    v_a_3783_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 1 + 5) as u32,
                );
                if v_harder_3790_ == 0 {
                    leanh::lean_dec_ref(v_e_3782_);
                    v___x_3791_ = leanh::lean_box(0);
                    v___x_3792_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_3792_, 0, v___x_3791_);
                    return v___x_3792_;
                } else {
                    v___x_3793_ = l_Lean_Meta_LibrarySearch_libSearchFindDecls(
                        v_e_3782_, v_a_3785_, v_a_3786_, v_a_3787_, v_a_3788_,
                    );
                    if leanh::lean_obj_tag(v___x_3793_) == 0 {
                        v_a_3794_ = leanh::lean_ctor_get(v___x_3793_, 0);
                        leanh::lean_inc(v_a_3794_);
                        leanh::lean_dec_ref_known(v___x_3793_, 1);
                        v___x_3795_ = leanh::lean_box(0);
                        v_sz_3796_ = lean_array_size(v_a_3794_);
                        v___x_3797_ = 0usize;
                        v___x_3798_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Try_Collector_saveLibSearchCandidates_spec__1___redArg(v_a_3794_, v_sz_3796_, v___x_3797_, v___x_3795_, v_a_3784_, v_a_3788_);
                        leanh::lean_dec(v_a_3794_);
                        if leanh::lean_obj_tag(v___x_3798_) == 0 {
                            v_isSharedCheck_3805_ =
                                (!leanh::lean_is_exclusive(v___x_3798_)) as u8;
                            if v_isSharedCheck_3805_ == 0 {
                                v_unused_3806_ = leanh::lean_ctor_get(v___x_3798_, 0);
                                leanh::lean_dec(v_unused_3806_);
                                v___x_3800_ = v___x_3798_;
                                v_isShared_3801_ = v_isSharedCheck_3805_;
                                state = 1;
                                continue;
                            } else {
                                leanh::lean_dec(v___x_3798_);
                                v___x_3800_ = leanh::lean_box(0);
                                v_isShared_3801_ = v_isSharedCheck_3805_;
                                state = 1;
                                continue;
                            }
                        } else {
                            return v___x_3798_;
                        }
                    } else {
                        v_a_3807_ = leanh::lean_ctor_get(v___x_3793_, 0);
                        v_isSharedCheck_3814_ =
                            (!leanh::lean_is_exclusive(v___x_3793_)) as u8;
                        if v_isSharedCheck_3814_ == 0 {
                            v___x_3809_ = v___x_3793_;
                            v_isShared_3810_ = v_isSharedCheck_3814_;
                            state = 3;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_3807_);
                            leanh::lean_dec(v___x_3793_);
                            v___x_3809_ = leanh::lean_box(0);
                            v_isShared_3810_ = v_isSharedCheck_3814_;
                            state = 3;
                            continue;
                        }
                    }
                }
            }
            1 => {
                if v_isShared_3801_ == 0 {
                    leanh::lean_ctor_set(v___x_3800_, 0, v___x_3795_);
                    v___x_3803_ = v___x_3800_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3804_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3804_, 0, v___x_3795_);
                    v___x_3803_ = v_reuseFailAlloc_3804_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3803_;
            }
            3 => {
                if v_isShared_3810_ == 0 {
                    v___x_3812_ = v___x_3809_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3813_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3813_, 0, v_a_3807_);
                    v___x_3812_ = v_reuseFailAlloc_3813_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_3812_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Try_Collector_saveLibSearchCandidates___boxed(
    mut v_e_3815_: *mut leanh::LeanObject,
    mut v_a_3816_: *mut leanh::LeanObject,
    mut v_a_3817_: *mut leanh::LeanObject,
    mut v_a_3818_: *mut leanh::LeanObject,
    mut v_a_3819_: *mut leanh::LeanObject,
    mut v_a_3820_: *mut leanh::LeanObject,
    mut v_a_3821_: *mut leanh::LeanObject,
    mut v_a_3822_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3823_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3823_ = l_Lean_Meta_Try_Collector_saveLibSearchCandidates(
        v_e_3815_, v_a_3816_, v_a_3817_, v_a_3818_, v_a_3819_, v_a_3820_, v_a_3821_,
    );
    leanh::lean_dec(v_a_3821_);
    leanh::lean_dec_ref(v_a_3820_);
    leanh::lean_dec(v_a_3819_);
    leanh::lean_dec_ref(v_a_3818_);
    leanh::lean_dec(v_a_3817_);
    leanh::lean_dec_ref(v_a_3816_);
    return v_res_3823_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Try_Collector_saveLibSearchCandidates_spec__1(
    mut v_as_3824_: *mut leanh::LeanObject,
    mut v_sz_3825_: usize,
    mut v_i_3826_: usize,
    mut v_b_3827_: *mut leanh::LeanObject,
    mut v___y_3828_: *mut leanh::LeanObject,
    mut v___y_3829_: *mut leanh::LeanObject,
    mut v___y_3830_: *mut leanh::LeanObject,
    mut v___y_3831_: *mut leanh::LeanObject,
    mut v___y_3832_: *mut leanh::LeanObject,
    mut v___y_3833_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3835_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3835_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Try_Collector_saveLibSearchCandidates_spec__1___redArg(v_as_3824_, v_sz_3825_, v_i_3826_, v_b_3827_, v___y_3829_, v___y_3833_);
    return v___x_3835_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Try_Collector_saveLibSearchCandidates_spec__1___boxed(
    mut v_as_3836_: *mut leanh::LeanObject,
    mut v_sz_3837_: *mut leanh::LeanObject,
    mut v_i_3838_: *mut leanh::LeanObject,
    mut v_b_3839_: *mut leanh::LeanObject,
    mut v___y_3840_: *mut leanh::LeanObject,
    mut v___y_3841_: *mut leanh::LeanObject,
    mut v___y_3842_: *mut leanh::LeanObject,
    mut v___y_3843_: *mut leanh::LeanObject,
    mut v___y_3844_: *mut leanh::LeanObject,
    mut v___y_3845_: *mut leanh::LeanObject,
    mut v___y_3846_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_sz_boxed_3847_: usize = 0;
    let mut v_i_boxed_3848_: usize = 0;
    let mut v_res_3849_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_3847_ = leanh::lean_unbox_usize(v_sz_3837_);
    leanh::lean_dec(v_sz_3837_);
    v_i_boxed_3848_ = leanh::lean_unbox_usize(v_i_3838_);
    leanh::lean_dec(v_i_3838_);
    v_res_3849_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Try_Collector_saveLibSearchCandidates_spec__1(v_as_3836_, v_sz_boxed_3847_, v_i_boxed_3848_, v_b_3839_, v___y_3840_, v___y_3841_, v___y_3842_, v___y_3843_, v___y_3844_, v___y_3845_);
    leanh::lean_dec(v___y_3845_);
    leanh::lean_dec_ref(v___y_3844_);
    leanh::lean_dec(v___y_3843_);
    leanh::lean_dec_ref(v___y_3842_);
    leanh::lean_dec(v___y_3841_);
    leanh::lean_dec_ref(v___y_3840_);
    leanh::lean_dec_ref(v_as_3836_);
    return v_res_3849_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Try_Collector_OrdSet_insert___at___00Lean_Meta_Try_Collector_saveLibSearchCandidates_spec__0_spec__0(
    mut v_00_u03b2_3850_: *mut leanh::LeanObject,
    mut v_m_3851_: *mut leanh::LeanObject,
    mut v_a_3852_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_3853_: u8 = 0;
    v___x_3853_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Try_Collector_OrdSet_insert___at___00Lean_Meta_Try_Collector_saveLibSearchCandidates_spec__0_spec__0___redArg(v_m_3851_, v_a_3852_);
    return v___x_3853_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Try_Collector_OrdSet_insert___at___00Lean_Meta_Try_Collector_saveLibSearchCandidates_spec__0_spec__0___boxed(
    mut v_00_u03b2_3854_: *mut leanh::LeanObject,
    mut v_m_3855_: *mut leanh::LeanObject,
    mut v_a_3856_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3857_: u8 = 0;
    let mut v_r_3858_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3857_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Try_Collector_OrdSet_insert___at___00Lean_Meta_Try_Collector_saveLibSearchCandidates_spec__0_spec__0(v_00_u03b2_3854_, v_m_3855_, v_a_3856_);
    leanh::lean_dec_ref(v_a_3856_);
    leanh::lean_dec_ref(v_m_3855_);
    v_r_3858_ = leanh::lean_box((v_res_3857_) as usize);
    return v_r_3858_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Try_Collector_OrdSet_insert___at___00Lean_Meta_Try_Collector_saveLibSearchCandidates_spec__0_spec__1(
    mut v_00_u03b2_3859_: *mut leanh::LeanObject,
    mut v_m_3860_: *mut leanh::LeanObject,
    mut v_a_3861_: *mut leanh::LeanObject,
    mut v_b_3862_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3863_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3863_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Try_Collector_OrdSet_insert___at___00Lean_Meta_Try_Collector_saveLibSearchCandidates_spec__0_spec__1___redArg(v_m_3860_, v_a_3861_, v_b_3862_);
    return v___x_3863_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Try_Collector_OrdSet_insert___at___00Lean_Meta_Try_Collector_saveLibSearchCandidates_spec__0_spec__0_spec__1(
    mut v_00_u03b2_3864_: *mut leanh::LeanObject,
    mut v_a_3865_: *mut leanh::LeanObject,
    mut v_x_3866_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_3867_: u8 = 0;
    v___x_3867_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Try_Collector_OrdSet_insert___at___00Lean_Meta_Try_Collector_saveLibSearchCandidates_spec__0_spec__0_spec__1___redArg(v_a_3865_, v_x_3866_);
    return v___x_3867_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Try_Collector_OrdSet_insert___at___00Lean_Meta_Try_Collector_saveLibSearchCandidates_spec__0_spec__0_spec__1___boxed(
    mut v_00_u03b2_3868_: *mut leanh::LeanObject,
    mut v_a_3869_: *mut leanh::LeanObject,
    mut v_x_3870_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3871_: u8 = 0;
    let mut v_r_3872_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3871_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Try_Collector_OrdSet_insert___at___00Lean_Meta_Try_Collector_saveLibSearchCandidates_spec__0_spec__0_spec__1(v_00_u03b2_3868_, v_a_3869_, v_x_3870_);
    leanh::lean_dec(v_x_3870_);
    leanh::lean_dec_ref(v_a_3869_);
    v_r_3872_ = leanh::lean_box((v_res_3871_) as usize);
    return v_r_3872_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Try_Collector_OrdSet_insert___at___00Lean_Meta_Try_Collector_saveLibSearchCandidates_spec__0_spec__1_spec__3(
    mut v_00_u03b2_3873_: *mut leanh::LeanObject,
    mut v_data_3874_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3875_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3875_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Try_Collector_OrdSet_insert___at___00Lean_Meta_Try_Collector_saveLibSearchCandidates_spec__0_spec__1_spec__3___redArg(v_data_3874_);
    return v___x_3875_;
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Try_Collector_OrdSet_insert___at___00Lean_Meta_Try_Collector_saveLibSearchCandidates_spec__0_spec__1_spec__3_spec__5(
    mut v_00_u03b2_3876_: *mut leanh::LeanObject,
    mut v_i_3877_: *mut leanh::LeanObject,
    mut v_source_3878_: *mut leanh::LeanObject,
    mut v_target_3879_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3880_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3880_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Try_Collector_OrdSet_insert___at___00Lean_Meta_Try_Collector_saveLibSearchCandidates_spec__0_spec__1_spec__3_spec__5___redArg(v_i_3877_, v_source_3878_, v_target_3879_);
    return v___x_3880_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Try_Collector_OrdSet_insert___at___00Lean_Meta_Try_Collector_saveLibSearchCandidates_spec__0_spec__1_spec__3_spec__5_spec__6(
    mut v_00_u03b2_3881_: *mut leanh::LeanObject,
    mut v_x_3882_: *mut leanh::LeanObject,
    mut v_x_3883_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3884_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3884_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Try_Collector_OrdSet_insert___at___00Lean_Meta_Try_Collector_saveLibSearchCandidates_spec__0_spec__1_spec__3_spec__5_spec__6___redArg(v_x_3882_, v_x_3883_);
    return v___x_3884_;
}
pub unsafe fn l_Lean_Meta_Try_Collector_visitApp(
    mut v_e_3885_: *mut leanh::LeanObject,
    mut v_declName_3886_: *mut leanh::LeanObject,
    mut v_args_3887_: *mut leanh::LeanObject,
    mut v_a_3888_: *mut leanh::LeanObject,
    mut v_a_3889_: *mut leanh::LeanObject,
    mut v_a_3890_: *mut leanh::LeanObject,
    mut v_a_3891_: *mut leanh::LeanObject,
    mut v_a_3892_: *mut leanh::LeanObject,
    mut v_a_3893_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3895_: *mut leanh::LeanObject = core::ptr::null_mut();
    leanh::lean_inc(v_declName_3886_);
    v___x_3895_ = l_Lean_Meta_Try_Collector_saveEqnCandidate(
        v_declName_3886_,
        v_a_3888_,
        v_a_3889_,
        v_a_3890_,
        v_a_3891_,
        v_a_3892_,
        v_a_3893_,
    );
    if leanh::lean_obj_tag(v___x_3895_) == 0 {
        let mut v___x_3896_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec_ref_known(v___x_3895_, 1);
        leanh::lean_inc(v_declName_3886_);
        leanh::lean_inc_ref(v_e_3885_);
        v___x_3896_ = l_Lean_Meta_Try_Collector_saveFunInd(
            v_e_3885_,
            v_declName_3886_,
            v_args_3887_,
            v_a_3888_,
            v_a_3889_,
            v_a_3890_,
            v_a_3891_,
            v_a_3892_,
            v_a_3893_,
        );
        if leanh::lean_obj_tag(v___x_3896_) == 0 {
            let mut v___x_3897_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec_ref_known(v___x_3896_, 1);
            v___x_3897_ = l_Lean_Meta_Try_Collector_saveUnfoldCandidate___redArg(
                v_declName_3886_,
                v_a_3888_,
                v_a_3889_,
                v_a_3892_,
                v_a_3893_,
            );
            if leanh::lean_obj_tag(v___x_3897_) == 0 {
                let mut v___x_3898_: *mut leanh::LeanObject = core::ptr::null_mut();
                leanh::lean_dec_ref_known(v___x_3897_, 1);
                v___x_3898_ = l_Lean_Meta_Try_Collector_saveLibSearchCandidates(
                    v_e_3885_, v_a_3888_, v_a_3889_, v_a_3890_, v_a_3891_, v_a_3892_, v_a_3893_,
                );
                return v___x_3898_;
            } else {
                leanh::lean_dec_ref(v_e_3885_);
                return v___x_3897_;
            }
        } else {
            leanh::lean_dec(v_declName_3886_);
            leanh::lean_dec_ref(v_e_3885_);
            return v___x_3896_;
        }
    } else {
        leanh::lean_dec(v_declName_3886_);
        leanh::lean_dec_ref(v_e_3885_);
        return v___x_3895_;
    }
}
pub unsafe fn l_Lean_Meta_Try_Collector_visitApp___boxed(
    mut v_e_3899_: *mut leanh::LeanObject,
    mut v_declName_3900_: *mut leanh::LeanObject,
    mut v_args_3901_: *mut leanh::LeanObject,
    mut v_a_3902_: *mut leanh::LeanObject,
    mut v_a_3903_: *mut leanh::LeanObject,
    mut v_a_3904_: *mut leanh::LeanObject,
    mut v_a_3905_: *mut leanh::LeanObject,
    mut v_a_3906_: *mut leanh::LeanObject,
    mut v_a_3907_: *mut leanh::LeanObject,
    mut v_a_3908_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3909_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3909_ = l_Lean_Meta_Try_Collector_visitApp(
        v_e_3899_,
        v_declName_3900_,
        v_args_3901_,
        v_a_3902_,
        v_a_3903_,
        v_a_3904_,
        v_a_3905_,
        v_a_3906_,
        v_a_3907_,
    );
    leanh::lean_dec(v_a_3907_);
    leanh::lean_dec_ref(v_a_3906_);
    leanh::lean_dec(v_a_3905_);
    leanh::lean_dec_ref(v_a_3904_);
    leanh::lean_dec(v_a_3903_);
    leanh::lean_dec_ref(v_a_3902_);
    leanh::lean_dec_ref(v_args_3901_);
    return v_res_3909_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Try_Collector_checkInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__0()
-> *mut leanh::LeanObject {
    let mut v___x_3910_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3910_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(
        leanh::lean_box(0),
        leanh::lean_box(0),
    );
    return v___x_3910_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Try_Collector_checkInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_3911_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3912_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3911_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Try_Collector_checkInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Try_Collector_checkInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__0_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Try_Collector_checkInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__0);
    v___x_3912_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_3912_, 0, v___x_3911_);
    return v___x_3912_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Try_Collector_checkInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__2()
-> *mut leanh::LeanObject {
    let mut v___x_3913_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3914_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3915_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3913_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Try_Collector_checkInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Try_Collector_checkInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__1_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Try_Collector_checkInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__1);
    v___x_3914_ = leanh::lean_unsigned_to_nat(0);
    v___x_3915_ = leanh::lean_alloc_ctor(0, 10, (0) as u32);
    leanh::lean_ctor_set(v___x_3915_, 0, v___x_3914_);
    leanh::lean_ctor_set(v___x_3915_, 1, v___x_3914_);
    leanh::lean_ctor_set(v___x_3915_, 2, v___x_3914_);
    leanh::lean_ctor_set(v___x_3915_, 3, v___x_3914_);
    leanh::lean_ctor_set(v___x_3915_, 4, v___x_3913_);
    leanh::lean_ctor_set(v___x_3915_, 5, v___x_3913_);
    leanh::lean_ctor_set(v___x_3915_, 6, v___x_3913_);
    leanh::lean_ctor_set(v___x_3915_, 7, v___x_3913_);
    leanh::lean_ctor_set(v___x_3915_, 8, v___x_3913_);
    leanh::lean_ctor_set(v___x_3915_, 9, v___x_3913_);
    return v___x_3915_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Try_Collector_checkInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__3()
-> *mut leanh::LeanObject {
    let mut v___x_3916_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3917_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3918_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3916_ = leanh::lean_unsigned_to_nat(32);
    v___x_3917_ = lean_mk_empty_array_with_capacity(v___x_3916_);
    v___x_3918_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_3918_, 0, v___x_3917_);
    return v___x_3918_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Try_Collector_checkInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__4()
-> *mut leanh::LeanObject {
    let mut v___x_3919_: usize = 0;
    let mut v___x_3920_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3921_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3922_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3923_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3924_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3919_ = 5usize;
    v___x_3920_ = leanh::lean_unsigned_to_nat(0);
    v___x_3921_ = leanh::lean_unsigned_to_nat(32);
    v___x_3922_ = lean_mk_empty_array_with_capacity(v___x_3921_);
    v___x_3923_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Try_Collector_checkInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__3), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Try_Collector_checkInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__3_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Try_Collector_checkInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__3);
    v___x_3924_ = leanh::lean_alloc_ctor(0, 4, (core::mem::size_of::<usize>() * 1) as u32);
    leanh::lean_ctor_set(v___x_3924_, 0, v___x_3923_);
    leanh::lean_ctor_set(v___x_3924_, 1, v___x_3922_);
    leanh::lean_ctor_set(v___x_3924_, 2, v___x_3920_);
    leanh::lean_ctor_set(v___x_3924_, 3, v___x_3920_);
    leanh::lean_ctor_set_usize(v___x_3924_, 4, v___x_3919_);
    return v___x_3924_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Try_Collector_checkInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__5()
-> *mut leanh::LeanObject {
    let mut v___x_3925_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3926_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3927_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3928_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3925_ = leanh::lean_box(1);
    v___x_3926_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Try_Collector_checkInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__4), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Try_Collector_checkInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__4_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Try_Collector_checkInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__4);
    v___x_3927_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Try_Collector_checkInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Try_Collector_checkInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__1_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Try_Collector_checkInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__1);
    v___x_3928_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_3928_, 0, v___x_3927_);
    leanh::lean_ctor_set(v___x_3928_, 1, v___x_3926_);
    leanh::lean_ctor_set(v___x_3928_, 2, v___x_3925_);
    return v___x_3928_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Try_Collector_checkInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__7()
-> *mut leanh::LeanObject {
    let mut v___x_3930_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3931_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3930_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Try_Collector_checkInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__6;
    v___x_3931_ = l_Lean_stringToMessageData(v___x_3930_);
    return v___x_3931_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Try_Collector_checkInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__9()
-> *mut leanh::LeanObject {
    let mut v___x_3933_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3934_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3933_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Try_Collector_checkInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__8;
    v___x_3934_ = l_Lean_stringToMessageData(v___x_3933_);
    return v___x_3934_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Try_Collector_checkInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__11()
-> *mut leanh::LeanObject {
    let mut v___x_3936_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3937_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3936_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Try_Collector_checkInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__10;
    v___x_3937_ = l_Lean_stringToMessageData(v___x_3936_);
    return v___x_3937_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Try_Collector_checkInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__13()
-> *mut leanh::LeanObject {
    let mut v___x_3939_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3940_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3939_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Try_Collector_checkInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__12;
    v___x_3940_ = l_Lean_stringToMessageData(v___x_3939_);
    return v___x_3940_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Try_Collector_checkInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__15()
-> *mut leanh::LeanObject {
    let mut v___x_3942_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3943_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3942_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Try_Collector_checkInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__14;
    v___x_3943_ = l_Lean_stringToMessageData(v___x_3942_);
    return v___x_3943_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Try_Collector_checkInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__17()
-> *mut leanh::LeanObject {
    let mut v___x_3945_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3946_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3945_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Try_Collector_checkInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__16;
    v___x_3946_ = l_Lean_stringToMessageData(v___x_3945_);
    return v___x_3946_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Try_Collector_checkInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__19()
-> *mut leanh::LeanObject {
    let mut v___x_3948_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3949_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3948_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Try_Collector_checkInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__18;
    v___x_3949_ = l_Lean_stringToMessageData(v___x_3948_);
    return v___x_3949_;
}
pub unsafe fn l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Try_Collector_checkInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg(
    mut v_msg_3950_: *mut leanh::LeanObject,
    mut v_declHint_3951_: *mut leanh::LeanObject,
    mut v___y_3952_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3954_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_3955_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3956_: u8 = 0;
    let mut v_isExporting_3957_: u8 = 0;
    let mut v___x_3958_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3959_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3960_: u8 = 0;
    let mut v___x_3961_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3962_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3963_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3964_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3965_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3966_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_c_3967_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3968_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3969_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3970_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3971_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3972_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3973_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3974_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3975_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3976_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3978_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3979_: u8 = 0;
    let mut v___x_3980_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3981_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3982_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_mod_3983_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3984_: u8 = 0;
    let mut v___x_3985_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3986_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3987_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3988_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3989_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3990_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3991_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3992_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3993_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3994_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3996_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3997_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3998_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3999_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4000_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4001_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4002_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4003_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4004_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4005_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4006_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4007_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4009_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4010_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4011_: u8 = 0;
    let mut v___x_4012_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3954_ = lean_st_ref_get(v___y_3952_);
                v_env_3955_ = leanh::lean_ctor_get(v___x_3954_, 0);
                leanh::lean_inc_ref(v_env_3955_);
                leanh::lean_dec(v___x_3954_);
                v___x_3956_ = l_Lean_Name_isAnonymous(v_declHint_3951_);
                if v___x_3956_ == 0 {
                    v_isExporting_3957_ = leanh::lean_ctor_get_uint8(
                        v_env_3955_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 8) as u32,
                    );
                    if v_isExporting_3957_ == 0 {
                        leanh::lean_dec_ref(v_env_3955_);
                        leanh::lean_dec(v_declHint_3951_);
                        v___x_3958_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v___x_3958_, 0, v_msg_3950_);
                        return v___x_3958_;
                    } else {
                        leanh::lean_inc_ref(v_env_3955_);
                        v___x_3959_ = l_Lean_Environment_setExporting(v_env_3955_, v___x_3956_);
                        leanh::lean_inc(v_declHint_3951_);
                        leanh::lean_inc_ref(v___x_3959_);
                        v___x_3960_ = l_Lean_Environment_contains(
                            v___x_3959_,
                            v_declHint_3951_,
                            v_isExporting_3957_,
                        );
                        if v___x_3960_ == 0 {
                            leanh::lean_dec_ref(v___x_3959_);
                            leanh::lean_dec_ref(v_env_3955_);
                            leanh::lean_dec(v_declHint_3951_);
                            v___x_3961_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                            leanh::lean_ctor_set(v___x_3961_, 0, v_msg_3950_);
                            return v___x_3961_;
                        } else {
                            v___x_3962_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Try_Collector_checkInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__2), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Try_Collector_checkInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__2_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Try_Collector_checkInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__2);
                            v___x_3963_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Try_Collector_checkInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__5), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Try_Collector_checkInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__5_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Try_Collector_checkInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__5);
                            v___x_3964_ = l_Lean_Options_empty;
                            v___x_3965_ = leanh::lean_alloc_ctor(0, 4, (0) as u32);
                            leanh::lean_ctor_set(v___x_3965_, 0, v___x_3959_);
                            leanh::lean_ctor_set(v___x_3965_, 1, v___x_3962_);
                            leanh::lean_ctor_set(v___x_3965_, 2, v___x_3963_);
                            leanh::lean_ctor_set(v___x_3965_, 3, v___x_3964_);
                            leanh::lean_inc(v_declHint_3951_);
                            v___x_3966_ =
                                l_Lean_MessageData_ofConstName(v_declHint_3951_, v___x_3956_);
                            v_c_3967_ = leanh::lean_alloc_ctor(3, 2, (0) as u32);
                            leanh::lean_ctor_set(v_c_3967_, 0, v___x_3965_);
                            leanh::lean_ctor_set(v_c_3967_, 1, v___x_3966_);
                            v___x_3968_ = l_Lean_Environment_getModuleIdxFor_x3f(
                                v_env_3955_,
                                v_declHint_3951_,
                            );
                            if leanh::lean_obj_tag(v___x_3968_) == 0 {
                                leanh::lean_dec_ref(v_env_3955_);
                                leanh::lean_dec(v_declHint_3951_);
                                v___x_3969_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Try_Collector_checkInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__7), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Try_Collector_checkInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__7_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Try_Collector_checkInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__7);
                                v___x_3970_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                                leanh::lean_ctor_set(v___x_3970_, 0, v___x_3969_);
                                leanh::lean_ctor_set(v___x_3970_, 1, v_c_3967_);
                                v___x_3971_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Try_Collector_checkInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__9), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Try_Collector_checkInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__9_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Try_Collector_checkInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__9);
                                v___x_3972_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                                leanh::lean_ctor_set(v___x_3972_, 0, v___x_3970_);
                                leanh::lean_ctor_set(v___x_3972_, 1, v___x_3971_);
                                v___x_3973_ = l_Lean_MessageData_note(v___x_3972_);
                                v___x_3974_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                                leanh::lean_ctor_set(v___x_3974_, 0, v_msg_3950_);
                                leanh::lean_ctor_set(v___x_3974_, 1, v___x_3973_);
                                v___x_3975_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                                leanh::lean_ctor_set(v___x_3975_, 0, v___x_3974_);
                                return v___x_3975_;
                            } else {
                                v_val_3976_ = leanh::lean_ctor_get(v___x_3968_, 0);
                                v_isSharedCheck_4011_ =
                                    (!leanh::lean_is_exclusive(v___x_3968_)) as u8;
                                if v_isSharedCheck_4011_ == 0 {
                                    v___x_3978_ = v___x_3968_;
                                    v_isShared_3979_ = v_isSharedCheck_4011_;
                                    state = 1;
                                    continue;
                                } else {
                                    leanh::lean_inc(v_val_3976_);
                                    leanh::lean_dec(v___x_3968_);
                                    v___x_3978_ = leanh::lean_box(0);
                                    v_isShared_3979_ = v_isSharedCheck_4011_;
                                    state = 1;
                                    continue;
                                }
                            }
                        }
                    }
                } else {
                    leanh::lean_dec_ref(v_env_3955_);
                    leanh::lean_dec(v_declHint_3951_);
                    v___x_4012_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_4012_, 0, v_msg_3950_);
                    return v___x_4012_;
                }
            }
            1 => {
                v___x_3980_ = leanh::lean_box(0);
                v___x_3981_ = l_Lean_Environment_header(v_env_3955_);
                leanh::lean_dec_ref(v_env_3955_);
                v___x_3982_ = l_Lean_EnvironmentHeader_moduleNames(v___x_3981_);
                v_mod_3983_ = lean_array_get(v___x_3980_, v___x_3982_, v_val_3976_);
                leanh::lean_dec(v_val_3976_);
                leanh::lean_dec_ref(v___x_3982_);
                v___x_3984_ = l_Lean_isPrivateName(v_declHint_3951_);
                leanh::lean_dec(v_declHint_3951_);
                if v___x_3984_ == 0 {
                    v___x_3985_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Try_Collector_checkInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__11), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Try_Collector_checkInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__11_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Try_Collector_checkInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__11);
                    v___x_3986_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_3986_, 0, v___x_3985_);
                    leanh::lean_ctor_set(v___x_3986_, 1, v_c_3967_);
                    v___x_3987_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Try_Collector_checkInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__13), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Try_Collector_checkInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__13_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Try_Collector_checkInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__13);
                    v___x_3988_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_3988_, 0, v___x_3986_);
                    leanh::lean_ctor_set(v___x_3988_, 1, v___x_3987_);
                    v___x_3989_ = l_Lean_MessageData_ofName(v_mod_3983_);
                    v___x_3990_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_3990_, 0, v___x_3988_);
                    leanh::lean_ctor_set(v___x_3990_, 1, v___x_3989_);
                    v___x_3991_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Try_Collector_checkInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__15), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Try_Collector_checkInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__15_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Try_Collector_checkInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__15);
                    v___x_3992_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_3992_, 0, v___x_3990_);
                    leanh::lean_ctor_set(v___x_3992_, 1, v___x_3991_);
                    v___x_3993_ = l_Lean_MessageData_note(v___x_3992_);
                    v___x_3994_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_3994_, 0, v_msg_3950_);
                    leanh::lean_ctor_set(v___x_3994_, 1, v___x_3993_);
                    if v_isShared_3979_ == 0 {
                        leanh::lean_ctor_set_tag(v___x_3978_, 0);
                        leanh::lean_ctor_set(v___x_3978_, 0, v___x_3994_);
                        v___x_3996_ = v___x_3978_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_3997_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_3997_, 0, v___x_3994_);
                        v___x_3996_ = v_reuseFailAlloc_3997_;
                        state = 2;
                        continue;
                    }
                } else {
                    v___x_3998_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Try_Collector_checkInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__7), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Try_Collector_checkInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__7_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Try_Collector_checkInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__7);
                    v___x_3999_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_3999_, 0, v___x_3998_);
                    leanh::lean_ctor_set(v___x_3999_, 1, v_c_3967_);
                    v___x_4000_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Try_Collector_checkInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__17), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Try_Collector_checkInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__17_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Try_Collector_checkInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__17);
                    v___x_4001_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_4001_, 0, v___x_3999_);
                    leanh::lean_ctor_set(v___x_4001_, 1, v___x_4000_);
                    v___x_4002_ = l_Lean_MessageData_ofName(v_mod_3983_);
                    v___x_4003_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_4003_, 0, v___x_4001_);
                    leanh::lean_ctor_set(v___x_4003_, 1, v___x_4002_);
                    v___x_4004_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Try_Collector_checkInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__19), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Try_Collector_checkInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__19_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Try_Collector_checkInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__19);
                    v___x_4005_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_4005_, 0, v___x_4003_);
                    leanh::lean_ctor_set(v___x_4005_, 1, v___x_4004_);
                    v___x_4006_ = l_Lean_MessageData_note(v___x_4005_);
                    v___x_4007_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_4007_, 0, v_msg_3950_);
                    leanh::lean_ctor_set(v___x_4007_, 1, v___x_4006_);
                    if v_isShared_3979_ == 0 {
                        leanh::lean_ctor_set_tag(v___x_3978_, 0);
                        leanh::lean_ctor_set(v___x_3978_, 0, v___x_4007_);
                        v___x_4009_ = v___x_3978_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_4010_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_4010_, 0, v___x_4007_);
                        v___x_4009_ = v_reuseFailAlloc_4010_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_3996_;
            }
            3 => {
                return v___x_4009_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Try_Collector_checkInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___boxed(
    mut v_msg_4013_: *mut leanh::LeanObject,
    mut v_declHint_4014_: *mut leanh::LeanObject,
    mut v___y_4015_: *mut leanh::LeanObject,
    mut v___y_4016_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4017_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4017_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Try_Collector_checkInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg(v_msg_4013_, v_declHint_4014_, v___y_4015_);
    leanh::lean_dec(v___y_4015_);
    return v_res_4017_;
}
pub unsafe fn l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Try_Collector_checkInductive_spec__0_spec__0_spec__1_spec__2_spec__3(
    mut v_msg_4018_: *mut leanh::LeanObject,
    mut v_declHint_4019_: *mut leanh::LeanObject,
    mut v___y_4020_: *mut leanh::LeanObject,
    mut v___y_4021_: *mut leanh::LeanObject,
    mut v___y_4022_: *mut leanh::LeanObject,
    mut v___y_4023_: *mut leanh::LeanObject,
    mut v___y_4024_: *mut leanh::LeanObject,
    mut v___y_4025_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4027_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4028_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4030_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4031_: u8 = 0;
    let mut v___x_4032_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4033_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4035_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4036_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4037_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4027_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Try_Collector_checkInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg(v_msg_4018_, v_declHint_4019_, v___y_4025_);
                v_a_4028_ = leanh::lean_ctor_get(v___x_4027_, 0);
                v_isSharedCheck_4037_ = (!leanh::lean_is_exclusive(v___x_4027_)) as u8;
                if v_isSharedCheck_4037_ == 0 {
                    v___x_4030_ = v___x_4027_;
                    v_isShared_4031_ = v_isSharedCheck_4037_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_a_4028_);
                    leanh::lean_dec(v___x_4027_);
                    v___x_4030_ = leanh::lean_box(0);
                    v_isShared_4031_ = v_isSharedCheck_4037_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_4032_ = l_Lean_unknownIdentifierMessageTag;
                v___x_4033_ = leanh::lean_alloc_ctor(8, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_4033_, 0, v___x_4032_);
                leanh::lean_ctor_set(v___x_4033_, 1, v_a_4028_);
                if v_isShared_4031_ == 0 {
                    leanh::lean_ctor_set(v___x_4030_, 0, v___x_4033_);
                    v___x_4035_ = v___x_4030_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4036_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4036_, 0, v___x_4033_);
                    v___x_4035_ = v_reuseFailAlloc_4036_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_4035_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Try_Collector_checkInductive_spec__0_spec__0_spec__1_spec__2_spec__3___boxed(
    mut v_msg_4038_: *mut leanh::LeanObject,
    mut v_declHint_4039_: *mut leanh::LeanObject,
    mut v___y_4040_: *mut leanh::LeanObject,
    mut v___y_4041_: *mut leanh::LeanObject,
    mut v___y_4042_: *mut leanh::LeanObject,
    mut v___y_4043_: *mut leanh::LeanObject,
    mut v___y_4044_: *mut leanh::LeanObject,
    mut v___y_4045_: *mut leanh::LeanObject,
    mut v___y_4046_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4047_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4047_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Try_Collector_checkInductive_spec__0_spec__0_spec__1_spec__2_spec__3(v_msg_4038_, v_declHint_4039_, v___y_4040_, v___y_4041_, v___y_4042_, v___y_4043_, v___y_4044_, v___y_4045_);
    leanh::lean_dec(v___y_4045_);
    leanh::lean_dec_ref(v___y_4044_);
    leanh::lean_dec(v___y_4043_);
    leanh::lean_dec_ref(v___y_4042_);
    leanh::lean_dec(v___y_4041_);
    leanh::lean_dec_ref(v___y_4040_);
    return v_res_4047_;
}
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Try_Collector_checkInductive_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6_spec__7(
    mut v_msgData_4048_: *mut leanh::LeanObject,
    mut v___y_4049_: *mut leanh::LeanObject,
    mut v___y_4050_: *mut leanh::LeanObject,
    mut v___y_4051_: *mut leanh::LeanObject,
    mut v___y_4052_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4054_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_4055_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4056_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_4057_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_lctx_4058_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_4059_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4060_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4061_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4062_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4054_ = lean_st_ref_get(v___y_4052_);
    v_env_4055_ = leanh::lean_ctor_get(v___x_4054_, 0);
    leanh::lean_inc_ref(v_env_4055_);
    leanh::lean_dec(v___x_4054_);
    v___x_4056_ = lean_st_ref_get(v___y_4050_);
    v_mctx_4057_ = leanh::lean_ctor_get(v___x_4056_, 0);
    leanh::lean_inc_ref(v_mctx_4057_);
    leanh::lean_dec(v___x_4056_);
    v_lctx_4058_ = leanh::lean_ctor_get(v___y_4049_, 2);
    v_options_4059_ = leanh::lean_ctor_get(v___y_4051_, 2);
    leanh::lean_inc_ref(v_options_4059_);
    leanh::lean_inc_ref(v_lctx_4058_);
    v___x_4060_ = leanh::lean_alloc_ctor(0, 4, (0) as u32);
    leanh::lean_ctor_set(v___x_4060_, 0, v_env_4055_);
    leanh::lean_ctor_set(v___x_4060_, 1, v_mctx_4057_);
    leanh::lean_ctor_set(v___x_4060_, 2, v_lctx_4058_);
    leanh::lean_ctor_set(v___x_4060_, 3, v_options_4059_);
    v___x_4061_ = leanh::lean_alloc_ctor(3, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_4061_, 0, v___x_4060_);
    leanh::lean_ctor_set(v___x_4061_, 1, v_msgData_4048_);
    v___x_4062_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_4062_, 0, v___x_4061_);
    return v___x_4062_;
}
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Try_Collector_checkInductive_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6_spec__7___boxed(
    mut v_msgData_4063_: *mut leanh::LeanObject,
    mut v___y_4064_: *mut leanh::LeanObject,
    mut v___y_4065_: *mut leanh::LeanObject,
    mut v___y_4066_: *mut leanh::LeanObject,
    mut v___y_4067_: *mut leanh::LeanObject,
    mut v___y_4068_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4069_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4069_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Try_Collector_checkInductive_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6_spec__7(v_msgData_4063_, v___y_4064_, v___y_4065_, v___y_4066_, v___y_4067_);
    leanh::lean_dec(v___y_4067_);
    leanh::lean_dec_ref(v___y_4066_);
    leanh::lean_dec(v___y_4065_);
    leanh::lean_dec_ref(v___y_4064_);
    return v_res_4069_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Try_Collector_checkInductive_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6___redArg(
    mut v_msg_4070_: *mut leanh::LeanObject,
    mut v___y_4071_: *mut leanh::LeanObject,
    mut v___y_4072_: *mut leanh::LeanObject,
    mut v___y_4073_: *mut leanh::LeanObject,
    mut v___y_4074_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_ref_4076_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4077_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4078_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4080_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4081_: u8 = 0;
    let mut v___x_4082_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4084_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4085_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4086_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ref_4076_ = leanh::lean_ctor_get(v___y_4073_, 5);
                v___x_4077_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Try_Collector_checkInductive_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6_spec__7(v_msg_4070_, v___y_4071_, v___y_4072_, v___y_4073_, v___y_4074_);
                v_a_4078_ = leanh::lean_ctor_get(v___x_4077_, 0);
                v_isSharedCheck_4086_ = (!leanh::lean_is_exclusive(v___x_4077_)) as u8;
                if v_isSharedCheck_4086_ == 0 {
                    v___x_4080_ = v___x_4077_;
                    v_isShared_4081_ = v_isSharedCheck_4086_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_a_4078_);
                    leanh::lean_dec(v___x_4077_);
                    v___x_4080_ = leanh::lean_box(0);
                    v_isShared_4081_ = v_isSharedCheck_4086_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                leanh::lean_inc(v_ref_4076_);
                v___x_4082_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_4082_, 0, v_ref_4076_);
                leanh::lean_ctor_set(v___x_4082_, 1, v_a_4078_);
                if v_isShared_4081_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_4080_, 1);
                    leanh::lean_ctor_set(v___x_4080_, 0, v___x_4082_);
                    v___x_4084_ = v___x_4080_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4085_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4085_, 0, v___x_4082_);
                    v___x_4084_ = v_reuseFailAlloc_4085_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_4084_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Try_Collector_checkInductive_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6___redArg___boxed(
    mut v_msg_4087_: *mut leanh::LeanObject,
    mut v___y_4088_: *mut leanh::LeanObject,
    mut v___y_4089_: *mut leanh::LeanObject,
    mut v___y_4090_: *mut leanh::LeanObject,
    mut v___y_4091_: *mut leanh::LeanObject,
    mut v___y_4092_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4093_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4093_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Try_Collector_checkInductive_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6___redArg(v_msg_4087_, v___y_4088_, v___y_4089_, v___y_4090_, v___y_4091_);
    leanh::lean_dec(v___y_4091_);
    leanh::lean_dec_ref(v___y_4090_);
    leanh::lean_dec(v___y_4089_);
    leanh::lean_dec_ref(v___y_4088_);
    return v_res_4093_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Try_Collector_checkInductive_spec__0_spec__0_spec__1_spec__2_spec__4___redArg(
    mut v_ref_4094_: *mut leanh::LeanObject,
    mut v_msg_4095_: *mut leanh::LeanObject,
    mut v___y_4096_: *mut leanh::LeanObject,
    mut v___y_4097_: *mut leanh::LeanObject,
    mut v___y_4098_: *mut leanh::LeanObject,
    mut v___y_4099_: *mut leanh::LeanObject,
    mut v___y_4100_: *mut leanh::LeanObject,
    mut v___y_4101_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_fileName_4103_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fileMap_4104_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_4105_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_currRecDepth_4106_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_maxRecDepth_4107_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_4108_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_currNamespace_4109_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_openDecls_4110_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_initHeartbeats_4111_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_maxHeartbeats_4112_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_quotContext_4113_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_currMacroScope_4114_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_diag_4115_: u8 = 0;
    let mut v_cancelTk_x3f_4116_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_suppressElabErrors_4117_: u8 = 0;
    let mut v_inheritedTraceOptions_4118_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_4119_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4120_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4121_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_fileName_4103_ = leanh::lean_ctor_get(v___y_4100_, 0);
    v_fileMap_4104_ = leanh::lean_ctor_get(v___y_4100_, 1);
    v_options_4105_ = leanh::lean_ctor_get(v___y_4100_, 2);
    v_currRecDepth_4106_ = leanh::lean_ctor_get(v___y_4100_, 3);
    v_maxRecDepth_4107_ = leanh::lean_ctor_get(v___y_4100_, 4);
    v_ref_4108_ = leanh::lean_ctor_get(v___y_4100_, 5);
    v_currNamespace_4109_ = leanh::lean_ctor_get(v___y_4100_, 6);
    v_openDecls_4110_ = leanh::lean_ctor_get(v___y_4100_, 7);
    v_initHeartbeats_4111_ = leanh::lean_ctor_get(v___y_4100_, 8);
    v_maxHeartbeats_4112_ = leanh::lean_ctor_get(v___y_4100_, 9);
    v_quotContext_4113_ = leanh::lean_ctor_get(v___y_4100_, 10);
    v_currMacroScope_4114_ = leanh::lean_ctor_get(v___y_4100_, 11);
    v_diag_4115_ = leanh::lean_ctor_get_uint8(
        v___y_4100_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 14) as u32,
    );
    v_cancelTk_x3f_4116_ = leanh::lean_ctor_get(v___y_4100_, 12);
    v_suppressElabErrors_4117_ = leanh::lean_ctor_get_uint8(
        v___y_4100_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 14 + 1) as u32,
    );
    v_inheritedTraceOptions_4118_ = leanh::lean_ctor_get(v___y_4100_, 13);
    v_ref_4119_ = l_Lean_replaceRef(v_ref_4094_, v_ref_4108_);
    leanh::lean_inc_ref(v_inheritedTraceOptions_4118_);
    leanh::lean_inc(v_cancelTk_x3f_4116_);
    leanh::lean_inc(v_currMacroScope_4114_);
    leanh::lean_inc(v_quotContext_4113_);
    leanh::lean_inc(v_maxHeartbeats_4112_);
    leanh::lean_inc(v_initHeartbeats_4111_);
    leanh::lean_inc(v_openDecls_4110_);
    leanh::lean_inc(v_currNamespace_4109_);
    leanh::lean_inc(v_maxRecDepth_4107_);
    leanh::lean_inc(v_currRecDepth_4106_);
    leanh::lean_inc_ref(v_options_4105_);
    leanh::lean_inc_ref(v_fileMap_4104_);
    leanh::lean_inc_ref(v_fileName_4103_);
    v___x_4120_ = leanh::lean_alloc_ctor(0, 14, (2) as u32);
    leanh::lean_ctor_set(v___x_4120_, 0, v_fileName_4103_);
    leanh::lean_ctor_set(v___x_4120_, 1, v_fileMap_4104_);
    leanh::lean_ctor_set(v___x_4120_, 2, v_options_4105_);
    leanh::lean_ctor_set(v___x_4120_, 3, v_currRecDepth_4106_);
    leanh::lean_ctor_set(v___x_4120_, 4, v_maxRecDepth_4107_);
    leanh::lean_ctor_set(v___x_4120_, 5, v_ref_4119_);
    leanh::lean_ctor_set(v___x_4120_, 6, v_currNamespace_4109_);
    leanh::lean_ctor_set(v___x_4120_, 7, v_openDecls_4110_);
    leanh::lean_ctor_set(v___x_4120_, 8, v_initHeartbeats_4111_);
    leanh::lean_ctor_set(v___x_4120_, 9, v_maxHeartbeats_4112_);
    leanh::lean_ctor_set(v___x_4120_, 10, v_quotContext_4113_);
    leanh::lean_ctor_set(v___x_4120_, 11, v_currMacroScope_4114_);
    leanh::lean_ctor_set(v___x_4120_, 12, v_cancelTk_x3f_4116_);
    leanh::lean_ctor_set(v___x_4120_, 13, v_inheritedTraceOptions_4118_);
    leanh::lean_ctor_set_uint8(
        v___x_4120_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 14) as u32,
        v_diag_4115_,
    );
    leanh::lean_ctor_set_uint8(
        v___x_4120_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 14 + 1) as u32,
        v_suppressElabErrors_4117_,
    );
    v___x_4121_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Try_Collector_checkInductive_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6___redArg(v_msg_4095_, v___y_4098_, v___y_4099_, v___x_4120_, v___y_4101_);
    leanh::lean_dec_ref_known(v___x_4120_, 14);
    return v___x_4121_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Try_Collector_checkInductive_spec__0_spec__0_spec__1_spec__2_spec__4___redArg___boxed(
    mut v_ref_4122_: *mut leanh::LeanObject,
    mut v_msg_4123_: *mut leanh::LeanObject,
    mut v___y_4124_: *mut leanh::LeanObject,
    mut v___y_4125_: *mut leanh::LeanObject,
    mut v___y_4126_: *mut leanh::LeanObject,
    mut v___y_4127_: *mut leanh::LeanObject,
    mut v___y_4128_: *mut leanh::LeanObject,
    mut v___y_4129_: *mut leanh::LeanObject,
    mut v___y_4130_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4131_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4131_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Try_Collector_checkInductive_spec__0_spec__0_spec__1_spec__2_spec__4___redArg(v_ref_4122_, v_msg_4123_, v___y_4124_, v___y_4125_, v___y_4126_, v___y_4127_, v___y_4128_, v___y_4129_);
    leanh::lean_dec(v___y_4129_);
    leanh::lean_dec_ref(v___y_4128_);
    leanh::lean_dec(v___y_4127_);
    leanh::lean_dec_ref(v___y_4126_);
    leanh::lean_dec(v___y_4125_);
    leanh::lean_dec_ref(v___y_4124_);
    leanh::lean_dec(v_ref_4122_);
    return v_res_4131_;
}
pub unsafe fn l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Try_Collector_checkInductive_spec__0_spec__0_spec__1_spec__2___redArg(
    mut v_ref_4132_: *mut leanh::LeanObject,
    mut v_msg_4133_: *mut leanh::LeanObject,
    mut v_declHint_4134_: *mut leanh::LeanObject,
    mut v___y_4135_: *mut leanh::LeanObject,
    mut v___y_4136_: *mut leanh::LeanObject,
    mut v___y_4137_: *mut leanh::LeanObject,
    mut v___y_4138_: *mut leanh::LeanObject,
    mut v___y_4139_: *mut leanh::LeanObject,
    mut v___y_4140_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4142_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4143_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4144_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4142_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Try_Collector_checkInductive_spec__0_spec__0_spec__1_spec__2_spec__3(v_msg_4133_, v_declHint_4134_, v___y_4135_, v___y_4136_, v___y_4137_, v___y_4138_, v___y_4139_, v___y_4140_);
    v_a_4143_ = leanh::lean_ctor_get(v___x_4142_, 0);
    leanh::lean_inc(v_a_4143_);
    leanh::lean_dec_ref(v___x_4142_);
    v___x_4144_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Try_Collector_checkInductive_spec__0_spec__0_spec__1_spec__2_spec__4___redArg(v_ref_4132_, v_a_4143_, v___y_4135_, v___y_4136_, v___y_4137_, v___y_4138_, v___y_4139_, v___y_4140_);
    return v___x_4144_;
}
pub unsafe fn l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Try_Collector_checkInductive_spec__0_spec__0_spec__1_spec__2___redArg___boxed(
    mut v_ref_4145_: *mut leanh::LeanObject,
    mut v_msg_4146_: *mut leanh::LeanObject,
    mut v_declHint_4147_: *mut leanh::LeanObject,
    mut v___y_4148_: *mut leanh::LeanObject,
    mut v___y_4149_: *mut leanh::LeanObject,
    mut v___y_4150_: *mut leanh::LeanObject,
    mut v___y_4151_: *mut leanh::LeanObject,
    mut v___y_4152_: *mut leanh::LeanObject,
    mut v___y_4153_: *mut leanh::LeanObject,
    mut v___y_4154_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4155_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4155_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Try_Collector_checkInductive_spec__0_spec__0_spec__1_spec__2___redArg(v_ref_4145_, v_msg_4146_, v_declHint_4147_, v___y_4148_, v___y_4149_, v___y_4150_, v___y_4151_, v___y_4152_, v___y_4153_);
    leanh::lean_dec(v___y_4153_);
    leanh::lean_dec_ref(v___y_4152_);
    leanh::lean_dec(v___y_4151_);
    leanh::lean_dec_ref(v___y_4150_);
    leanh::lean_dec(v___y_4149_);
    leanh::lean_dec_ref(v___y_4148_);
    leanh::lean_dec(v_ref_4145_);
    return v_res_4155_;
}
pub unsafe fn _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Try_Collector_checkInductive_spec__0_spec__0_spec__1___redArg___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_4157_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4158_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4157_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Try_Collector_checkInductive_spec__0_spec__0_spec__1___redArg___closed__0;
    v___x_4158_ = l_Lean_stringToMessageData(v___x_4157_);
    return v___x_4158_;
}
pub unsafe fn _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Try_Collector_checkInductive_spec__0_spec__0_spec__1___redArg___closed__3()
-> *mut leanh::LeanObject {
    let mut v___x_4160_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4161_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4160_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Try_Collector_checkInductive_spec__0_spec__0_spec__1___redArg___closed__2;
    v___x_4161_ = l_Lean_stringToMessageData(v___x_4160_);
    return v___x_4161_;
}
pub unsafe fn l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Try_Collector_checkInductive_spec__0_spec__0_spec__1___redArg(
    mut v_ref_4162_: *mut leanh::LeanObject,
    mut v_constName_4163_: *mut leanh::LeanObject,
    mut v___y_4164_: *mut leanh::LeanObject,
    mut v___y_4165_: *mut leanh::LeanObject,
    mut v___y_4166_: *mut leanh::LeanObject,
    mut v___y_4167_: *mut leanh::LeanObject,
    mut v___y_4168_: *mut leanh::LeanObject,
    mut v___y_4169_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4171_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4172_: u8 = 0;
    let mut v___x_4173_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4174_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4175_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4176_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4177_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4171_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Try_Collector_checkInductive_spec__0_spec__0_spec__1___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Try_Collector_checkInductive_spec__0_spec__0_spec__1___redArg___closed__1_once), _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Try_Collector_checkInductive_spec__0_spec__0_spec__1___redArg___closed__1);
    v___x_4172_ = 0;
    leanh::lean_inc(v_constName_4163_);
    v___x_4173_ = l_Lean_MessageData_ofConstName(v_constName_4163_, v___x_4172_);
    v___x_4174_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_4174_, 0, v___x_4171_);
    leanh::lean_ctor_set(v___x_4174_, 1, v___x_4173_);
    v___x_4175_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Try_Collector_checkInductive_spec__0_spec__0_spec__1___redArg___closed__3), core::ptr::addr_of_mut!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Try_Collector_checkInductive_spec__0_spec__0_spec__1___redArg___closed__3_once), _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Try_Collector_checkInductive_spec__0_spec__0_spec__1___redArg___closed__3);
    v___x_4176_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_4176_, 0, v___x_4174_);
    leanh::lean_ctor_set(v___x_4176_, 1, v___x_4175_);
    v___x_4177_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Try_Collector_checkInductive_spec__0_spec__0_spec__1_spec__2___redArg(v_ref_4162_, v___x_4176_, v_constName_4163_, v___y_4164_, v___y_4165_, v___y_4166_, v___y_4167_, v___y_4168_, v___y_4169_);
    return v___x_4177_;
}
pub unsafe fn l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Try_Collector_checkInductive_spec__0_spec__0_spec__1___redArg___boxed(
    mut v_ref_4178_: *mut leanh::LeanObject,
    mut v_constName_4179_: *mut leanh::LeanObject,
    mut v___y_4180_: *mut leanh::LeanObject,
    mut v___y_4181_: *mut leanh::LeanObject,
    mut v___y_4182_: *mut leanh::LeanObject,
    mut v___y_4183_: *mut leanh::LeanObject,
    mut v___y_4184_: *mut leanh::LeanObject,
    mut v___y_4185_: *mut leanh::LeanObject,
    mut v___y_4186_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4187_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4187_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Try_Collector_checkInductive_spec__0_spec__0_spec__1___redArg(v_ref_4178_, v_constName_4179_, v___y_4180_, v___y_4181_, v___y_4182_, v___y_4183_, v___y_4184_, v___y_4185_);
    leanh::lean_dec(v___y_4185_);
    leanh::lean_dec_ref(v___y_4184_);
    leanh::lean_dec(v___y_4183_);
    leanh::lean_dec_ref(v___y_4182_);
    leanh::lean_dec(v___y_4181_);
    leanh::lean_dec_ref(v___y_4180_);
    leanh::lean_dec(v_ref_4178_);
    return v_res_4187_;
}
pub unsafe fn l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Try_Collector_checkInductive_spec__0_spec__0___redArg(
    mut v_constName_4188_: *mut leanh::LeanObject,
    mut v___y_4189_: *mut leanh::LeanObject,
    mut v___y_4190_: *mut leanh::LeanObject,
    mut v___y_4191_: *mut leanh::LeanObject,
    mut v___y_4192_: *mut leanh::LeanObject,
    mut v___y_4193_: *mut leanh::LeanObject,
    mut v___y_4194_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_ref_4196_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4197_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_ref_4196_ = leanh::lean_ctor_get(v___y_4193_, 5);
    v___x_4197_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Try_Collector_checkInductive_spec__0_spec__0_spec__1___redArg(v_ref_4196_, v_constName_4188_, v___y_4189_, v___y_4190_, v___y_4191_, v___y_4192_, v___y_4193_, v___y_4194_);
    return v___x_4197_;
}
pub unsafe fn l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Try_Collector_checkInductive_spec__0_spec__0___redArg___boxed(
    mut v_constName_4198_: *mut leanh::LeanObject,
    mut v___y_4199_: *mut leanh::LeanObject,
    mut v___y_4200_: *mut leanh::LeanObject,
    mut v___y_4201_: *mut leanh::LeanObject,
    mut v___y_4202_: *mut leanh::LeanObject,
    mut v___y_4203_: *mut leanh::LeanObject,
    mut v___y_4204_: *mut leanh::LeanObject,
    mut v___y_4205_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4206_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4206_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Try_Collector_checkInductive_spec__0_spec__0___redArg(v_constName_4198_, v___y_4199_, v___y_4200_, v___y_4201_, v___y_4202_, v___y_4203_, v___y_4204_);
    leanh::lean_dec(v___y_4204_);
    leanh::lean_dec_ref(v___y_4203_);
    leanh::lean_dec(v___y_4202_);
    leanh::lean_dec_ref(v___y_4201_);
    leanh::lean_dec(v___y_4200_);
    leanh::lean_dec_ref(v___y_4199_);
    return v_res_4206_;
}
pub unsafe fn l_Lean_getConstInfo___at___00Lean_Meta_Try_Collector_checkInductive_spec__0(
    mut v_constName_4207_: *mut leanh::LeanObject,
    mut v___y_4208_: *mut leanh::LeanObject,
    mut v___y_4209_: *mut leanh::LeanObject,
    mut v___y_4210_: *mut leanh::LeanObject,
    mut v___y_4211_: *mut leanh::LeanObject,
    mut v___y_4212_: *mut leanh::LeanObject,
    mut v___y_4213_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4215_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_4216_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4217_: u8 = 0;
    let mut v___x_4218_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4219_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_4220_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4222_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4223_: u8 = 0;
    let mut v___x_4225_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4226_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4227_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4215_ = lean_st_ref_get(v___y_4213_);
                v_env_4216_ = leanh::lean_ctor_get(v___x_4215_, 0);
                leanh::lean_inc_ref(v_env_4216_);
                leanh::lean_dec(v___x_4215_);
                v___x_4217_ = 0;
                leanh::lean_inc(v_constName_4207_);
                v___x_4218_ =
                    l_Lean_Environment_find_x3f(v_env_4216_, v_constName_4207_, v___x_4217_);
                if leanh::lean_obj_tag(v___x_4218_) == 0 {
                    v___x_4219_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Try_Collector_checkInductive_spec__0_spec__0___redArg(v_constName_4207_, v___y_4208_, v___y_4209_, v___y_4210_, v___y_4211_, v___y_4212_, v___y_4213_);
                    return v___x_4219_;
                } else {
                    leanh::lean_dec(v_constName_4207_);
                    v_val_4220_ = leanh::lean_ctor_get(v___x_4218_, 0);
                    v_isSharedCheck_4227_ = (!leanh::lean_is_exclusive(v___x_4218_)) as u8;
                    if v_isSharedCheck_4227_ == 0 {
                        v___x_4222_ = v___x_4218_;
                        v_isShared_4223_ = v_isSharedCheck_4227_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_val_4220_);
                        leanh::lean_dec(v___x_4218_);
                        v___x_4222_ = leanh::lean_box(0);
                        v_isShared_4223_ = v_isSharedCheck_4227_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_4223_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_4222_, 0);
                    v___x_4225_ = v___x_4222_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4226_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4226_, 0, v_val_4220_);
                    v___x_4225_ = v_reuseFailAlloc_4226_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_4225_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_getConstInfo___at___00Lean_Meta_Try_Collector_checkInductive_spec__0___boxed(
    mut v_constName_4228_: *mut leanh::LeanObject,
    mut v___y_4229_: *mut leanh::LeanObject,
    mut v___y_4230_: *mut leanh::LeanObject,
    mut v___y_4231_: *mut leanh::LeanObject,
    mut v___y_4232_: *mut leanh::LeanObject,
    mut v___y_4233_: *mut leanh::LeanObject,
    mut v___y_4234_: *mut leanh::LeanObject,
    mut v___y_4235_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4236_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4236_ = l_Lean_getConstInfo___at___00Lean_Meta_Try_Collector_checkInductive_spec__0(
        v_constName_4228_,
        v___y_4229_,
        v___y_4230_,
        v___y_4231_,
        v___y_4232_,
        v___y_4233_,
        v___y_4234_,
    );
    leanh::lean_dec(v___y_4234_);
    leanh::lean_dec_ref(v___y_4233_);
    leanh::lean_dec(v___y_4232_);
    leanh::lean_dec_ref(v___y_4231_);
    leanh::lean_dec(v___y_4230_);
    leanh::lean_dec_ref(v___y_4229_);
    return v_res_4236_;
}
pub unsafe fn l_Lean_Meta_Try_Collector_checkInductive(
    mut v_localDecl_4237_: *mut leanh::LeanObject,
    mut v_a_4238_: *mut leanh::LeanObject,
    mut v_a_4239_: *mut leanh::LeanObject,
    mut v_a_4240_: *mut leanh::LeanObject,
    mut v_a_4241_: *mut leanh::LeanObject,
    mut v_a_4242_: *mut leanh::LeanObject,
    mut v_a_4243_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4245_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4246_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4247_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4249_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4250_: u8 = 0;
    let mut v___x_4251_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_declName_4252_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4253_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4254_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4256_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4257_: u8 = 0;
    let mut v_val_4258_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4259_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4260_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4262_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4263_: u8 = 0;
    let mut v___x_4264_: u8 = 0;
    let mut v___x_4265_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4267_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4268_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4269_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4270_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4272_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4273_: u8 = 0;
    let mut v___x_4274_: u8 = 0;
    let mut v___x_4275_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_allConsts_4276_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unfoldCandidates_4277_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_eqnCandidates_4278_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_funIndCandidates_4279_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_indCandidates_4280_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_libSearchResults_4281_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4283_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4284_: u8 = 0;
    let mut v___x_4285_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4286_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4287_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4289_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4290_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4291_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4293_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4294_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4295_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4296_: u8 = 0;
    let mut v___x_4297_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4299_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4300_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4301_: u8 = 0;
    let mut v_a_4302_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4304_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4305_: u8 = 0;
    let mut v___x_4307_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4308_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4309_: u8 = 0;
    let mut v_isSharedCheck_4310_: u8 = 0;
    let mut v___x_4311_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4313_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4314_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4315_: u8 = 0;
    let mut v_a_4316_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4318_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4319_: u8 = 0;
    let mut v___x_4321_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4322_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4323_: u8 = 0;
    let mut v___x_4324_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4326_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4327_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4328_: u8 = 0;
    let mut v_a_4329_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4331_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4332_: u8 = 0;
    let mut v___x_4334_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4335_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4336_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4245_ = l_Lean_LocalDecl_type(v_localDecl_4237_);
                v___x_4246_ =
                    l_Lean_Meta_whnfD(v___x_4245_, v_a_4240_, v_a_4241_, v_a_4242_, v_a_4243_);
                if leanh::lean_obj_tag(v___x_4246_) == 0 {
                    v_a_4247_ = leanh::lean_ctor_get(v___x_4246_, 0);
                    v_isSharedCheck_4328_ = (!leanh::lean_is_exclusive(v___x_4246_)) as u8;
                    if v_isSharedCheck_4328_ == 0 {
                        v___x_4249_ = v___x_4246_;
                        v_isShared_4250_ = v_isSharedCheck_4328_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_4247_);
                        leanh::lean_dec(v___x_4246_);
                        v___x_4249_ = leanh::lean_box(0);
                        v_isShared_4250_ = v_isSharedCheck_4328_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_4329_ = leanh::lean_ctor_get(v___x_4246_, 0);
                    v_isSharedCheck_4336_ = (!leanh::lean_is_exclusive(v___x_4246_)) as u8;
                    if v_isSharedCheck_4336_ == 0 {
                        v___x_4331_ = v___x_4246_;
                        v_isShared_4332_ = v_isSharedCheck_4336_;
                        state = 16;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_4329_);
                        leanh::lean_dec(v___x_4246_);
                        v___x_4331_ = leanh::lean_box(0);
                        v_isShared_4332_ = v_isSharedCheck_4336_;
                        state = 16;
                        continue;
                    }
                }
            }
            1 => {
                v___x_4251_ = l_Lean_Expr_getAppFn(v_a_4247_);
                leanh::lean_dec(v_a_4247_);
                if leanh::lean_obj_tag(v___x_4251_) == 4 {
                    leanh::lean_del_object(v___x_4249_);
                    v_declName_4252_ = leanh::lean_ctor_get(v___x_4251_, 0);
                    leanh::lean_inc_n(v_declName_4252_, 2);
                    leanh::lean_dec_ref_known(v___x_4251_, 2);
                    v___x_4253_ =
                        l_Lean_getConstInfo___at___00Lean_Meta_Try_Collector_checkInductive_spec__0(
                            v_declName_4252_,
                            v_a_4238_,
                            v_a_4239_,
                            v_a_4240_,
                            v_a_4241_,
                            v_a_4242_,
                            v_a_4243_,
                        );
                    if leanh::lean_obj_tag(v___x_4253_) == 0 {
                        v_a_4254_ = leanh::lean_ctor_get(v___x_4253_, 0);
                        v_isSharedCheck_4315_ =
                            (!leanh::lean_is_exclusive(v___x_4253_)) as u8;
                        if v_isSharedCheck_4315_ == 0 {
                            v___x_4256_ = v___x_4253_;
                            v_isShared_4257_ = v_isSharedCheck_4315_;
                            state = 2;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_4254_);
                            leanh::lean_dec(v___x_4253_);
                            v___x_4256_ = leanh::lean_box(0);
                            v_isShared_4257_ = v_isSharedCheck_4315_;
                            state = 2;
                            continue;
                        }
                    } else {
                        leanh::lean_dec(v_declName_4252_);
                        v_a_4316_ = leanh::lean_ctor_get(v___x_4253_, 0);
                        v_isSharedCheck_4323_ =
                            (!leanh::lean_is_exclusive(v___x_4253_)) as u8;
                        if v_isSharedCheck_4323_ == 0 {
                            v___x_4318_ = v___x_4253_;
                            v_isShared_4319_ = v_isSharedCheck_4323_;
                            state = 13;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_4316_);
                            leanh::lean_dec(v___x_4253_);
                            v___x_4318_ = leanh::lean_box(0);
                            v_isShared_4319_ = v_isSharedCheck_4323_;
                            state = 13;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_dec_ref(v___x_4251_);
                    v___x_4324_ = leanh::lean_box(0);
                    if v_isShared_4250_ == 0 {
                        leanh::lean_ctor_set(v___x_4249_, 0, v___x_4324_);
                        v___x_4326_ = v___x_4249_;
                        state = 15;
                        continue;
                    } else {
                        v_reuseFailAlloc_4327_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_4327_, 0, v___x_4324_);
                        v___x_4326_ = v_reuseFailAlloc_4327_;
                        state = 15;
                        continue;
                    }
                }
            }
            2 => {
                if leanh::lean_obj_tag(v_a_4254_) == 5 {
                    leanh::lean_del_object(v___x_4256_);
                    v_val_4258_ = leanh::lean_ctor_get(v_a_4254_, 0);
                    leanh::lean_inc_ref(v_val_4258_);
                    leanh::lean_dec_ref_known(v_a_4254_, 1);
                    v___x_4259_ = l_Lean_Meta_Try_Collector_isEligible___redArg(
                        v_declName_4252_,
                        v_a_4238_,
                        v_a_4242_,
                        v_a_4243_,
                    );
                    v_a_4260_ = leanh::lean_ctor_get(v___x_4259_, 0);
                    v_isSharedCheck_4310_ = (!leanh::lean_is_exclusive(v___x_4259_)) as u8;
                    if v_isSharedCheck_4310_ == 0 {
                        v___x_4262_ = v___x_4259_;
                        v_isShared_4263_ = v_isSharedCheck_4310_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_4260_);
                        leanh::lean_dec(v___x_4259_);
                        v___x_4262_ = leanh::lean_box(0);
                        v_isShared_4263_ = v_isSharedCheck_4310_;
                        state = 3;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v_a_4254_);
                    leanh::lean_dec(v_declName_4252_);
                    v___x_4311_ = leanh::lean_box(0);
                    if v_isShared_4257_ == 0 {
                        leanh::lean_ctor_set(v___x_4256_, 0, v___x_4311_);
                        v___x_4313_ = v___x_4256_;
                        state = 12;
                        continue;
                    } else {
                        v_reuseFailAlloc_4314_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_4314_, 0, v___x_4311_);
                        v___x_4313_ = v_reuseFailAlloc_4314_;
                        state = 12;
                        continue;
                    }
                }
            }
            3 => {
                v___x_4264_ = (leanh::lean_unbox(v_a_4260_) as u8);
                leanh::lean_dec(v_a_4260_);
                if v___x_4264_ == 0 {
                    leanh::lean_dec_ref(v_val_4258_);
                    leanh::lean_dec(v_declName_4252_);
                    v___x_4265_ = leanh::lean_box(0);
                    if v_isShared_4263_ == 0 {
                        leanh::lean_ctor_set(v___x_4262_, 0, v___x_4265_);
                        v___x_4267_ = v___x_4262_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_4268_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_4268_, 0, v___x_4265_);
                        v___x_4267_ = v_reuseFailAlloc_4268_;
                        state = 4;
                        continue;
                    }
                } else {
                    leanh::lean_del_object(v___x_4262_);
                    v___x_4269_ =
                        l_Lean_Meta_Grind_isGlobalSplit___redArg(v_declName_4252_, v_a_4243_);
                    leanh::lean_dec(v_declName_4252_);
                    if leanh::lean_obj_tag(v___x_4269_) == 0 {
                        v_a_4270_ = leanh::lean_ctor_get(v___x_4269_, 0);
                        v_isSharedCheck_4301_ =
                            (!leanh::lean_is_exclusive(v___x_4269_)) as u8;
                        if v_isSharedCheck_4301_ == 0 {
                            v___x_4272_ = v___x_4269_;
                            v_isShared_4273_ = v_isSharedCheck_4301_;
                            state = 5;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_4270_);
                            leanh::lean_dec(v___x_4269_);
                            v___x_4272_ = leanh::lean_box(0);
                            v_isShared_4273_ = v_isSharedCheck_4301_;
                            state = 5;
                            continue;
                        }
                    } else {
                        leanh::lean_dec_ref(v_val_4258_);
                        v_a_4302_ = leanh::lean_ctor_get(v___x_4269_, 0);
                        v_isSharedCheck_4309_ =
                            (!leanh::lean_is_exclusive(v___x_4269_)) as u8;
                        if v_isSharedCheck_4309_ == 0 {
                            v___x_4304_ = v___x_4269_;
                            v_isShared_4305_ = v_isSharedCheck_4309_;
                            state = 10;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_4302_);
                            leanh::lean_dec(v___x_4269_);
                            v___x_4304_ = leanh::lean_box(0);
                            v_isShared_4305_ = v_isSharedCheck_4309_;
                            state = 10;
                            continue;
                        }
                    }
                }
            }
            4 => {
                return v___x_4267_;
            }
            5 => {
                v___x_4274_ = (leanh::lean_unbox(v_a_4270_) as u8);
                leanh::lean_dec(v_a_4270_);
                if v___x_4274_ == 0 {
                    v___x_4275_ = lean_st_ref_take(v_a_4239_);
                    v_allConsts_4276_ = leanh::lean_ctor_get(v___x_4275_, 0);
                    v_unfoldCandidates_4277_ = leanh::lean_ctor_get(v___x_4275_, 1);
                    v_eqnCandidates_4278_ = leanh::lean_ctor_get(v___x_4275_, 2);
                    v_funIndCandidates_4279_ = leanh::lean_ctor_get(v___x_4275_, 3);
                    v_indCandidates_4280_ = leanh::lean_ctor_get(v___x_4275_, 4);
                    v_libSearchResults_4281_ = leanh::lean_ctor_get(v___x_4275_, 5);
                    v_isSharedCheck_4296_ = (!leanh::lean_is_exclusive(v___x_4275_)) as u8;
                    if v_isSharedCheck_4296_ == 0 {
                        v___x_4283_ = v___x_4275_;
                        v_isShared_4284_ = v_isSharedCheck_4296_;
                        state = 6;
                        continue;
                    } else {
                        leanh::lean_inc(v_libSearchResults_4281_);
                        leanh::lean_inc(v_indCandidates_4280_);
                        leanh::lean_inc(v_funIndCandidates_4279_);
                        leanh::lean_inc(v_eqnCandidates_4278_);
                        leanh::lean_inc(v_unfoldCandidates_4277_);
                        leanh::lean_inc(v_allConsts_4276_);
                        leanh::lean_dec(v___x_4275_);
                        v___x_4283_ = leanh::lean_box(0);
                        v_isShared_4284_ = v_isSharedCheck_4296_;
                        state = 6;
                        continue;
                    }
                } else {
                    leanh::lean_dec_ref(v_val_4258_);
                    v___x_4297_ = leanh::lean_box(0);
                    if v_isShared_4273_ == 0 {
                        leanh::lean_ctor_set(v___x_4272_, 0, v___x_4297_);
                        v___x_4299_ = v___x_4272_;
                        state = 9;
                        continue;
                    } else {
                        v_reuseFailAlloc_4300_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_4300_, 0, v___x_4297_);
                        v___x_4299_ = v_reuseFailAlloc_4300_;
                        state = 9;
                        continue;
                    }
                }
            }
            6 => {
                v___x_4285_ = l_Lean_LocalDecl_fvarId(v_localDecl_4237_);
                v___x_4286_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_4286_, 0, v___x_4285_);
                leanh::lean_ctor_set(v___x_4286_, 1, v_val_4258_);
                v___x_4287_ = lean_array_push(v_indCandidates_4280_, v___x_4286_);
                if v_isShared_4284_ == 0 {
                    leanh::lean_ctor_set(v___x_4283_, 4, v___x_4287_);
                    v___x_4289_ = v___x_4283_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_4295_ = leanh::lean_alloc_ctor(0, 6, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4295_, 0, v_allConsts_4276_);
                    leanh::lean_ctor_set(
                        v_reuseFailAlloc_4295_,
                        1,
                        v_unfoldCandidates_4277_,
                    );
                    leanh::lean_ctor_set(v_reuseFailAlloc_4295_, 2, v_eqnCandidates_4278_);
                    leanh::lean_ctor_set(
                        v_reuseFailAlloc_4295_,
                        3,
                        v_funIndCandidates_4279_,
                    );
                    leanh::lean_ctor_set(v_reuseFailAlloc_4295_, 4, v___x_4287_);
                    leanh::lean_ctor_set(
                        v_reuseFailAlloc_4295_,
                        5,
                        v_libSearchResults_4281_,
                    );
                    v___x_4289_ = v_reuseFailAlloc_4295_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                v___x_4290_ = lean_st_ref_set(v_a_4239_, v___x_4289_);
                v___x_4291_ = leanh::lean_box(0);
                if v_isShared_4273_ == 0 {
                    leanh::lean_ctor_set(v___x_4272_, 0, v___x_4291_);
                    v___x_4293_ = v___x_4272_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_4294_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4294_, 0, v___x_4291_);
                    v___x_4293_ = v_reuseFailAlloc_4294_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_4293_;
            }
            9 => {
                return v___x_4299_;
            }
            10 => {
                if v_isShared_4305_ == 0 {
                    v___x_4307_ = v___x_4304_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_4308_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4308_, 0, v_a_4302_);
                    v___x_4307_ = v_reuseFailAlloc_4308_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                return v___x_4307_;
            }
            12 => {
                return v___x_4313_;
            }
            13 => {
                if v_isShared_4319_ == 0 {
                    v___x_4321_ = v___x_4318_;
                    state = 14;
                    continue;
                } else {
                    v_reuseFailAlloc_4322_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4322_, 0, v_a_4316_);
                    v___x_4321_ = v_reuseFailAlloc_4322_;
                    state = 14;
                    continue;
                }
            }
            14 => {
                return v___x_4321_;
            }
            15 => {
                return v___x_4326_;
            }
            16 => {
                if v_isShared_4332_ == 0 {
                    v___x_4334_ = v___x_4331_;
                    state = 17;
                    continue;
                } else {
                    v_reuseFailAlloc_4335_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4335_, 0, v_a_4329_);
                    v___x_4334_ = v_reuseFailAlloc_4335_;
                    state = 17;
                    continue;
                }
            }
            17 => {
                return v___x_4334_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Try_Collector_checkInductive___boxed(
    mut v_localDecl_4337_: *mut leanh::LeanObject,
    mut v_a_4338_: *mut leanh::LeanObject,
    mut v_a_4339_: *mut leanh::LeanObject,
    mut v_a_4340_: *mut leanh::LeanObject,
    mut v_a_4341_: *mut leanh::LeanObject,
    mut v_a_4342_: *mut leanh::LeanObject,
    mut v_a_4343_: *mut leanh::LeanObject,
    mut v_a_4344_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4345_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4345_ = l_Lean_Meta_Try_Collector_checkInductive(
        v_localDecl_4337_,
        v_a_4338_,
        v_a_4339_,
        v_a_4340_,
        v_a_4341_,
        v_a_4342_,
        v_a_4343_,
    );
    leanh::lean_dec(v_a_4343_);
    leanh::lean_dec_ref(v_a_4342_);
    leanh::lean_dec(v_a_4341_);
    leanh::lean_dec_ref(v_a_4340_);
    leanh::lean_dec(v_a_4339_);
    leanh::lean_dec_ref(v_a_4338_);
    leanh::lean_dec_ref(v_localDecl_4337_);
    return v_res_4345_;
}
pub unsafe fn l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Try_Collector_checkInductive_spec__0_spec__0(
    mut v_00_u03b1_4346_: *mut leanh::LeanObject,
    mut v_constName_4347_: *mut leanh::LeanObject,
    mut v___y_4348_: *mut leanh::LeanObject,
    mut v___y_4349_: *mut leanh::LeanObject,
    mut v___y_4350_: *mut leanh::LeanObject,
    mut v___y_4351_: *mut leanh::LeanObject,
    mut v___y_4352_: *mut leanh::LeanObject,
    mut v___y_4353_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4355_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4355_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Try_Collector_checkInductive_spec__0_spec__0___redArg(v_constName_4347_, v___y_4348_, v___y_4349_, v___y_4350_, v___y_4351_, v___y_4352_, v___y_4353_);
    return v___x_4355_;
}
pub unsafe fn l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Try_Collector_checkInductive_spec__0_spec__0___boxed(
    mut v_00_u03b1_4356_: *mut leanh::LeanObject,
    mut v_constName_4357_: *mut leanh::LeanObject,
    mut v___y_4358_: *mut leanh::LeanObject,
    mut v___y_4359_: *mut leanh::LeanObject,
    mut v___y_4360_: *mut leanh::LeanObject,
    mut v___y_4361_: *mut leanh::LeanObject,
    mut v___y_4362_: *mut leanh::LeanObject,
    mut v___y_4363_: *mut leanh::LeanObject,
    mut v___y_4364_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4365_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4365_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Try_Collector_checkInductive_spec__0_spec__0(v_00_u03b1_4356_, v_constName_4357_, v___y_4358_, v___y_4359_, v___y_4360_, v___y_4361_, v___y_4362_, v___y_4363_);
    leanh::lean_dec(v___y_4363_);
    leanh::lean_dec_ref(v___y_4362_);
    leanh::lean_dec(v___y_4361_);
    leanh::lean_dec_ref(v___y_4360_);
    leanh::lean_dec(v___y_4359_);
    leanh::lean_dec_ref(v___y_4358_);
    return v_res_4365_;
}
pub unsafe fn l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Try_Collector_checkInductive_spec__0_spec__0_spec__1(
    mut v_00_u03b1_4366_: *mut leanh::LeanObject,
    mut v_ref_4367_: *mut leanh::LeanObject,
    mut v_constName_4368_: *mut leanh::LeanObject,
    mut v___y_4369_: *mut leanh::LeanObject,
    mut v___y_4370_: *mut leanh::LeanObject,
    mut v___y_4371_: *mut leanh::LeanObject,
    mut v___y_4372_: *mut leanh::LeanObject,
    mut v___y_4373_: *mut leanh::LeanObject,
    mut v___y_4374_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4376_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4376_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Try_Collector_checkInductive_spec__0_spec__0_spec__1___redArg(v_ref_4367_, v_constName_4368_, v___y_4369_, v___y_4370_, v___y_4371_, v___y_4372_, v___y_4373_, v___y_4374_);
    return v___x_4376_;
}
pub unsafe fn l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Try_Collector_checkInductive_spec__0_spec__0_spec__1___boxed(
    mut v_00_u03b1_4377_: *mut leanh::LeanObject,
    mut v_ref_4378_: *mut leanh::LeanObject,
    mut v_constName_4379_: *mut leanh::LeanObject,
    mut v___y_4380_: *mut leanh::LeanObject,
    mut v___y_4381_: *mut leanh::LeanObject,
    mut v___y_4382_: *mut leanh::LeanObject,
    mut v___y_4383_: *mut leanh::LeanObject,
    mut v___y_4384_: *mut leanh::LeanObject,
    mut v___y_4385_: *mut leanh::LeanObject,
    mut v___y_4386_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4387_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4387_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Try_Collector_checkInductive_spec__0_spec__0_spec__1(v_00_u03b1_4377_, v_ref_4378_, v_constName_4379_, v___y_4380_, v___y_4381_, v___y_4382_, v___y_4383_, v___y_4384_, v___y_4385_);
    leanh::lean_dec(v___y_4385_);
    leanh::lean_dec_ref(v___y_4384_);
    leanh::lean_dec(v___y_4383_);
    leanh::lean_dec_ref(v___y_4382_);
    leanh::lean_dec(v___y_4381_);
    leanh::lean_dec_ref(v___y_4380_);
    leanh::lean_dec(v_ref_4378_);
    return v_res_4387_;
}
pub unsafe fn l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Try_Collector_checkInductive_spec__0_spec__0_spec__1_spec__2(
    mut v_00_u03b1_4388_: *mut leanh::LeanObject,
    mut v_ref_4389_: *mut leanh::LeanObject,
    mut v_msg_4390_: *mut leanh::LeanObject,
    mut v_declHint_4391_: *mut leanh::LeanObject,
    mut v___y_4392_: *mut leanh::LeanObject,
    mut v___y_4393_: *mut leanh::LeanObject,
    mut v___y_4394_: *mut leanh::LeanObject,
    mut v___y_4395_: *mut leanh::LeanObject,
    mut v___y_4396_: *mut leanh::LeanObject,
    mut v___y_4397_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4399_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4399_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Try_Collector_checkInductive_spec__0_spec__0_spec__1_spec__2___redArg(v_ref_4389_, v_msg_4390_, v_declHint_4391_, v___y_4392_, v___y_4393_, v___y_4394_, v___y_4395_, v___y_4396_, v___y_4397_);
    return v___x_4399_;
}
pub unsafe fn l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Try_Collector_checkInductive_spec__0_spec__0_spec__1_spec__2___boxed(
    mut v_00_u03b1_4400_: *mut leanh::LeanObject,
    mut v_ref_4401_: *mut leanh::LeanObject,
    mut v_msg_4402_: *mut leanh::LeanObject,
    mut v_declHint_4403_: *mut leanh::LeanObject,
    mut v___y_4404_: *mut leanh::LeanObject,
    mut v___y_4405_: *mut leanh::LeanObject,
    mut v___y_4406_: *mut leanh::LeanObject,
    mut v___y_4407_: *mut leanh::LeanObject,
    mut v___y_4408_: *mut leanh::LeanObject,
    mut v___y_4409_: *mut leanh::LeanObject,
    mut v___y_4410_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4411_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4411_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Try_Collector_checkInductive_spec__0_spec__0_spec__1_spec__2(v_00_u03b1_4400_, v_ref_4401_, v_msg_4402_, v_declHint_4403_, v___y_4404_, v___y_4405_, v___y_4406_, v___y_4407_, v___y_4408_, v___y_4409_);
    leanh::lean_dec(v___y_4409_);
    leanh::lean_dec_ref(v___y_4408_);
    leanh::lean_dec(v___y_4407_);
    leanh::lean_dec_ref(v___y_4406_);
    leanh::lean_dec(v___y_4405_);
    leanh::lean_dec_ref(v___y_4404_);
    leanh::lean_dec(v_ref_4401_);
    return v_res_4411_;
}
pub unsafe fn l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Try_Collector_checkInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4(
    mut v_msg_4412_: *mut leanh::LeanObject,
    mut v_declHint_4413_: *mut leanh::LeanObject,
    mut v___y_4414_: *mut leanh::LeanObject,
    mut v___y_4415_: *mut leanh::LeanObject,
    mut v___y_4416_: *mut leanh::LeanObject,
    mut v___y_4417_: *mut leanh::LeanObject,
    mut v___y_4418_: *mut leanh::LeanObject,
    mut v___y_4419_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4421_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4421_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Try_Collector_checkInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg(v_msg_4412_, v_declHint_4413_, v___y_4419_);
    return v___x_4421_;
}
pub unsafe fn l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Try_Collector_checkInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___boxed(
    mut v_msg_4422_: *mut leanh::LeanObject,
    mut v_declHint_4423_: *mut leanh::LeanObject,
    mut v___y_4424_: *mut leanh::LeanObject,
    mut v___y_4425_: *mut leanh::LeanObject,
    mut v___y_4426_: *mut leanh::LeanObject,
    mut v___y_4427_: *mut leanh::LeanObject,
    mut v___y_4428_: *mut leanh::LeanObject,
    mut v___y_4429_: *mut leanh::LeanObject,
    mut v___y_4430_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4431_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4431_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Try_Collector_checkInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4(v_msg_4422_, v_declHint_4423_, v___y_4424_, v___y_4425_, v___y_4426_, v___y_4427_, v___y_4428_, v___y_4429_);
    leanh::lean_dec(v___y_4429_);
    leanh::lean_dec_ref(v___y_4428_);
    leanh::lean_dec(v___y_4427_);
    leanh::lean_dec_ref(v___y_4426_);
    leanh::lean_dec(v___y_4425_);
    leanh::lean_dec_ref(v___y_4424_);
    return v_res_4431_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Try_Collector_checkInductive_spec__0_spec__0_spec__1_spec__2_spec__4(
    mut v_00_u03b1_4432_: *mut leanh::LeanObject,
    mut v_ref_4433_: *mut leanh::LeanObject,
    mut v_msg_4434_: *mut leanh::LeanObject,
    mut v___y_4435_: *mut leanh::LeanObject,
    mut v___y_4436_: *mut leanh::LeanObject,
    mut v___y_4437_: *mut leanh::LeanObject,
    mut v___y_4438_: *mut leanh::LeanObject,
    mut v___y_4439_: *mut leanh::LeanObject,
    mut v___y_4440_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4442_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4442_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Try_Collector_checkInductive_spec__0_spec__0_spec__1_spec__2_spec__4___redArg(v_ref_4433_, v_msg_4434_, v___y_4435_, v___y_4436_, v___y_4437_, v___y_4438_, v___y_4439_, v___y_4440_);
    return v___x_4442_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Try_Collector_checkInductive_spec__0_spec__0_spec__1_spec__2_spec__4___boxed(
    mut v_00_u03b1_4443_: *mut leanh::LeanObject,
    mut v_ref_4444_: *mut leanh::LeanObject,
    mut v_msg_4445_: *mut leanh::LeanObject,
    mut v___y_4446_: *mut leanh::LeanObject,
    mut v___y_4447_: *mut leanh::LeanObject,
    mut v___y_4448_: *mut leanh::LeanObject,
    mut v___y_4449_: *mut leanh::LeanObject,
    mut v___y_4450_: *mut leanh::LeanObject,
    mut v___y_4451_: *mut leanh::LeanObject,
    mut v___y_4452_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4453_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4453_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Try_Collector_checkInductive_spec__0_spec__0_spec__1_spec__2_spec__4(v_00_u03b1_4443_, v_ref_4444_, v_msg_4445_, v___y_4446_, v___y_4447_, v___y_4448_, v___y_4449_, v___y_4450_, v___y_4451_);
    leanh::lean_dec(v___y_4451_);
    leanh::lean_dec_ref(v___y_4450_);
    leanh::lean_dec(v___y_4449_);
    leanh::lean_dec_ref(v___y_4448_);
    leanh::lean_dec(v___y_4447_);
    leanh::lean_dec_ref(v___y_4446_);
    leanh::lean_dec(v_ref_4444_);
    return v_res_4453_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Try_Collector_checkInductive_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6(
    mut v_00_u03b1_4454_: *mut leanh::LeanObject,
    mut v_msg_4455_: *mut leanh::LeanObject,
    mut v___y_4456_: *mut leanh::LeanObject,
    mut v___y_4457_: *mut leanh::LeanObject,
    mut v___y_4458_: *mut leanh::LeanObject,
    mut v___y_4459_: *mut leanh::LeanObject,
    mut v___y_4460_: *mut leanh::LeanObject,
    mut v___y_4461_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4463_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4463_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Try_Collector_checkInductive_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6___redArg(v_msg_4455_, v___y_4458_, v___y_4459_, v___y_4460_, v___y_4461_);
    return v___x_4463_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Try_Collector_checkInductive_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6___boxed(
    mut v_00_u03b1_4464_: *mut leanh::LeanObject,
    mut v_msg_4465_: *mut leanh::LeanObject,
    mut v___y_4466_: *mut leanh::LeanObject,
    mut v___y_4467_: *mut leanh::LeanObject,
    mut v___y_4468_: *mut leanh::LeanObject,
    mut v___y_4469_: *mut leanh::LeanObject,
    mut v___y_4470_: *mut leanh::LeanObject,
    mut v___y_4471_: *mut leanh::LeanObject,
    mut v___y_4472_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4473_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4473_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Try_Collector_checkInductive_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6(v_00_u03b1_4464_, v_msg_4465_, v___y_4466_, v___y_4467_, v___y_4468_, v___y_4469_, v___y_4470_, v___y_4471_);
    leanh::lean_dec(v___y_4471_);
    leanh::lean_dec_ref(v___y_4470_);
    leanh::lean_dec(v___y_4469_);
    leanh::lean_dec_ref(v___y_4468_);
    leanh::lean_dec(v___y_4467_);
    leanh::lean_dec_ref(v___y_4466_);
    return v_res_4473_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Try_Collector_visit_spec__1_spec__1___redArg(
    mut v_a_4474_: *mut leanh::LeanObject,
    mut v_x_4475_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_4476_: u8 = 0;
    let mut v_key_4477_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_4478_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4479_: usize = 0;
    let mut v___x_4480_: usize = 0;
    let mut v___x_4481_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_4475_) == 0 {
                    v___x_4476_ = 0;
                    return v___x_4476_;
                } else {
                    v_key_4477_ = leanh::lean_ctor_get(v_x_4475_, 0);
                    v_tail_4478_ = leanh::lean_ctor_get(v_x_4475_, 2);
                    v___x_4479_ = lean_ptr_addr(v_key_4477_);
                    v___x_4480_ = lean_ptr_addr(v_a_4474_);
                    v___x_4481_ = lean_usize_dec_eq(v___x_4479_, v___x_4480_);
                    if v___x_4481_ == 0 {
                        v_x_4475_ = v_tail_4478_;
                        state = 0;
                        continue;
                    } else {
                        return v___x_4481_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Try_Collector_visit_spec__1_spec__1___redArg___boxed(
    mut v_a_4483_: *mut leanh::LeanObject,
    mut v_x_4484_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4485_: u8 = 0;
    let mut v_r_4486_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4485_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Try_Collector_visit_spec__1_spec__1___redArg(v_a_4483_, v_x_4484_);
    leanh::lean_dec(v_x_4484_);
    leanh::lean_dec_ref(v_a_4483_);
    v_r_4486_ = leanh::lean_box((v_res_4485_) as usize);
    return v_r_4486_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Try_Collector_visit_spec__1___redArg(
    mut v_m_4487_: *mut leanh::LeanObject,
    mut v_a_4488_: *mut leanh::LeanObject,
) -> u8 {
    let mut v_buckets_4489_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4490_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4491_: usize = 0;
    let mut v___x_4492_: u64 = 0;
    let mut v___x_4493_: u64 = 0;
    let mut v___x_4494_: u64 = 0;
    let mut v___x_4495_: u64 = 0;
    let mut v___x_4496_: u64 = 0;
    let mut v_fold_4497_: u64 = 0;
    let mut v___x_4498_: u64 = 0;
    let mut v___x_4499_: u64 = 0;
    let mut v___x_4500_: u64 = 0;
    let mut v___x_4501_: usize = 0;
    let mut v___x_4502_: usize = 0;
    let mut v___x_4503_: usize = 0;
    let mut v___x_4504_: usize = 0;
    let mut v___x_4505_: usize = 0;
    let mut v___x_4506_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4507_: u8 = 0;
    v_buckets_4489_ = leanh::lean_ctor_get(v_m_4487_, 1);
    v___x_4490_ = lean_array_get_size(v_buckets_4489_);
    v___x_4491_ = lean_ptr_addr(v_a_4488_);
    v___x_4492_ = lean_usize_to_uint64(v___x_4491_);
    v___x_4493_ = 11u64;
    v___x_4494_ = lean_uint64_mix_hash(v___x_4492_, v___x_4493_);
    v___x_4495_ = 32u64;
    v___x_4496_ = lean_uint64_shift_right(v___x_4494_, v___x_4495_);
    v_fold_4497_ = lean_uint64_xor(v___x_4494_, v___x_4496_);
    v___x_4498_ = 16u64;
    v___x_4499_ = lean_uint64_shift_right(v_fold_4497_, v___x_4498_);
    v___x_4500_ = lean_uint64_xor(v_fold_4497_, v___x_4499_);
    v___x_4501_ = lean_uint64_to_usize(v___x_4500_);
    v___x_4502_ = lean_usize_of_nat(v___x_4490_);
    v___x_4503_ = 1usize;
    v___x_4504_ = lean_usize_sub(v___x_4502_, v___x_4503_);
    v___x_4505_ = lean_usize_land(v___x_4501_, v___x_4504_);
    v___x_4506_ = lean_array_uget_borrowed(v_buckets_4489_, v___x_4505_);
    v___x_4507_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Try_Collector_visit_spec__1_spec__1___redArg(v_a_4488_, v___x_4506_);
    return v___x_4507_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Try_Collector_visit_spec__1___redArg___boxed(
    mut v_m_4508_: *mut leanh::LeanObject,
    mut v_a_4509_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4510_: u8 = 0;
    let mut v_r_4511_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4510_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Try_Collector_visit_spec__1___redArg(v_m_4508_, v_a_4509_);
    leanh::lean_dec_ref(v_a_4509_);
    leanh::lean_dec_ref(v_m_4508_);
    v_r_4511_ = leanh::lean_box((v_res_4510_) as usize);
    return v_r_4511_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Try_Collector_visit_spec__2_spec__3_spec__4_spec__6___redArg(
    mut v_x_4512_: *mut leanh::LeanObject,
    mut v_x_4513_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_key_4514_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_4515_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_4516_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4518_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4519_: u8 = 0;
    let mut v___x_4520_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4521_: usize = 0;
    let mut v___x_4522_: u64 = 0;
    let mut v___x_4523_: u64 = 0;
    let mut v___x_4524_: u64 = 0;
    let mut v___x_4525_: u64 = 0;
    let mut v___x_4526_: u64 = 0;
    let mut v_fold_4527_: u64 = 0;
    let mut v___x_4528_: u64 = 0;
    let mut v___x_4529_: u64 = 0;
    let mut v___x_4530_: u64 = 0;
    let mut v___x_4531_: usize = 0;
    let mut v___x_4532_: usize = 0;
    let mut v___x_4533_: usize = 0;
    let mut v___x_4534_: usize = 0;
    let mut v___x_4535_: usize = 0;
    let mut v___x_4536_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4538_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4539_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4541_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4542_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_4513_) == 0 {
                    return v_x_4512_;
                } else {
                    v_key_4514_ = leanh::lean_ctor_get(v_x_4513_, 0);
                    v_value_4515_ = leanh::lean_ctor_get(v_x_4513_, 1);
                    v_tail_4516_ = leanh::lean_ctor_get(v_x_4513_, 2);
                    v_isSharedCheck_4542_ = (!leanh::lean_is_exclusive(v_x_4513_)) as u8;
                    if v_isSharedCheck_4542_ == 0 {
                        v___x_4518_ = v_x_4513_;
                        v_isShared_4519_ = v_isSharedCheck_4542_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_tail_4516_);
                        leanh::lean_inc(v_value_4515_);
                        leanh::lean_inc(v_key_4514_);
                        leanh::lean_dec(v_x_4513_);
                        v___x_4518_ = leanh::lean_box(0);
                        v_isShared_4519_ = v_isSharedCheck_4542_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_4520_ = lean_array_get_size(v_x_4512_);
                v___x_4521_ = lean_ptr_addr(v_key_4514_);
                v___x_4522_ = lean_usize_to_uint64(v___x_4521_);
                v___x_4523_ = 11u64;
                v___x_4524_ = lean_uint64_mix_hash(v___x_4522_, v___x_4523_);
                v___x_4525_ = 32u64;
                v___x_4526_ = lean_uint64_shift_right(v___x_4524_, v___x_4525_);
                v_fold_4527_ = lean_uint64_xor(v___x_4524_, v___x_4526_);
                v___x_4528_ = 16u64;
                v___x_4529_ = lean_uint64_shift_right(v_fold_4527_, v___x_4528_);
                v___x_4530_ = lean_uint64_xor(v_fold_4527_, v___x_4529_);
                v___x_4531_ = lean_uint64_to_usize(v___x_4530_);
                v___x_4532_ = lean_usize_of_nat(v___x_4520_);
                v___x_4533_ = 1usize;
                v___x_4534_ = lean_usize_sub(v___x_4532_, v___x_4533_);
                v___x_4535_ = lean_usize_land(v___x_4531_, v___x_4534_);
                v___x_4536_ = lean_array_uget_borrowed(v_x_4512_, v___x_4535_);
                leanh::lean_inc(v___x_4536_);
                if v_isShared_4519_ == 0 {
                    leanh::lean_ctor_set(v___x_4518_, 2, v___x_4536_);
                    v___x_4538_ = v___x_4518_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4541_ = leanh::lean_alloc_ctor(1, 3, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4541_, 0, v_key_4514_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4541_, 1, v_value_4515_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4541_, 2, v___x_4536_);
                    v___x_4538_ = v_reuseFailAlloc_4541_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_4539_ = lean_array_uset(v_x_4512_, v___x_4535_, v___x_4538_);
                v_x_4512_ = v___x_4539_;
                v_x_4513_ = v_tail_4516_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Try_Collector_visit_spec__2_spec__3_spec__4___redArg(
    mut v_i_4543_: *mut leanh::LeanObject,
    mut v_source_4544_: *mut leanh::LeanObject,
    mut v_target_4545_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4546_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4547_: u8 = 0;
    let mut v_es_4548_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4549_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_source_4550_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_target_4551_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4552_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4553_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4546_ = lean_array_get_size(v_source_4544_);
                v___x_4547_ = lean_nat_dec_lt(v_i_4543_, v___x_4546_);
                if v___x_4547_ == 0 {
                    leanh::lean_dec_ref(v_source_4544_);
                    leanh::lean_dec(v_i_4543_);
                    return v_target_4545_;
                } else {
                    v_es_4548_ = lean_array_fget(v_source_4544_, v_i_4543_);
                    v___x_4549_ = leanh::lean_box(0);
                    v_source_4550_ = lean_array_fset(v_source_4544_, v_i_4543_, v___x_4549_);
                    v_target_4551_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Try_Collector_visit_spec__2_spec__3_spec__4_spec__6___redArg(v_target_4545_, v_es_4548_);
                    v___x_4552_ = leanh::lean_unsigned_to_nat(1);
                    v___x_4553_ = lean_nat_add(v_i_4543_, v___x_4552_);
                    leanh::lean_dec(v_i_4543_);
                    v_i_4543_ = v___x_4553_;
                    v_source_4544_ = v_source_4550_;
                    v_target_4545_ = v_target_4551_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Try_Collector_visit_spec__2_spec__3___redArg(
    mut v_data_4555_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4556_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4557_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_nbuckets_4558_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4559_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4560_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4561_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4562_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4556_ = lean_array_get_size(v_data_4555_);
    v___x_4557_ = leanh::lean_unsigned_to_nat(2);
    v_nbuckets_4558_ = lean_nat_mul(v___x_4556_, v___x_4557_);
    v___x_4559_ = leanh::lean_unsigned_to_nat(0);
    v___x_4560_ = leanh::lean_box(0);
    v___x_4561_ = lean_mk_array(v_nbuckets_4558_, v___x_4560_);
    v___x_4562_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Try_Collector_visit_spec__2_spec__3_spec__4___redArg(v___x_4559_, v_data_4555_, v___x_4561_);
    return v___x_4562_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Try_Collector_visit_spec__2___redArg(
    mut v_m_4563_: *mut leanh::LeanObject,
    mut v_a_4564_: *mut leanh::LeanObject,
    mut v_b_4565_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_size_4566_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_4567_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4568_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4569_: usize = 0;
    let mut v___x_4570_: u64 = 0;
    let mut v___x_4571_: u64 = 0;
    let mut v___x_4572_: u64 = 0;
    let mut v___x_4573_: u64 = 0;
    let mut v___x_4574_: u64 = 0;
    let mut v_fold_4575_: u64 = 0;
    let mut v___x_4576_: u64 = 0;
    let mut v___x_4577_: u64 = 0;
    let mut v___x_4578_: u64 = 0;
    let mut v___x_4579_: usize = 0;
    let mut v___x_4580_: usize = 0;
    let mut v___x_4581_: usize = 0;
    let mut v___x_4582_: usize = 0;
    let mut v___x_4583_: usize = 0;
    let mut v_bkt_4584_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4585_: u8 = 0;
    let mut v___x_4587_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4588_: u8 = 0;
    let mut v___x_4589_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_x27_4590_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4591_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_x27_4592_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4593_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4594_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4595_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4596_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4597_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4598_: u8 = 0;
    let mut v_val_4599_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4601_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4602_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4604_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4605_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4606_: u8 = 0;
    let mut v_unused_4607_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_4608_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_size_4566_ = leanh::lean_ctor_get(v_m_4563_, 0);
                v_buckets_4567_ = leanh::lean_ctor_get(v_m_4563_, 1);
                v___x_4568_ = lean_array_get_size(v_buckets_4567_);
                v___x_4569_ = lean_ptr_addr(v_a_4564_);
                v___x_4570_ = lean_usize_to_uint64(v___x_4569_);
                v___x_4571_ = 11u64;
                v___x_4572_ = lean_uint64_mix_hash(v___x_4570_, v___x_4571_);
                v___x_4573_ = 32u64;
                v___x_4574_ = lean_uint64_shift_right(v___x_4572_, v___x_4573_);
                v_fold_4575_ = lean_uint64_xor(v___x_4572_, v___x_4574_);
                v___x_4576_ = 16u64;
                v___x_4577_ = lean_uint64_shift_right(v_fold_4575_, v___x_4576_);
                v___x_4578_ = lean_uint64_xor(v_fold_4575_, v___x_4577_);
                v___x_4579_ = lean_uint64_to_usize(v___x_4578_);
                v___x_4580_ = lean_usize_of_nat(v___x_4568_);
                v___x_4581_ = 1usize;
                v___x_4582_ = lean_usize_sub(v___x_4580_, v___x_4581_);
                v___x_4583_ = lean_usize_land(v___x_4579_, v___x_4582_);
                v_bkt_4584_ = lean_array_uget_borrowed(v_buckets_4567_, v___x_4583_);
                v___x_4585_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Try_Collector_visit_spec__1_spec__1___redArg(v_a_4564_, v_bkt_4584_);
                if v___x_4585_ == 0 {
                    leanh::lean_inc_ref(v_buckets_4567_);
                    leanh::lean_inc(v_size_4566_);
                    v_isSharedCheck_4606_ = (!leanh::lean_is_exclusive(v_m_4563_)) as u8;
                    if v_isSharedCheck_4606_ == 0 {
                        v_unused_4607_ = leanh::lean_ctor_get(v_m_4563_, 1);
                        leanh::lean_dec(v_unused_4607_);
                        v_unused_4608_ = leanh::lean_ctor_get(v_m_4563_, 0);
                        leanh::lean_dec(v_unused_4608_);
                        v___x_4587_ = v_m_4563_;
                        v_isShared_4588_ = v_isSharedCheck_4606_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_dec(v_m_4563_);
                        v___x_4587_ = leanh::lean_box(0);
                        v_isShared_4588_ = v_isSharedCheck_4606_;
                        state = 1;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v_b_4565_);
                    leanh::lean_dec_ref(v_a_4564_);
                    return v_m_4563_;
                }
            }
            1 => {
                v___x_4589_ = leanh::lean_unsigned_to_nat(1);
                v_size_x27_4590_ = lean_nat_add(v_size_4566_, v___x_4589_);
                leanh::lean_dec(v_size_4566_);
                leanh::lean_inc(v_bkt_4584_);
                v___x_4591_ = leanh::lean_alloc_ctor(1, 3, (0) as u32);
                leanh::lean_ctor_set(v___x_4591_, 0, v_a_4564_);
                leanh::lean_ctor_set(v___x_4591_, 1, v_b_4565_);
                leanh::lean_ctor_set(v___x_4591_, 2, v_bkt_4584_);
                v_buckets_x27_4592_ = lean_array_uset(v_buckets_4567_, v___x_4583_, v___x_4591_);
                v___x_4593_ = leanh::lean_unsigned_to_nat(4);
                v___x_4594_ = lean_nat_mul(v_size_x27_4590_, v___x_4593_);
                v___x_4595_ = leanh::lean_unsigned_to_nat(3);
                v___x_4596_ = lean_nat_div(v___x_4594_, v___x_4595_);
                leanh::lean_dec(v___x_4594_);
                v___x_4597_ = lean_array_get_size(v_buckets_x27_4592_);
                v___x_4598_ = lean_nat_dec_le(v___x_4596_, v___x_4597_);
                leanh::lean_dec(v___x_4596_);
                if v___x_4598_ == 0 {
                    v_val_4599_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Try_Collector_visit_spec__2_spec__3___redArg(v_buckets_x27_4592_);
                    if v_isShared_4588_ == 0 {
                        leanh::lean_ctor_set(v___x_4587_, 1, v_val_4599_);
                        leanh::lean_ctor_set(v___x_4587_, 0, v_size_x27_4590_);
                        v___x_4601_ = v___x_4587_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_4602_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_4602_, 0, v_size_x27_4590_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_4602_, 1, v_val_4599_);
                        v___x_4601_ = v_reuseFailAlloc_4602_;
                        state = 2;
                        continue;
                    }
                } else {
                    if v_isShared_4588_ == 0 {
                        leanh::lean_ctor_set(v___x_4587_, 1, v_buckets_x27_4592_);
                        leanh::lean_ctor_set(v___x_4587_, 0, v_size_x27_4590_);
                        v___x_4604_ = v___x_4587_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_4605_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_4605_, 0, v_size_x27_4590_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_4605_, 1, v_buckets_x27_4592_);
                        v___x_4604_ = v_reuseFailAlloc_4605_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_4601_;
            }
            3 => {
                return v___x_4604_;
            }
            _ => {}
        }
    }
}
pub unsafe fn _init_l_Lean_Meta_Try_Collector_visit___closed__0() -> *mut leanh::LeanObject {
    let mut v___x_4609_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_dummy_4610_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4609_ = leanh::lean_box(0);
    v_dummy_4610_ = l_Lean_Expr_sort___override(v___x_4609_);
    return v_dummy_4610_;
}
pub unsafe fn l_Lean_Expr_withAppAux___at___00Lean_Meta_Try_Collector_visit_spec__3(
    mut v_e_4611_: *mut leanh::LeanObject,
    mut v_x_4612_: *mut leanh::LeanObject,
    mut v_x_4613_: *mut leanh::LeanObject,
    mut v_x_4614_: *mut leanh::LeanObject,
    mut v___y_4615_: *mut leanh::LeanObject,
    mut v___y_4616_: *mut leanh::LeanObject,
    mut v___y_4617_: *mut leanh::LeanObject,
    mut v___y_4618_: *mut leanh::LeanObject,
    mut v___y_4619_: *mut leanh::LeanObject,
    mut v___y_4620_: *mut leanh::LeanObject,
    mut v___y_4621_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___y_4624_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4625_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4626_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4627_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4628_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4629_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4630_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4631_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4632_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4633_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4634_: u8 = 0;
    let mut v___x_4635_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4636_: u8 = 0;
    let mut v___x_4637_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4638_: usize = 0;
    let mut v___x_4639_: usize = 0;
    let mut v___x_4640_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4641_: usize = 0;
    let mut v___x_4642_: usize = 0;
    let mut v___x_4643_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fn_4644_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_arg_4645_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4646_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4647_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4648_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_declName_4650_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4651_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4652_: u8 = 0;
    let mut v___x_4653_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4654_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_4612_) == 5 {
                    v_fn_4644_ = leanh::lean_ctor_get(v_x_4612_, 0);
                    leanh::lean_inc_ref(v_fn_4644_);
                    v_arg_4645_ = leanh::lean_ctor_get(v_x_4612_, 1);
                    leanh::lean_inc_ref(v_arg_4645_);
                    leanh::lean_dec_ref_known(v_x_4612_, 2);
                    v___x_4646_ = lean_array_set(v_x_4613_, v_x_4614_, v_arg_4645_);
                    v___x_4647_ = leanh::lean_unsigned_to_nat(1);
                    v___x_4648_ = lean_nat_sub(v_x_4614_, v___x_4647_);
                    leanh::lean_dec(v_x_4614_);
                    v_x_4612_ = v_fn_4644_;
                    v_x_4613_ = v___x_4646_;
                    v_x_4614_ = v___x_4648_;
                    state = 0;
                    continue;
                } else {
                    leanh::lean_dec(v_x_4614_);
                    if leanh::lean_obj_tag(v_x_4612_) == 4 {
                        v_declName_4650_ = leanh::lean_ctor_get(v_x_4612_, 0);
                        leanh::lean_inc_n(v_declName_4650_, 2);
                        leanh::lean_dec_ref_known(v_x_4612_, 2);
                        v___x_4651_ = l_Lean_Meta_Try_Collector_saveConst___redArg(
                            v_declName_4650_,
                            v___y_4617_,
                        );
                        leanh::lean_dec_ref(v___x_4651_);
                        v___x_4652_ = l_Lean_Expr_hasLooseBVars(v_e_4611_);
                        if v___x_4652_ == 0 {
                            v___x_4653_ = l_Lean_Meta_Try_Collector_visitApp(
                                v_e_4611_,
                                v_declName_4650_,
                                v_x_4613_,
                                v___y_4616_,
                                v___y_4617_,
                                v___y_4618_,
                                v___y_4619_,
                                v___y_4620_,
                                v___y_4621_,
                            );
                            if leanh::lean_obj_tag(v___x_4653_) == 0 {
                                leanh::lean_dec_ref_known(v___x_4653_, 1);
                                v___y_4624_ = v___y_4615_;
                                v___y_4625_ = v___y_4616_;
                                v___y_4626_ = v___y_4617_;
                                v___y_4627_ = v___y_4618_;
                                v___y_4628_ = v___y_4619_;
                                v___y_4629_ = v___y_4620_;
                                v___y_4630_ = v___y_4621_;
                                state = 1;
                                continue;
                            } else {
                                leanh::lean_dec_ref(v_x_4613_);
                                return v___x_4653_;
                            }
                        } else {
                            leanh::lean_dec(v_declName_4650_);
                            leanh::lean_dec_ref(v_e_4611_);
                            v___y_4624_ = v___y_4615_;
                            v___y_4625_ = v___y_4616_;
                            v___y_4626_ = v___y_4617_;
                            v___y_4627_ = v___y_4618_;
                            v___y_4628_ = v___y_4619_;
                            v___y_4629_ = v___y_4620_;
                            v___y_4630_ = v___y_4621_;
                            state = 1;
                            continue;
                        }
                    } else {
                        leanh::lean_dec_ref(v_e_4611_);
                        v___x_4654_ = l_Lean_Meta_Try_Collector_visit(
                            v_x_4612_,
                            v___y_4615_,
                            v___y_4616_,
                            v___y_4617_,
                            v___y_4618_,
                            v___y_4619_,
                            v___y_4620_,
                            v___y_4621_,
                        );
                        if leanh::lean_obj_tag(v___x_4654_) == 0 {
                            leanh::lean_dec_ref_known(v___x_4654_, 1);
                            v___y_4624_ = v___y_4615_;
                            v___y_4625_ = v___y_4616_;
                            v___y_4626_ = v___y_4617_;
                            v___y_4627_ = v___y_4618_;
                            v___y_4628_ = v___y_4619_;
                            v___y_4629_ = v___y_4620_;
                            v___y_4630_ = v___y_4621_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_dec_ref(v_x_4613_);
                            return v___x_4654_;
                        }
                    }
                }
            }
            1 => {
                v___x_4631_ = leanh::lean_unsigned_to_nat(0);
                v___x_4632_ = lean_array_get_size(v_x_4613_);
                v___x_4633_ = leanh::lean_box(0);
                v___x_4634_ = lean_nat_dec_lt(v___x_4631_, v___x_4632_);
                if v___x_4634_ == 0 {
                    leanh::lean_dec_ref(v_x_4613_);
                    v___x_4635_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_4635_, 0, v___x_4633_);
                    return v___x_4635_;
                } else {
                    v___x_4636_ = lean_nat_dec_le(v___x_4632_, v___x_4632_);
                    if v___x_4636_ == 0 {
                        if v___x_4634_ == 0 {
                            leanh::lean_dec_ref(v_x_4613_);
                            v___x_4637_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                            leanh::lean_ctor_set(v___x_4637_, 0, v___x_4633_);
                            return v___x_4637_;
                        } else {
                            v___x_4638_ = 0usize;
                            v___x_4639_ = lean_usize_of_nat(v___x_4632_);
                            v___x_4640_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Try_Collector_visit_spec__0(v_x_4613_, v___x_4638_, v___x_4639_, v___x_4633_, v___y_4624_, v___y_4625_, v___y_4626_, v___y_4627_, v___y_4628_, v___y_4629_, v___y_4630_);
                            leanh::lean_dec_ref(v_x_4613_);
                            return v___x_4640_;
                        }
                    } else {
                        v___x_4641_ = 0usize;
                        v___x_4642_ = lean_usize_of_nat(v___x_4632_);
                        v___x_4643_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Try_Collector_visit_spec__0(v_x_4613_, v___x_4641_, v___x_4642_, v___x_4633_, v___y_4624_, v___y_4625_, v___y_4626_, v___y_4627_, v___y_4628_, v___y_4629_, v___y_4630_);
                        leanh::lean_dec_ref(v_x_4613_);
                        return v___x_4643_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Try_Collector_visit(
    mut v_e_4655_: *mut leanh::LeanObject,
    mut v_a_4656_: *mut leanh::LeanObject,
    mut v_a_4657_: *mut leanh::LeanObject,
    mut v_a_4658_: *mut leanh::LeanObject,
    mut v_a_4659_: *mut leanh::LeanObject,
    mut v_a_4660_: *mut leanh::LeanObject,
    mut v_a_4661_: *mut leanh::LeanObject,
    mut v_a_4662_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4664_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4665_: u8 = 0;
    let mut v___x_4666_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4667_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4668_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4669_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_d_4671_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_b_4672_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4673_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4674_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4675_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4676_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4677_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4678_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4679_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4680_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_declName_4682_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4683_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_binderType_4684_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_body_4685_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_binderType_4686_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_body_4687_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_expr_4688_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_type_4690_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_4691_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_body_4692_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4693_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4694_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_dummy_4696_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_nargs_4697_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4698_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4699_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4700_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4701_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_struct_4702_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4704_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4705_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4706_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4664_ = lean_st_ref_get(v_a_4656_);
                v___x_4665_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Try_Collector_visit_spec__1___redArg(v___x_4664_, v_e_4655_);
                leanh::lean_dec(v___x_4664_);
                if v___x_4665_ == 0 {
                    v___x_4666_ = lean_st_ref_take(v_a_4656_);
                    v___x_4667_ = leanh::lean_box(0);
                    leanh::lean_inc_ref(v_e_4655_);
                    v___x_4668_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Try_Collector_visit_spec__2___redArg(v___x_4666_, v_e_4655_, v___x_4667_);
                    v___x_4669_ = lean_st_ref_set(v_a_4656_, v___x_4668_);
                    match leanh::lean_obj_tag(v_e_4655_) {
                        4 => {
                            v_declName_4682_ = leanh::lean_ctor_get(v_e_4655_, 0);
                            leanh::lean_inc(v_declName_4682_);
                            leanh::lean_dec_ref_known(v_e_4655_, 2);
                            v___x_4683_ = l_Lean_Meta_Try_Collector_visitConst___redArg(
                                v_declName_4682_,
                                v_a_4657_,
                                v_a_4658_,
                                v_a_4661_,
                                v_a_4662_,
                            );
                            return v___x_4683_;
                        }
                        7 => {
                            v_binderType_4684_ = leanh::lean_ctor_get(v_e_4655_, 1);
                            leanh::lean_inc_ref(v_binderType_4684_);
                            v_body_4685_ = leanh::lean_ctor_get(v_e_4655_, 2);
                            leanh::lean_inc_ref(v_body_4685_);
                            leanh::lean_dec_ref_known(v_e_4655_, 3);
                            v_d_4671_ = v_binderType_4684_;
                            v_b_4672_ = v_body_4685_;
                            v___y_4673_ = v_a_4656_;
                            v___y_4674_ = v_a_4657_;
                            v___y_4675_ = v_a_4658_;
                            v___y_4676_ = v_a_4659_;
                            v___y_4677_ = v_a_4660_;
                            v___y_4678_ = v_a_4661_;
                            v___y_4679_ = v_a_4662_;
                            state = 1;
                            continue;
                        }
                        6 => {
                            v_binderType_4686_ = leanh::lean_ctor_get(v_e_4655_, 1);
                            leanh::lean_inc_ref(v_binderType_4686_);
                            v_body_4687_ = leanh::lean_ctor_get(v_e_4655_, 2);
                            leanh::lean_inc_ref(v_body_4687_);
                            leanh::lean_dec_ref_known(v_e_4655_, 3);
                            v_d_4671_ = v_binderType_4686_;
                            v_b_4672_ = v_body_4687_;
                            v___y_4673_ = v_a_4656_;
                            v___y_4674_ = v_a_4657_;
                            v___y_4675_ = v_a_4658_;
                            v___y_4676_ = v_a_4659_;
                            v___y_4677_ = v_a_4660_;
                            v___y_4678_ = v_a_4661_;
                            v___y_4679_ = v_a_4662_;
                            state = 1;
                            continue;
                        }
                        10 => {
                            v_expr_4688_ = leanh::lean_ctor_get(v_e_4655_, 1);
                            leanh::lean_inc_ref(v_expr_4688_);
                            leanh::lean_dec_ref_known(v_e_4655_, 2);
                            v_e_4655_ = v_expr_4688_;
                            state = 0;
                            continue;
                        }
                        8 => {
                            v_type_4690_ = leanh::lean_ctor_get(v_e_4655_, 1);
                            leanh::lean_inc_ref(v_type_4690_);
                            v_value_4691_ = leanh::lean_ctor_get(v_e_4655_, 2);
                            leanh::lean_inc_ref(v_value_4691_);
                            v_body_4692_ = leanh::lean_ctor_get(v_e_4655_, 3);
                            leanh::lean_inc_ref(v_body_4692_);
                            leanh::lean_dec_ref_known(v_e_4655_, 4);
                            v___x_4693_ = l_Lean_Meta_Try_Collector_visit(
                                v_type_4690_,
                                v_a_4656_,
                                v_a_4657_,
                                v_a_4658_,
                                v_a_4659_,
                                v_a_4660_,
                                v_a_4661_,
                                v_a_4662_,
                            );
                            if leanh::lean_obj_tag(v___x_4693_) == 0 {
                                leanh::lean_dec_ref_known(v___x_4693_, 1);
                                v___x_4694_ = l_Lean_Meta_Try_Collector_visit(
                                    v_value_4691_,
                                    v_a_4656_,
                                    v_a_4657_,
                                    v_a_4658_,
                                    v_a_4659_,
                                    v_a_4660_,
                                    v_a_4661_,
                                    v_a_4662_,
                                );
                                if leanh::lean_obj_tag(v___x_4694_) == 0 {
                                    leanh::lean_dec_ref_known(v___x_4694_, 1);
                                    v_e_4655_ = v_body_4692_;
                                    state = 0;
                                    continue;
                                } else {
                                    leanh::lean_dec_ref(v_body_4692_);
                                    return v___x_4694_;
                                }
                            } else {
                                leanh::lean_dec_ref(v_body_4692_);
                                leanh::lean_dec_ref(v_value_4691_);
                                return v___x_4693_;
                            }
                        }
                        5 => {
                            v_dummy_4696_ = leanh::lean_obj_once(
                                core::ptr::addr_of_mut!(
                                    l_Lean_Meta_Try_Collector_visit___closed__0
                                ),
                                core::ptr::addr_of_mut!(
                                    l_Lean_Meta_Try_Collector_visit___closed__0_once
                                ),
                                _init_l_Lean_Meta_Try_Collector_visit___closed__0,
                            );
                            v_nargs_4697_ = l_Lean_Expr_getAppNumArgs(v_e_4655_);
                            leanh::lean_inc(v_nargs_4697_);
                            v___x_4698_ = lean_mk_array(v_nargs_4697_, v_dummy_4696_);
                            v___x_4699_ = leanh::lean_unsigned_to_nat(1);
                            v___x_4700_ = lean_nat_sub(v_nargs_4697_, v___x_4699_);
                            leanh::lean_dec(v_nargs_4697_);
                            leanh::lean_inc_ref(v_e_4655_);
                            v___x_4701_ = l_Lean_Expr_withAppAux___at___00Lean_Meta_Try_Collector_visit_spec__3(v_e_4655_, v_e_4655_, v___x_4698_, v___x_4700_, v_a_4656_, v_a_4657_, v_a_4658_, v_a_4659_, v_a_4660_, v_a_4661_, v_a_4662_);
                            return v___x_4701_;
                        }
                        11 => {
                            v_struct_4702_ = leanh::lean_ctor_get(v_e_4655_, 2);
                            leanh::lean_inc_ref(v_struct_4702_);
                            leanh::lean_dec_ref_known(v_e_4655_, 3);
                            v_e_4655_ = v_struct_4702_;
                            state = 0;
                            continue;
                        }
                        _ => {
                            leanh::lean_dec_ref(v_e_4655_);
                            v___x_4704_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                            leanh::lean_ctor_set(v___x_4704_, 0, v___x_4667_);
                            return v___x_4704_;
                        }
                    }
                } else {
                    leanh::lean_dec_ref(v_e_4655_);
                    v___x_4705_ = leanh::lean_box(0);
                    v___x_4706_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_4706_, 0, v___x_4705_);
                    return v___x_4706_;
                }
            }
            1 => {
                v___x_4680_ = l_Lean_Meta_Try_Collector_visit(
                    v_d_4671_,
                    v___y_4673_,
                    v___y_4674_,
                    v___y_4675_,
                    v___y_4676_,
                    v___y_4677_,
                    v___y_4678_,
                    v___y_4679_,
                );
                if leanh::lean_obj_tag(v___x_4680_) == 0 {
                    leanh::lean_dec_ref_known(v___x_4680_, 1);
                    v_e_4655_ = v_b_4672_;
                    v_a_4656_ = v___y_4673_;
                    v_a_4657_ = v___y_4674_;
                    v_a_4658_ = v___y_4675_;
                    v_a_4659_ = v___y_4676_;
                    v_a_4660_ = v___y_4677_;
                    v_a_4661_ = v___y_4678_;
                    v_a_4662_ = v___y_4679_;
                    state = 0;
                    continue;
                } else {
                    leanh::lean_dec_ref(v_b_4672_);
                    return v___x_4680_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Try_Collector_visit_spec__0(
    mut v_as_4707_: *mut leanh::LeanObject,
    mut v_i_4708_: usize,
    mut v_stop_4709_: usize,
    mut v_b_4710_: *mut leanh::LeanObject,
    mut v___y_4711_: *mut leanh::LeanObject,
    mut v___y_4712_: *mut leanh::LeanObject,
    mut v___y_4713_: *mut leanh::LeanObject,
    mut v___y_4714_: *mut leanh::LeanObject,
    mut v___y_4715_: *mut leanh::LeanObject,
    mut v___y_4716_: *mut leanh::LeanObject,
    mut v___y_4717_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4719_: u8 = 0;
    let mut v___x_4720_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4721_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4722_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4723_: usize = 0;
    let mut v___x_4724_: usize = 0;
    let mut v___x_4726_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4719_ = lean_usize_dec_eq(v_i_4708_, v_stop_4709_);
                if v___x_4719_ == 0 {
                    v___x_4720_ = lean_array_uget_borrowed(v_as_4707_, v_i_4708_);
                    leanh::lean_inc(v___x_4720_);
                    v___x_4721_ = l_Lean_Meta_Try_Collector_visit(
                        v___x_4720_,
                        v___y_4711_,
                        v___y_4712_,
                        v___y_4713_,
                        v___y_4714_,
                        v___y_4715_,
                        v___y_4716_,
                        v___y_4717_,
                    );
                    if leanh::lean_obj_tag(v___x_4721_) == 0 {
                        v_a_4722_ = leanh::lean_ctor_get(v___x_4721_, 0);
                        leanh::lean_inc(v_a_4722_);
                        leanh::lean_dec_ref_known(v___x_4721_, 1);
                        v___x_4723_ = 1usize;
                        v___x_4724_ = lean_usize_add(v_i_4708_, v___x_4723_);
                        v_i_4708_ = v___x_4724_;
                        v_b_4710_ = v_a_4722_;
                        state = 0;
                        continue;
                    } else {
                        return v___x_4721_;
                    }
                } else {
                    v___x_4726_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_4726_, 0, v_b_4710_);
                    return v___x_4726_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Try_Collector_visit_spec__0___boxed(
    mut v_as_4727_: *mut leanh::LeanObject,
    mut v_i_4728_: *mut leanh::LeanObject,
    mut v_stop_4729_: *mut leanh::LeanObject,
    mut v_b_4730_: *mut leanh::LeanObject,
    mut v___y_4731_: *mut leanh::LeanObject,
    mut v___y_4732_: *mut leanh::LeanObject,
    mut v___y_4733_: *mut leanh::LeanObject,
    mut v___y_4734_: *mut leanh::LeanObject,
    mut v___y_4735_: *mut leanh::LeanObject,
    mut v___y_4736_: *mut leanh::LeanObject,
    mut v___y_4737_: *mut leanh::LeanObject,
    mut v___y_4738_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_i_boxed_4739_: usize = 0;
    let mut v_stop_boxed_4740_: usize = 0;
    let mut v_res_4741_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_4739_ = leanh::lean_unbox_usize(v_i_4728_);
    leanh::lean_dec(v_i_4728_);
    v_stop_boxed_4740_ = leanh::lean_unbox_usize(v_stop_4729_);
    leanh::lean_dec(v_stop_4729_);
    v_res_4741_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Try_Collector_visit_spec__0(v_as_4727_, v_i_boxed_4739_, v_stop_boxed_4740_, v_b_4730_, v___y_4731_, v___y_4732_, v___y_4733_, v___y_4734_, v___y_4735_, v___y_4736_, v___y_4737_);
    leanh::lean_dec(v___y_4737_);
    leanh::lean_dec_ref(v___y_4736_);
    leanh::lean_dec(v___y_4735_);
    leanh::lean_dec_ref(v___y_4734_);
    leanh::lean_dec(v___y_4733_);
    leanh::lean_dec_ref(v___y_4732_);
    leanh::lean_dec(v___y_4731_);
    leanh::lean_dec_ref(v_as_4727_);
    return v_res_4741_;
}
pub unsafe fn l_Lean_Expr_withAppAux___at___00Lean_Meta_Try_Collector_visit_spec__3___boxed(
    mut v_e_4742_: *mut leanh::LeanObject,
    mut v_x_4743_: *mut leanh::LeanObject,
    mut v_x_4744_: *mut leanh::LeanObject,
    mut v_x_4745_: *mut leanh::LeanObject,
    mut v___y_4746_: *mut leanh::LeanObject,
    mut v___y_4747_: *mut leanh::LeanObject,
    mut v___y_4748_: *mut leanh::LeanObject,
    mut v___y_4749_: *mut leanh::LeanObject,
    mut v___y_4750_: *mut leanh::LeanObject,
    mut v___y_4751_: *mut leanh::LeanObject,
    mut v___y_4752_: *mut leanh::LeanObject,
    mut v___y_4753_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4754_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4754_ = l_Lean_Expr_withAppAux___at___00Lean_Meta_Try_Collector_visit_spec__3(
        v_e_4742_,
        v_x_4743_,
        v_x_4744_,
        v_x_4745_,
        v___y_4746_,
        v___y_4747_,
        v___y_4748_,
        v___y_4749_,
        v___y_4750_,
        v___y_4751_,
        v___y_4752_,
    );
    leanh::lean_dec(v___y_4752_);
    leanh::lean_dec_ref(v___y_4751_);
    leanh::lean_dec(v___y_4750_);
    leanh::lean_dec_ref(v___y_4749_);
    leanh::lean_dec(v___y_4748_);
    leanh::lean_dec_ref(v___y_4747_);
    leanh::lean_dec(v___y_4746_);
    return v_res_4754_;
}
pub unsafe fn l_Lean_Meta_Try_Collector_visit___boxed(
    mut v_e_4755_: *mut leanh::LeanObject,
    mut v_a_4756_: *mut leanh::LeanObject,
    mut v_a_4757_: *mut leanh::LeanObject,
    mut v_a_4758_: *mut leanh::LeanObject,
    mut v_a_4759_: *mut leanh::LeanObject,
    mut v_a_4760_: *mut leanh::LeanObject,
    mut v_a_4761_: *mut leanh::LeanObject,
    mut v_a_4762_: *mut leanh::LeanObject,
    mut v_a_4763_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4764_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4764_ = l_Lean_Meta_Try_Collector_visit(
        v_e_4755_, v_a_4756_, v_a_4757_, v_a_4758_, v_a_4759_, v_a_4760_, v_a_4761_, v_a_4762_,
    );
    leanh::lean_dec(v_a_4762_);
    leanh::lean_dec_ref(v_a_4761_);
    leanh::lean_dec(v_a_4760_);
    leanh::lean_dec_ref(v_a_4759_);
    leanh::lean_dec(v_a_4758_);
    leanh::lean_dec_ref(v_a_4757_);
    leanh::lean_dec(v_a_4756_);
    return v_res_4764_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Try_Collector_visit_spec__1(
    mut v_00_u03b2_4765_: *mut leanh::LeanObject,
    mut v_m_4766_: *mut leanh::LeanObject,
    mut v_a_4767_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_4768_: u8 = 0;
    v___x_4768_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Try_Collector_visit_spec__1___redArg(v_m_4766_, v_a_4767_);
    return v___x_4768_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Try_Collector_visit_spec__1___boxed(
    mut v_00_u03b2_4769_: *mut leanh::LeanObject,
    mut v_m_4770_: *mut leanh::LeanObject,
    mut v_a_4771_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4772_: u8 = 0;
    let mut v_r_4773_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4772_ =
        l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Try_Collector_visit_spec__1(
            v_00_u03b2_4769_,
            v_m_4770_,
            v_a_4771_,
        );
    leanh::lean_dec_ref(v_a_4771_);
    leanh::lean_dec_ref(v_m_4770_);
    v_r_4773_ = leanh::lean_box((v_res_4772_) as usize);
    return v_r_4773_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Try_Collector_visit_spec__2(
    mut v_00_u03b2_4774_: *mut leanh::LeanObject,
    mut v_m_4775_: *mut leanh::LeanObject,
    mut v_a_4776_: *mut leanh::LeanObject,
    mut v_b_4777_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4778_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4778_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Try_Collector_visit_spec__2___redArg(v_m_4775_, v_a_4776_, v_b_4777_);
    return v___x_4778_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Try_Collector_visit_spec__1_spec__1(
    mut v_00_u03b2_4779_: *mut leanh::LeanObject,
    mut v_a_4780_: *mut leanh::LeanObject,
    mut v_x_4781_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_4782_: u8 = 0;
    v___x_4782_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Try_Collector_visit_spec__1_spec__1___redArg(v_a_4780_, v_x_4781_);
    return v___x_4782_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Try_Collector_visit_spec__1_spec__1___boxed(
    mut v_00_u03b2_4783_: *mut leanh::LeanObject,
    mut v_a_4784_: *mut leanh::LeanObject,
    mut v_x_4785_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4786_: u8 = 0;
    let mut v_r_4787_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4786_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Try_Collector_visit_spec__1_spec__1(v_00_u03b2_4783_, v_a_4784_, v_x_4785_);
    leanh::lean_dec(v_x_4785_);
    leanh::lean_dec_ref(v_a_4784_);
    v_r_4787_ = leanh::lean_box((v_res_4786_) as usize);
    return v_r_4787_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Try_Collector_visit_spec__2_spec__3(
    mut v_00_u03b2_4788_: *mut leanh::LeanObject,
    mut v_data_4789_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4790_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4790_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Try_Collector_visit_spec__2_spec__3___redArg(v_data_4789_);
    return v___x_4790_;
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Try_Collector_visit_spec__2_spec__3_spec__4(
    mut v_00_u03b2_4791_: *mut leanh::LeanObject,
    mut v_i_4792_: *mut leanh::LeanObject,
    mut v_source_4793_: *mut leanh::LeanObject,
    mut v_target_4794_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4795_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4795_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Try_Collector_visit_spec__2_spec__3_spec__4___redArg(v_i_4792_, v_source_4793_, v_target_4794_);
    return v___x_4795_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Try_Collector_visit_spec__2_spec__3_spec__4_spec__6(
    mut v_00_u03b2_4796_: *mut leanh::LeanObject,
    mut v_x_4797_: *mut leanh::LeanObject,
    mut v_x_4798_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4799_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4799_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Try_Collector_visit_spec__2_spec__3_spec__4_spec__6___redArg(v_x_4797_, v_x_4798_);
    return v___x_4799_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Try_Collect_0__Lean_Meta_Try_Collector_main_go_spec__0_spec__1_spec__4(
    mut v_as_4800_: *mut leanh::LeanObject,
    mut v_sz_4801_: usize,
    mut v_i_4802_: usize,
    mut v_b_4803_: *mut leanh::LeanObject,
    mut v___y_4804_: *mut leanh::LeanObject,
    mut v___y_4805_: *mut leanh::LeanObject,
    mut v___y_4806_: *mut leanh::LeanObject,
    mut v___y_4807_: *mut leanh::LeanObject,
    mut v___y_4808_: *mut leanh::LeanObject,
    mut v___y_4809_: *mut leanh::LeanObject,
    mut v___y_4810_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4812_: u8 = 0;
    let mut v___x_4813_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_4814_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4816_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4817_: u8 = 0;
    let mut v___x_4818_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4820_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4822_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4823_: usize = 0;
    let mut v___x_4824_: usize = 0;
    let mut v_reuseFailAlloc_4826_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4827_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_4828_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4829_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4830_: u8 = 0;
    let mut v___x_4831_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_4832_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4833_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4834_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4836_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4837_: u8 = 0;
    let mut v___x_4839_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4840_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4841_: u8 = 0;
    let mut v___x_4842_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4843_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4844_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4845_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4847_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4848_: u8 = 0;
    let mut v___x_4850_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4851_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4852_: u8 = 0;
    let mut v_a_4853_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4855_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4856_: u8 = 0;
    let mut v___x_4858_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4859_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4860_: u8 = 0;
    let mut v_isSharedCheck_4861_: u8 = 0;
    let mut v_unused_4862_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4812_ = lean_usize_dec_lt(v_i_4802_, v_sz_4801_);
                if v___x_4812_ == 0 {
                    v___x_4813_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_4813_, 0, v_b_4803_);
                    return v___x_4813_;
                } else {
                    v_snd_4814_ = leanh::lean_ctor_get(v_b_4803_, 1);
                    v_isSharedCheck_4861_ = (!leanh::lean_is_exclusive(v_b_4803_)) as u8;
                    if v_isSharedCheck_4861_ == 0 {
                        v_unused_4862_ = leanh::lean_ctor_get(v_b_4803_, 0);
                        leanh::lean_dec(v_unused_4862_);
                        v___x_4816_ = v_b_4803_;
                        v_isShared_4817_ = v_isSharedCheck_4861_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_snd_4814_);
                        leanh::lean_dec(v_b_4803_);
                        v___x_4816_ = leanh::lean_box(0);
                        v_isShared_4817_ = v_isSharedCheck_4861_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_4818_ = leanh::lean_box(0);
                v_a_4827_ = lean_array_uget_borrowed(v_as_4800_, v_i_4802_);
                if leanh::lean_obj_tag(v_a_4827_) == 0 {
                    v_a_4820_ = v_snd_4814_;
                    state = 2;
                    continue;
                } else {
                    leanh::lean_dec(v_snd_4814_);
                    v_val_4828_ = leanh::lean_ctor_get(v_a_4827_, 0);
                    v___x_4829_ = leanh::lean_box(0);
                    v___x_4830_ = l_Lean_LocalDecl_isAuxDecl(v_val_4828_);
                    if v___x_4830_ == 0 {
                        v___x_4831_ = l_Lean_LocalDecl_value_x3f(v_val_4828_, v___x_4830_);
                        if leanh::lean_obj_tag(v___x_4831_) == 1 {
                            v_val_4832_ = leanh::lean_ctor_get(v___x_4831_, 0);
                            leanh::lean_inc(v_val_4832_);
                            leanh::lean_dec_ref_known(v___x_4831_, 1);
                            v___x_4833_ = l_Lean_Meta_Try_Collector_visit(
                                v_val_4832_,
                                v___y_4804_,
                                v___y_4805_,
                                v___y_4806_,
                                v___y_4807_,
                                v___y_4808_,
                                v___y_4809_,
                                v___y_4810_,
                            );
                            if leanh::lean_obj_tag(v___x_4833_) == 0 {
                                leanh::lean_dec_ref_known(v___x_4833_, 1);
                                v_a_4820_ = v___x_4829_;
                                state = 2;
                                continue;
                            } else {
                                leanh::lean_del_object(v___x_4816_);
                                v_a_4834_ = leanh::lean_ctor_get(v___x_4833_, 0);
                                v_isSharedCheck_4841_ =
                                    (!leanh::lean_is_exclusive(v___x_4833_)) as u8;
                                if v_isSharedCheck_4841_ == 0 {
                                    v___x_4836_ = v___x_4833_;
                                    v_isShared_4837_ = v_isSharedCheck_4841_;
                                    state = 4;
                                    continue;
                                } else {
                                    leanh::lean_inc(v_a_4834_);
                                    leanh::lean_dec(v___x_4833_);
                                    v___x_4836_ = leanh::lean_box(0);
                                    v_isShared_4837_ = v_isSharedCheck_4841_;
                                    state = 4;
                                    continue;
                                }
                            }
                        } else {
                            leanh::lean_dec(v___x_4831_);
                            v___x_4842_ = l_Lean_Meta_Try_Collector_checkInductive(
                                v_val_4828_,
                                v___y_4805_,
                                v___y_4806_,
                                v___y_4807_,
                                v___y_4808_,
                                v___y_4809_,
                                v___y_4810_,
                            );
                            if leanh::lean_obj_tag(v___x_4842_) == 0 {
                                leanh::lean_dec_ref_known(v___x_4842_, 1);
                                v___x_4843_ = l_Lean_LocalDecl_type(v_val_4828_);
                                v___x_4844_ = l_Lean_Meta_Try_Collector_visit(
                                    v___x_4843_,
                                    v___y_4804_,
                                    v___y_4805_,
                                    v___y_4806_,
                                    v___y_4807_,
                                    v___y_4808_,
                                    v___y_4809_,
                                    v___y_4810_,
                                );
                                if leanh::lean_obj_tag(v___x_4844_) == 0 {
                                    leanh::lean_dec_ref_known(v___x_4844_, 1);
                                    v_a_4820_ = v___x_4829_;
                                    state = 2;
                                    continue;
                                } else {
                                    leanh::lean_del_object(v___x_4816_);
                                    v_a_4845_ = leanh::lean_ctor_get(v___x_4844_, 0);
                                    v_isSharedCheck_4852_ =
                                        (!leanh::lean_is_exclusive(v___x_4844_)) as u8;
                                    if v_isSharedCheck_4852_ == 0 {
                                        v___x_4847_ = v___x_4844_;
                                        v_isShared_4848_ = v_isSharedCheck_4852_;
                                        state = 6;
                                        continue;
                                    } else {
                                        leanh::lean_inc(v_a_4845_);
                                        leanh::lean_dec(v___x_4844_);
                                        v___x_4847_ = leanh::lean_box(0);
                                        v_isShared_4848_ = v_isSharedCheck_4852_;
                                        state = 6;
                                        continue;
                                    }
                                }
                            } else {
                                leanh::lean_del_object(v___x_4816_);
                                v_a_4853_ = leanh::lean_ctor_get(v___x_4842_, 0);
                                v_isSharedCheck_4860_ =
                                    (!leanh::lean_is_exclusive(v___x_4842_)) as u8;
                                if v_isSharedCheck_4860_ == 0 {
                                    v___x_4855_ = v___x_4842_;
                                    v_isShared_4856_ = v_isSharedCheck_4860_;
                                    state = 8;
                                    continue;
                                } else {
                                    leanh::lean_inc(v_a_4853_);
                                    leanh::lean_dec(v___x_4842_);
                                    v___x_4855_ = leanh::lean_box(0);
                                    v_isShared_4856_ = v_isSharedCheck_4860_;
                                    state = 8;
                                    continue;
                                }
                            }
                        }
                    } else {
                        v_a_4820_ = v___x_4829_;
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                if v_isShared_4817_ == 0 {
                    leanh::lean_ctor_set(v___x_4816_, 1, v_a_4820_);
                    leanh::lean_ctor_set(v___x_4816_, 0, v___x_4818_);
                    v___x_4822_ = v___x_4816_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_4826_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4826_, 0, v___x_4818_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4826_, 1, v_a_4820_);
                    v___x_4822_ = v_reuseFailAlloc_4826_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_4823_ = 1usize;
                v___x_4824_ = lean_usize_add(v_i_4802_, v___x_4823_);
                v_i_4802_ = v___x_4824_;
                v_b_4803_ = v___x_4822_;
                state = 0;
                continue;
            }
            4 => {
                if v_isShared_4837_ == 0 {
                    v___x_4839_ = v___x_4836_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_4840_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4840_, 0, v_a_4834_);
                    v___x_4839_ = v_reuseFailAlloc_4840_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_4839_;
            }
            6 => {
                if v_isShared_4848_ == 0 {
                    v___x_4850_ = v___x_4847_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_4851_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4851_, 0, v_a_4845_);
                    v___x_4850_ = v_reuseFailAlloc_4851_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_4850_;
            }
            8 => {
                if v_isShared_4856_ == 0 {
                    v___x_4858_ = v___x_4855_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_4859_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4859_, 0, v_a_4853_);
                    v___x_4858_ = v_reuseFailAlloc_4859_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_4858_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Try_Collect_0__Lean_Meta_Try_Collector_main_go_spec__0_spec__1_spec__4___boxed(
    mut v_as_4863_: *mut leanh::LeanObject,
    mut v_sz_4864_: *mut leanh::LeanObject,
    mut v_i_4865_: *mut leanh::LeanObject,
    mut v_b_4866_: *mut leanh::LeanObject,
    mut v___y_4867_: *mut leanh::LeanObject,
    mut v___y_4868_: *mut leanh::LeanObject,
    mut v___y_4869_: *mut leanh::LeanObject,
    mut v___y_4870_: *mut leanh::LeanObject,
    mut v___y_4871_: *mut leanh::LeanObject,
    mut v___y_4872_: *mut leanh::LeanObject,
    mut v___y_4873_: *mut leanh::LeanObject,
    mut v___y_4874_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_sz_boxed_4875_: usize = 0;
    let mut v_i_boxed_4876_: usize = 0;
    let mut v_res_4877_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_4875_ = leanh::lean_unbox_usize(v_sz_4864_);
    leanh::lean_dec(v_sz_4864_);
    v_i_boxed_4876_ = leanh::lean_unbox_usize(v_i_4865_);
    leanh::lean_dec(v_i_4865_);
    v_res_4877_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Try_Collect_0__Lean_Meta_Try_Collector_main_go_spec__0_spec__1_spec__4(v_as_4863_, v_sz_boxed_4875_, v_i_boxed_4876_, v_b_4866_, v___y_4867_, v___y_4868_, v___y_4869_, v___y_4870_, v___y_4871_, v___y_4872_, v___y_4873_);
    leanh::lean_dec(v___y_4873_);
    leanh::lean_dec_ref(v___y_4872_);
    leanh::lean_dec(v___y_4871_);
    leanh::lean_dec_ref(v___y_4870_);
    leanh::lean_dec(v___y_4869_);
    leanh::lean_dec_ref(v___y_4868_);
    leanh::lean_dec(v___y_4867_);
    leanh::lean_dec_ref(v_as_4863_);
    return v_res_4877_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Try_Collect_0__Lean_Meta_Try_Collector_main_go_spec__0_spec__1(
    mut v_as_4878_: *mut leanh::LeanObject,
    mut v_sz_4879_: usize,
    mut v_i_4880_: usize,
    mut v_b_4881_: *mut leanh::LeanObject,
    mut v___y_4882_: *mut leanh::LeanObject,
    mut v___y_4883_: *mut leanh::LeanObject,
    mut v___y_4884_: *mut leanh::LeanObject,
    mut v___y_4885_: *mut leanh::LeanObject,
    mut v___y_4886_: *mut leanh::LeanObject,
    mut v___y_4887_: *mut leanh::LeanObject,
    mut v___y_4888_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4890_: u8 = 0;
    let mut v___x_4891_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_4892_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4894_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4895_: u8 = 0;
    let mut v___x_4896_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4898_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4900_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4901_: usize = 0;
    let mut v___x_4902_: usize = 0;
    let mut v___x_4903_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4904_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4905_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_4906_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4907_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4908_: u8 = 0;
    let mut v___x_4909_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_4910_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4911_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4912_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4914_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4915_: u8 = 0;
    let mut v___x_4917_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4918_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4919_: u8 = 0;
    let mut v___x_4920_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4921_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4922_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4923_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4925_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4926_: u8 = 0;
    let mut v___x_4928_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4929_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4930_: u8 = 0;
    let mut v_a_4931_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4933_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4934_: u8 = 0;
    let mut v___x_4936_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4937_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4938_: u8 = 0;
    let mut v_isSharedCheck_4939_: u8 = 0;
    let mut v_unused_4940_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4890_ = lean_usize_dec_lt(v_i_4880_, v_sz_4879_);
                if v___x_4890_ == 0 {
                    v___x_4891_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_4891_, 0, v_b_4881_);
                    return v___x_4891_;
                } else {
                    v_snd_4892_ = leanh::lean_ctor_get(v_b_4881_, 1);
                    v_isSharedCheck_4939_ = (!leanh::lean_is_exclusive(v_b_4881_)) as u8;
                    if v_isSharedCheck_4939_ == 0 {
                        v_unused_4940_ = leanh::lean_ctor_get(v_b_4881_, 0);
                        leanh::lean_dec(v_unused_4940_);
                        v___x_4894_ = v_b_4881_;
                        v_isShared_4895_ = v_isSharedCheck_4939_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_snd_4892_);
                        leanh::lean_dec(v_b_4881_);
                        v___x_4894_ = leanh::lean_box(0);
                        v_isShared_4895_ = v_isSharedCheck_4939_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_4896_ = leanh::lean_box(0);
                v_a_4905_ = lean_array_uget_borrowed(v_as_4878_, v_i_4880_);
                if leanh::lean_obj_tag(v_a_4905_) == 0 {
                    v_a_4898_ = v_snd_4892_;
                    state = 2;
                    continue;
                } else {
                    leanh::lean_dec(v_snd_4892_);
                    v_val_4906_ = leanh::lean_ctor_get(v_a_4905_, 0);
                    v___x_4907_ = leanh::lean_box(0);
                    v___x_4908_ = l_Lean_LocalDecl_isAuxDecl(v_val_4906_);
                    if v___x_4908_ == 0 {
                        v___x_4909_ = l_Lean_LocalDecl_value_x3f(v_val_4906_, v___x_4908_);
                        if leanh::lean_obj_tag(v___x_4909_) == 1 {
                            v_val_4910_ = leanh::lean_ctor_get(v___x_4909_, 0);
                            leanh::lean_inc(v_val_4910_);
                            leanh::lean_dec_ref_known(v___x_4909_, 1);
                            v___x_4911_ = l_Lean_Meta_Try_Collector_visit(
                                v_val_4910_,
                                v___y_4882_,
                                v___y_4883_,
                                v___y_4884_,
                                v___y_4885_,
                                v___y_4886_,
                                v___y_4887_,
                                v___y_4888_,
                            );
                            if leanh::lean_obj_tag(v___x_4911_) == 0 {
                                leanh::lean_dec_ref_known(v___x_4911_, 1);
                                v_a_4898_ = v___x_4907_;
                                state = 2;
                                continue;
                            } else {
                                leanh::lean_del_object(v___x_4894_);
                                v_a_4912_ = leanh::lean_ctor_get(v___x_4911_, 0);
                                v_isSharedCheck_4919_ =
                                    (!leanh::lean_is_exclusive(v___x_4911_)) as u8;
                                if v_isSharedCheck_4919_ == 0 {
                                    v___x_4914_ = v___x_4911_;
                                    v_isShared_4915_ = v_isSharedCheck_4919_;
                                    state = 4;
                                    continue;
                                } else {
                                    leanh::lean_inc(v_a_4912_);
                                    leanh::lean_dec(v___x_4911_);
                                    v___x_4914_ = leanh::lean_box(0);
                                    v_isShared_4915_ = v_isSharedCheck_4919_;
                                    state = 4;
                                    continue;
                                }
                            }
                        } else {
                            leanh::lean_dec(v___x_4909_);
                            v___x_4920_ = l_Lean_Meta_Try_Collector_checkInductive(
                                v_val_4906_,
                                v___y_4883_,
                                v___y_4884_,
                                v___y_4885_,
                                v___y_4886_,
                                v___y_4887_,
                                v___y_4888_,
                            );
                            if leanh::lean_obj_tag(v___x_4920_) == 0 {
                                leanh::lean_dec_ref_known(v___x_4920_, 1);
                                v___x_4921_ = l_Lean_LocalDecl_type(v_val_4906_);
                                v___x_4922_ = l_Lean_Meta_Try_Collector_visit(
                                    v___x_4921_,
                                    v___y_4882_,
                                    v___y_4883_,
                                    v___y_4884_,
                                    v___y_4885_,
                                    v___y_4886_,
                                    v___y_4887_,
                                    v___y_4888_,
                                );
                                if leanh::lean_obj_tag(v___x_4922_) == 0 {
                                    leanh::lean_dec_ref_known(v___x_4922_, 1);
                                    v_a_4898_ = v___x_4907_;
                                    state = 2;
                                    continue;
                                } else {
                                    leanh::lean_del_object(v___x_4894_);
                                    v_a_4923_ = leanh::lean_ctor_get(v___x_4922_, 0);
                                    v_isSharedCheck_4930_ =
                                        (!leanh::lean_is_exclusive(v___x_4922_)) as u8;
                                    if v_isSharedCheck_4930_ == 0 {
                                        v___x_4925_ = v___x_4922_;
                                        v_isShared_4926_ = v_isSharedCheck_4930_;
                                        state = 6;
                                        continue;
                                    } else {
                                        leanh::lean_inc(v_a_4923_);
                                        leanh::lean_dec(v___x_4922_);
                                        v___x_4925_ = leanh::lean_box(0);
                                        v_isShared_4926_ = v_isSharedCheck_4930_;
                                        state = 6;
                                        continue;
                                    }
                                }
                            } else {
                                leanh::lean_del_object(v___x_4894_);
                                v_a_4931_ = leanh::lean_ctor_get(v___x_4920_, 0);
                                v_isSharedCheck_4938_ =
                                    (!leanh::lean_is_exclusive(v___x_4920_)) as u8;
                                if v_isSharedCheck_4938_ == 0 {
                                    v___x_4933_ = v___x_4920_;
                                    v_isShared_4934_ = v_isSharedCheck_4938_;
                                    state = 8;
                                    continue;
                                } else {
                                    leanh::lean_inc(v_a_4931_);
                                    leanh::lean_dec(v___x_4920_);
                                    v___x_4933_ = leanh::lean_box(0);
                                    v_isShared_4934_ = v_isSharedCheck_4938_;
                                    state = 8;
                                    continue;
                                }
                            }
                        }
                    } else {
                        v_a_4898_ = v___x_4907_;
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                if v_isShared_4895_ == 0 {
                    leanh::lean_ctor_set(v___x_4894_, 1, v_a_4898_);
                    leanh::lean_ctor_set(v___x_4894_, 0, v___x_4896_);
                    v___x_4900_ = v___x_4894_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_4904_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4904_, 0, v___x_4896_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4904_, 1, v_a_4898_);
                    v___x_4900_ = v_reuseFailAlloc_4904_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_4901_ = 1usize;
                v___x_4902_ = lean_usize_add(v_i_4880_, v___x_4901_);
                v___x_4903_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Try_Collect_0__Lean_Meta_Try_Collector_main_go_spec__0_spec__1_spec__4(v_as_4878_, v_sz_4879_, v___x_4902_, v___x_4900_, v___y_4882_, v___y_4883_, v___y_4884_, v___y_4885_, v___y_4886_, v___y_4887_, v___y_4888_);
                return v___x_4903_;
            }
            4 => {
                if v_isShared_4915_ == 0 {
                    v___x_4917_ = v___x_4914_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_4918_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4918_, 0, v_a_4912_);
                    v___x_4917_ = v_reuseFailAlloc_4918_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_4917_;
            }
            6 => {
                if v_isShared_4926_ == 0 {
                    v___x_4928_ = v___x_4925_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_4929_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4929_, 0, v_a_4923_);
                    v___x_4928_ = v_reuseFailAlloc_4929_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_4928_;
            }
            8 => {
                if v_isShared_4934_ == 0 {
                    v___x_4936_ = v___x_4933_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_4937_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4937_, 0, v_a_4931_);
                    v___x_4936_ = v_reuseFailAlloc_4937_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_4936_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Try_Collect_0__Lean_Meta_Try_Collector_main_go_spec__0_spec__1___boxed(
    mut v_as_4941_: *mut leanh::LeanObject,
    mut v_sz_4942_: *mut leanh::LeanObject,
    mut v_i_4943_: *mut leanh::LeanObject,
    mut v_b_4944_: *mut leanh::LeanObject,
    mut v___y_4945_: *mut leanh::LeanObject,
    mut v___y_4946_: *mut leanh::LeanObject,
    mut v___y_4947_: *mut leanh::LeanObject,
    mut v___y_4948_: *mut leanh::LeanObject,
    mut v___y_4949_: *mut leanh::LeanObject,
    mut v___y_4950_: *mut leanh::LeanObject,
    mut v___y_4951_: *mut leanh::LeanObject,
    mut v___y_4952_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_sz_boxed_4953_: usize = 0;
    let mut v_i_boxed_4954_: usize = 0;
    let mut v_res_4955_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_4953_ = leanh::lean_unbox_usize(v_sz_4942_);
    leanh::lean_dec(v_sz_4942_);
    v_i_boxed_4954_ = leanh::lean_unbox_usize(v_i_4943_);
    leanh::lean_dec(v_i_4943_);
    v_res_4955_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Try_Collect_0__Lean_Meta_Try_Collector_main_go_spec__0_spec__1(v_as_4941_, v_sz_boxed_4953_, v_i_boxed_4954_, v_b_4944_, v___y_4945_, v___y_4946_, v___y_4947_, v___y_4948_, v___y_4949_, v___y_4950_, v___y_4951_);
    leanh::lean_dec(v___y_4951_);
    leanh::lean_dec_ref(v___y_4950_);
    leanh::lean_dec(v___y_4949_);
    leanh::lean_dec_ref(v___y_4948_);
    leanh::lean_dec(v___y_4947_);
    leanh::lean_dec_ref(v___y_4946_);
    leanh::lean_dec(v___y_4945_);
    leanh::lean_dec_ref(v_as_4941_);
    return v_res_4955_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Try_Collect_0__Lean_Meta_Try_Collector_main_go_spec__0_spec__0_spec__2_spec__3(
    mut v_as_4956_: *mut leanh::LeanObject,
    mut v_sz_4957_: usize,
    mut v_i_4958_: usize,
    mut v_b_4959_: *mut leanh::LeanObject,
    mut v___y_4960_: *mut leanh::LeanObject,
    mut v___y_4961_: *mut leanh::LeanObject,
    mut v___y_4962_: *mut leanh::LeanObject,
    mut v___y_4963_: *mut leanh::LeanObject,
    mut v___y_4964_: *mut leanh::LeanObject,
    mut v___y_4965_: *mut leanh::LeanObject,
    mut v___y_4966_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4968_: u8 = 0;
    let mut v___x_4969_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_4970_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4972_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4973_: u8 = 0;
    let mut v___x_4974_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4976_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4978_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4979_: usize = 0;
    let mut v___x_4980_: usize = 0;
    let mut v_reuseFailAlloc_4982_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4983_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_4984_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4985_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4986_: u8 = 0;
    let mut v___x_4987_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_4988_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4989_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4990_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4992_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4993_: u8 = 0;
    let mut v___x_4995_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4996_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4997_: u8 = 0;
    let mut v___x_4998_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4999_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5000_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5001_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5003_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5004_: u8 = 0;
    let mut v___x_5006_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5007_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5008_: u8 = 0;
    let mut v_a_5009_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5011_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5012_: u8 = 0;
    let mut v___x_5014_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5015_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5016_: u8 = 0;
    let mut v_isSharedCheck_5017_: u8 = 0;
    let mut v_unused_5018_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4968_ = lean_usize_dec_lt(v_i_4958_, v_sz_4957_);
                if v___x_4968_ == 0 {
                    v___x_4969_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_4969_, 0, v_b_4959_);
                    return v___x_4969_;
                } else {
                    v_snd_4970_ = leanh::lean_ctor_get(v_b_4959_, 1);
                    v_isSharedCheck_5017_ = (!leanh::lean_is_exclusive(v_b_4959_)) as u8;
                    if v_isSharedCheck_5017_ == 0 {
                        v_unused_5018_ = leanh::lean_ctor_get(v_b_4959_, 0);
                        leanh::lean_dec(v_unused_5018_);
                        v___x_4972_ = v_b_4959_;
                        v_isShared_4973_ = v_isSharedCheck_5017_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_snd_4970_);
                        leanh::lean_dec(v_b_4959_);
                        v___x_4972_ = leanh::lean_box(0);
                        v_isShared_4973_ = v_isSharedCheck_5017_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_4974_ = leanh::lean_box(0);
                v_a_4983_ = lean_array_uget_borrowed(v_as_4956_, v_i_4958_);
                if leanh::lean_obj_tag(v_a_4983_) == 0 {
                    v_a_4976_ = v_snd_4970_;
                    state = 2;
                    continue;
                } else {
                    leanh::lean_dec(v_snd_4970_);
                    v_val_4984_ = leanh::lean_ctor_get(v_a_4983_, 0);
                    v___x_4985_ = leanh::lean_box(0);
                    v___x_4986_ = l_Lean_LocalDecl_isAuxDecl(v_val_4984_);
                    if v___x_4986_ == 0 {
                        v___x_4987_ = l_Lean_LocalDecl_value_x3f(v_val_4984_, v___x_4986_);
                        if leanh::lean_obj_tag(v___x_4987_) == 1 {
                            v_val_4988_ = leanh::lean_ctor_get(v___x_4987_, 0);
                            leanh::lean_inc(v_val_4988_);
                            leanh::lean_dec_ref_known(v___x_4987_, 1);
                            v___x_4989_ = l_Lean_Meta_Try_Collector_visit(
                                v_val_4988_,
                                v___y_4960_,
                                v___y_4961_,
                                v___y_4962_,
                                v___y_4963_,
                                v___y_4964_,
                                v___y_4965_,
                                v___y_4966_,
                            );
                            if leanh::lean_obj_tag(v___x_4989_) == 0 {
                                leanh::lean_dec_ref_known(v___x_4989_, 1);
                                v_a_4976_ = v___x_4985_;
                                state = 2;
                                continue;
                            } else {
                                leanh::lean_del_object(v___x_4972_);
                                v_a_4990_ = leanh::lean_ctor_get(v___x_4989_, 0);
                                v_isSharedCheck_4997_ =
                                    (!leanh::lean_is_exclusive(v___x_4989_)) as u8;
                                if v_isSharedCheck_4997_ == 0 {
                                    v___x_4992_ = v___x_4989_;
                                    v_isShared_4993_ = v_isSharedCheck_4997_;
                                    state = 4;
                                    continue;
                                } else {
                                    leanh::lean_inc(v_a_4990_);
                                    leanh::lean_dec(v___x_4989_);
                                    v___x_4992_ = leanh::lean_box(0);
                                    v_isShared_4993_ = v_isSharedCheck_4997_;
                                    state = 4;
                                    continue;
                                }
                            }
                        } else {
                            leanh::lean_dec(v___x_4987_);
                            v___x_4998_ = l_Lean_Meta_Try_Collector_checkInductive(
                                v_val_4984_,
                                v___y_4961_,
                                v___y_4962_,
                                v___y_4963_,
                                v___y_4964_,
                                v___y_4965_,
                                v___y_4966_,
                            );
                            if leanh::lean_obj_tag(v___x_4998_) == 0 {
                                leanh::lean_dec_ref_known(v___x_4998_, 1);
                                v___x_4999_ = l_Lean_LocalDecl_type(v_val_4984_);
                                v___x_5000_ = l_Lean_Meta_Try_Collector_visit(
                                    v___x_4999_,
                                    v___y_4960_,
                                    v___y_4961_,
                                    v___y_4962_,
                                    v___y_4963_,
                                    v___y_4964_,
                                    v___y_4965_,
                                    v___y_4966_,
                                );
                                if leanh::lean_obj_tag(v___x_5000_) == 0 {
                                    leanh::lean_dec_ref_known(v___x_5000_, 1);
                                    v_a_4976_ = v___x_4985_;
                                    state = 2;
                                    continue;
                                } else {
                                    leanh::lean_del_object(v___x_4972_);
                                    v_a_5001_ = leanh::lean_ctor_get(v___x_5000_, 0);
                                    v_isSharedCheck_5008_ =
                                        (!leanh::lean_is_exclusive(v___x_5000_)) as u8;
                                    if v_isSharedCheck_5008_ == 0 {
                                        v___x_5003_ = v___x_5000_;
                                        v_isShared_5004_ = v_isSharedCheck_5008_;
                                        state = 6;
                                        continue;
                                    } else {
                                        leanh::lean_inc(v_a_5001_);
                                        leanh::lean_dec(v___x_5000_);
                                        v___x_5003_ = leanh::lean_box(0);
                                        v_isShared_5004_ = v_isSharedCheck_5008_;
                                        state = 6;
                                        continue;
                                    }
                                }
                            } else {
                                leanh::lean_del_object(v___x_4972_);
                                v_a_5009_ = leanh::lean_ctor_get(v___x_4998_, 0);
                                v_isSharedCheck_5016_ =
                                    (!leanh::lean_is_exclusive(v___x_4998_)) as u8;
                                if v_isSharedCheck_5016_ == 0 {
                                    v___x_5011_ = v___x_4998_;
                                    v_isShared_5012_ = v_isSharedCheck_5016_;
                                    state = 8;
                                    continue;
                                } else {
                                    leanh::lean_inc(v_a_5009_);
                                    leanh::lean_dec(v___x_4998_);
                                    v___x_5011_ = leanh::lean_box(0);
                                    v_isShared_5012_ = v_isSharedCheck_5016_;
                                    state = 8;
                                    continue;
                                }
                            }
                        }
                    } else {
                        v_a_4976_ = v___x_4985_;
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                if v_isShared_4973_ == 0 {
                    leanh::lean_ctor_set(v___x_4972_, 1, v_a_4976_);
                    leanh::lean_ctor_set(v___x_4972_, 0, v___x_4974_);
                    v___x_4978_ = v___x_4972_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_4982_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4982_, 0, v___x_4974_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4982_, 1, v_a_4976_);
                    v___x_4978_ = v_reuseFailAlloc_4982_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_4979_ = 1usize;
                v___x_4980_ = lean_usize_add(v_i_4958_, v___x_4979_);
                v_i_4958_ = v___x_4980_;
                v_b_4959_ = v___x_4978_;
                state = 0;
                continue;
            }
            4 => {
                if v_isShared_4993_ == 0 {
                    v___x_4995_ = v___x_4992_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_4996_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4996_, 0, v_a_4990_);
                    v___x_4995_ = v_reuseFailAlloc_4996_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_4995_;
            }
            6 => {
                if v_isShared_5004_ == 0 {
                    v___x_5006_ = v___x_5003_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_5007_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5007_, 0, v_a_5001_);
                    v___x_5006_ = v_reuseFailAlloc_5007_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_5006_;
            }
            8 => {
                if v_isShared_5012_ == 0 {
                    v___x_5014_ = v___x_5011_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_5015_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5015_, 0, v_a_5009_);
                    v___x_5014_ = v_reuseFailAlloc_5015_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_5014_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Try_Collect_0__Lean_Meta_Try_Collector_main_go_spec__0_spec__0_spec__2_spec__3___boxed(
    mut v_as_5019_: *mut leanh::LeanObject,
    mut v_sz_5020_: *mut leanh::LeanObject,
    mut v_i_5021_: *mut leanh::LeanObject,
    mut v_b_5022_: *mut leanh::LeanObject,
    mut v___y_5023_: *mut leanh::LeanObject,
    mut v___y_5024_: *mut leanh::LeanObject,
    mut v___y_5025_: *mut leanh::LeanObject,
    mut v___y_5026_: *mut leanh::LeanObject,
    mut v___y_5027_: *mut leanh::LeanObject,
    mut v___y_5028_: *mut leanh::LeanObject,
    mut v___y_5029_: *mut leanh::LeanObject,
    mut v___y_5030_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_sz_boxed_5031_: usize = 0;
    let mut v_i_boxed_5032_: usize = 0;
    let mut v_res_5033_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_5031_ = leanh::lean_unbox_usize(v_sz_5020_);
    leanh::lean_dec(v_sz_5020_);
    v_i_boxed_5032_ = leanh::lean_unbox_usize(v_i_5021_);
    leanh::lean_dec(v_i_5021_);
    v_res_5033_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Try_Collect_0__Lean_Meta_Try_Collector_main_go_spec__0_spec__0_spec__2_spec__3(v_as_5019_, v_sz_boxed_5031_, v_i_boxed_5032_, v_b_5022_, v___y_5023_, v___y_5024_, v___y_5025_, v___y_5026_, v___y_5027_, v___y_5028_, v___y_5029_);
    leanh::lean_dec(v___y_5029_);
    leanh::lean_dec_ref(v___y_5028_);
    leanh::lean_dec(v___y_5027_);
    leanh::lean_dec_ref(v___y_5026_);
    leanh::lean_dec(v___y_5025_);
    leanh::lean_dec_ref(v___y_5024_);
    leanh::lean_dec(v___y_5023_);
    leanh::lean_dec_ref(v_as_5019_);
    return v_res_5033_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Try_Collect_0__Lean_Meta_Try_Collector_main_go_spec__0_spec__0_spec__2(
    mut v_as_5034_: *mut leanh::LeanObject,
    mut v_sz_5035_: usize,
    mut v_i_5036_: usize,
    mut v_b_5037_: *mut leanh::LeanObject,
    mut v___y_5038_: *mut leanh::LeanObject,
    mut v___y_5039_: *mut leanh::LeanObject,
    mut v___y_5040_: *mut leanh::LeanObject,
    mut v___y_5041_: *mut leanh::LeanObject,
    mut v___y_5042_: *mut leanh::LeanObject,
    mut v___y_5043_: *mut leanh::LeanObject,
    mut v___y_5044_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5046_: u8 = 0;
    let mut v___x_5047_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_5048_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5050_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5051_: u8 = 0;
    let mut v___x_5052_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5054_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5056_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5057_: usize = 0;
    let mut v___x_5058_: usize = 0;
    let mut v___x_5059_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5060_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5061_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_5062_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5063_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5064_: u8 = 0;
    let mut v___x_5065_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_5066_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5067_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5068_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5070_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5071_: u8 = 0;
    let mut v___x_5073_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5074_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5075_: u8 = 0;
    let mut v___x_5076_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5077_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5078_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5079_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5081_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5082_: u8 = 0;
    let mut v___x_5084_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5085_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5086_: u8 = 0;
    let mut v_a_5087_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5089_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5090_: u8 = 0;
    let mut v___x_5092_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5093_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5094_: u8 = 0;
    let mut v_isSharedCheck_5095_: u8 = 0;
    let mut v_unused_5096_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5046_ = lean_usize_dec_lt(v_i_5036_, v_sz_5035_);
                if v___x_5046_ == 0 {
                    v___x_5047_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_5047_, 0, v_b_5037_);
                    return v___x_5047_;
                } else {
                    v_snd_5048_ = leanh::lean_ctor_get(v_b_5037_, 1);
                    v_isSharedCheck_5095_ = (!leanh::lean_is_exclusive(v_b_5037_)) as u8;
                    if v_isSharedCheck_5095_ == 0 {
                        v_unused_5096_ = leanh::lean_ctor_get(v_b_5037_, 0);
                        leanh::lean_dec(v_unused_5096_);
                        v___x_5050_ = v_b_5037_;
                        v_isShared_5051_ = v_isSharedCheck_5095_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_snd_5048_);
                        leanh::lean_dec(v_b_5037_);
                        v___x_5050_ = leanh::lean_box(0);
                        v_isShared_5051_ = v_isSharedCheck_5095_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_5052_ = leanh::lean_box(0);
                v_a_5061_ = lean_array_uget_borrowed(v_as_5034_, v_i_5036_);
                if leanh::lean_obj_tag(v_a_5061_) == 0 {
                    v_a_5054_ = v_snd_5048_;
                    state = 2;
                    continue;
                } else {
                    leanh::lean_dec(v_snd_5048_);
                    v_val_5062_ = leanh::lean_ctor_get(v_a_5061_, 0);
                    v___x_5063_ = leanh::lean_box(0);
                    v___x_5064_ = l_Lean_LocalDecl_isAuxDecl(v_val_5062_);
                    if v___x_5064_ == 0 {
                        v___x_5065_ = l_Lean_LocalDecl_value_x3f(v_val_5062_, v___x_5064_);
                        if leanh::lean_obj_tag(v___x_5065_) == 1 {
                            v_val_5066_ = leanh::lean_ctor_get(v___x_5065_, 0);
                            leanh::lean_inc(v_val_5066_);
                            leanh::lean_dec_ref_known(v___x_5065_, 1);
                            v___x_5067_ = l_Lean_Meta_Try_Collector_visit(
                                v_val_5066_,
                                v___y_5038_,
                                v___y_5039_,
                                v___y_5040_,
                                v___y_5041_,
                                v___y_5042_,
                                v___y_5043_,
                                v___y_5044_,
                            );
                            if leanh::lean_obj_tag(v___x_5067_) == 0 {
                                leanh::lean_dec_ref_known(v___x_5067_, 1);
                                v_a_5054_ = v___x_5063_;
                                state = 2;
                                continue;
                            } else {
                                leanh::lean_del_object(v___x_5050_);
                                v_a_5068_ = leanh::lean_ctor_get(v___x_5067_, 0);
                                v_isSharedCheck_5075_ =
                                    (!leanh::lean_is_exclusive(v___x_5067_)) as u8;
                                if v_isSharedCheck_5075_ == 0 {
                                    v___x_5070_ = v___x_5067_;
                                    v_isShared_5071_ = v_isSharedCheck_5075_;
                                    state = 4;
                                    continue;
                                } else {
                                    leanh::lean_inc(v_a_5068_);
                                    leanh::lean_dec(v___x_5067_);
                                    v___x_5070_ = leanh::lean_box(0);
                                    v_isShared_5071_ = v_isSharedCheck_5075_;
                                    state = 4;
                                    continue;
                                }
                            }
                        } else {
                            leanh::lean_dec(v___x_5065_);
                            v___x_5076_ = l_Lean_Meta_Try_Collector_checkInductive(
                                v_val_5062_,
                                v___y_5039_,
                                v___y_5040_,
                                v___y_5041_,
                                v___y_5042_,
                                v___y_5043_,
                                v___y_5044_,
                            );
                            if leanh::lean_obj_tag(v___x_5076_) == 0 {
                                leanh::lean_dec_ref_known(v___x_5076_, 1);
                                v___x_5077_ = l_Lean_LocalDecl_type(v_val_5062_);
                                v___x_5078_ = l_Lean_Meta_Try_Collector_visit(
                                    v___x_5077_,
                                    v___y_5038_,
                                    v___y_5039_,
                                    v___y_5040_,
                                    v___y_5041_,
                                    v___y_5042_,
                                    v___y_5043_,
                                    v___y_5044_,
                                );
                                if leanh::lean_obj_tag(v___x_5078_) == 0 {
                                    leanh::lean_dec_ref_known(v___x_5078_, 1);
                                    v_a_5054_ = v___x_5063_;
                                    state = 2;
                                    continue;
                                } else {
                                    leanh::lean_del_object(v___x_5050_);
                                    v_a_5079_ = leanh::lean_ctor_get(v___x_5078_, 0);
                                    v_isSharedCheck_5086_ =
                                        (!leanh::lean_is_exclusive(v___x_5078_)) as u8;
                                    if v_isSharedCheck_5086_ == 0 {
                                        v___x_5081_ = v___x_5078_;
                                        v_isShared_5082_ = v_isSharedCheck_5086_;
                                        state = 6;
                                        continue;
                                    } else {
                                        leanh::lean_inc(v_a_5079_);
                                        leanh::lean_dec(v___x_5078_);
                                        v___x_5081_ = leanh::lean_box(0);
                                        v_isShared_5082_ = v_isSharedCheck_5086_;
                                        state = 6;
                                        continue;
                                    }
                                }
                            } else {
                                leanh::lean_del_object(v___x_5050_);
                                v_a_5087_ = leanh::lean_ctor_get(v___x_5076_, 0);
                                v_isSharedCheck_5094_ =
                                    (!leanh::lean_is_exclusive(v___x_5076_)) as u8;
                                if v_isSharedCheck_5094_ == 0 {
                                    v___x_5089_ = v___x_5076_;
                                    v_isShared_5090_ = v_isSharedCheck_5094_;
                                    state = 8;
                                    continue;
                                } else {
                                    leanh::lean_inc(v_a_5087_);
                                    leanh::lean_dec(v___x_5076_);
                                    v___x_5089_ = leanh::lean_box(0);
                                    v_isShared_5090_ = v_isSharedCheck_5094_;
                                    state = 8;
                                    continue;
                                }
                            }
                        }
                    } else {
                        v_a_5054_ = v___x_5063_;
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                if v_isShared_5051_ == 0 {
                    leanh::lean_ctor_set(v___x_5050_, 1, v_a_5054_);
                    leanh::lean_ctor_set(v___x_5050_, 0, v___x_5052_);
                    v___x_5056_ = v___x_5050_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_5060_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5060_, 0, v___x_5052_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5060_, 1, v_a_5054_);
                    v___x_5056_ = v_reuseFailAlloc_5060_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_5057_ = 1usize;
                v___x_5058_ = lean_usize_add(v_i_5036_, v___x_5057_);
                v___x_5059_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Try_Collect_0__Lean_Meta_Try_Collector_main_go_spec__0_spec__0_spec__2_spec__3(v_as_5034_, v_sz_5035_, v___x_5058_, v___x_5056_, v___y_5038_, v___y_5039_, v___y_5040_, v___y_5041_, v___y_5042_, v___y_5043_, v___y_5044_);
                return v___x_5059_;
            }
            4 => {
                if v_isShared_5071_ == 0 {
                    v___x_5073_ = v___x_5070_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_5074_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5074_, 0, v_a_5068_);
                    v___x_5073_ = v_reuseFailAlloc_5074_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_5073_;
            }
            6 => {
                if v_isShared_5082_ == 0 {
                    v___x_5084_ = v___x_5081_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_5085_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5085_, 0, v_a_5079_);
                    v___x_5084_ = v_reuseFailAlloc_5085_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_5084_;
            }
            8 => {
                if v_isShared_5090_ == 0 {
                    v___x_5092_ = v___x_5089_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_5093_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5093_, 0, v_a_5087_);
                    v___x_5092_ = v_reuseFailAlloc_5093_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_5092_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Try_Collect_0__Lean_Meta_Try_Collector_main_go_spec__0_spec__0_spec__2___boxed(
    mut v_as_5097_: *mut leanh::LeanObject,
    mut v_sz_5098_: *mut leanh::LeanObject,
    mut v_i_5099_: *mut leanh::LeanObject,
    mut v_b_5100_: *mut leanh::LeanObject,
    mut v___y_5101_: *mut leanh::LeanObject,
    mut v___y_5102_: *mut leanh::LeanObject,
    mut v___y_5103_: *mut leanh::LeanObject,
    mut v___y_5104_: *mut leanh::LeanObject,
    mut v___y_5105_: *mut leanh::LeanObject,
    mut v___y_5106_: *mut leanh::LeanObject,
    mut v___y_5107_: *mut leanh::LeanObject,
    mut v___y_5108_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_sz_boxed_5109_: usize = 0;
    let mut v_i_boxed_5110_: usize = 0;
    let mut v_res_5111_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_5109_ = leanh::lean_unbox_usize(v_sz_5098_);
    leanh::lean_dec(v_sz_5098_);
    v_i_boxed_5110_ = leanh::lean_unbox_usize(v_i_5099_);
    leanh::lean_dec(v_i_5099_);
    v_res_5111_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Try_Collect_0__Lean_Meta_Try_Collector_main_go_spec__0_spec__0_spec__2(v_as_5097_, v_sz_boxed_5109_, v_i_boxed_5110_, v_b_5100_, v___y_5101_, v___y_5102_, v___y_5103_, v___y_5104_, v___y_5105_, v___y_5106_, v___y_5107_);
    leanh::lean_dec(v___y_5107_);
    leanh::lean_dec_ref(v___y_5106_);
    leanh::lean_dec(v___y_5105_);
    leanh::lean_dec_ref(v___y_5104_);
    leanh::lean_dec(v___y_5103_);
    leanh::lean_dec_ref(v___y_5102_);
    leanh::lean_dec(v___y_5101_);
    leanh::lean_dec_ref(v_as_5097_);
    return v_res_5111_;
}
pub unsafe fn l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Try_Collect_0__Lean_Meta_Try_Collector_main_go_spec__0_spec__0(
    mut v_init_5112_: *mut leanh::LeanObject,
    mut v_n_5113_: *mut leanh::LeanObject,
    mut v_b_5114_: *mut leanh::LeanObject,
    mut v___y_5115_: *mut leanh::LeanObject,
    mut v___y_5116_: *mut leanh::LeanObject,
    mut v___y_5117_: *mut leanh::LeanObject,
    mut v___y_5118_: *mut leanh::LeanObject,
    mut v___y_5119_: *mut leanh::LeanObject,
    mut v___y_5120_: *mut leanh::LeanObject,
    mut v___y_5121_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_cs_5123_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5124_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5125_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_5126_: usize = 0;
    let mut v___x_5127_: usize = 0;
    let mut v___x_5128_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5129_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5131_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5132_: u8 = 0;
    let mut v_fst_5133_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_5134_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5135_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5137_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5138_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_5139_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5141_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5142_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5143_: u8 = 0;
    let mut v_a_5144_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5146_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5147_: u8 = 0;
    let mut v___x_5149_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5150_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5151_: u8 = 0;
    let mut v_vs_5152_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5153_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5154_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_5155_: usize = 0;
    let mut v___x_5156_: usize = 0;
    let mut v___x_5157_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5158_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5160_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5161_: u8 = 0;
    let mut v_fst_5162_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_5163_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5164_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5166_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5167_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_5168_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5170_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5171_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5172_: u8 = 0;
    let mut v_a_5173_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5175_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5176_: u8 = 0;
    let mut v___x_5178_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5179_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5180_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_n_5113_) == 0 {
                    v_cs_5123_ = leanh::lean_ctor_get(v_n_5113_, 0);
                    v___x_5124_ = leanh::lean_box(0);
                    v___x_5125_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_5125_, 0, v___x_5124_);
                    leanh::lean_ctor_set(v___x_5125_, 1, v_b_5114_);
                    v_sz_5126_ = lean_array_size(v_cs_5123_);
                    v___x_5127_ = 0usize;
                    v___x_5128_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Try_Collect_0__Lean_Meta_Try_Collector_main_go_spec__0_spec__0_spec__1(v_init_5112_, v_cs_5123_, v_sz_5126_, v___x_5127_, v___x_5125_, v___y_5115_, v___y_5116_, v___y_5117_, v___y_5118_, v___y_5119_, v___y_5120_, v___y_5121_);
                    if leanh::lean_obj_tag(v___x_5128_) == 0 {
                        v_a_5129_ = leanh::lean_ctor_get(v___x_5128_, 0);
                        v_isSharedCheck_5143_ =
                            (!leanh::lean_is_exclusive(v___x_5128_)) as u8;
                        if v_isSharedCheck_5143_ == 0 {
                            v___x_5131_ = v___x_5128_;
                            v_isShared_5132_ = v_isSharedCheck_5143_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_5129_);
                            leanh::lean_dec(v___x_5128_);
                            v___x_5131_ = leanh::lean_box(0);
                            v_isShared_5132_ = v_isSharedCheck_5143_;
                            state = 1;
                            continue;
                        }
                    } else {
                        v_a_5144_ = leanh::lean_ctor_get(v___x_5128_, 0);
                        v_isSharedCheck_5151_ =
                            (!leanh::lean_is_exclusive(v___x_5128_)) as u8;
                        if v_isSharedCheck_5151_ == 0 {
                            v___x_5146_ = v___x_5128_;
                            v_isShared_5147_ = v_isSharedCheck_5151_;
                            state = 4;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_5144_);
                            leanh::lean_dec(v___x_5128_);
                            v___x_5146_ = leanh::lean_box(0);
                            v_isShared_5147_ = v_isSharedCheck_5151_;
                            state = 4;
                            continue;
                        }
                    }
                } else {
                    v_vs_5152_ = leanh::lean_ctor_get(v_n_5113_, 0);
                    v___x_5153_ = leanh::lean_box(0);
                    v___x_5154_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_5154_, 0, v___x_5153_);
                    leanh::lean_ctor_set(v___x_5154_, 1, v_b_5114_);
                    v_sz_5155_ = lean_array_size(v_vs_5152_);
                    v___x_5156_ = 0usize;
                    v___x_5157_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Try_Collect_0__Lean_Meta_Try_Collector_main_go_spec__0_spec__0_spec__2(v_vs_5152_, v_sz_5155_, v___x_5156_, v___x_5154_, v___y_5115_, v___y_5116_, v___y_5117_, v___y_5118_, v___y_5119_, v___y_5120_, v___y_5121_);
                    if leanh::lean_obj_tag(v___x_5157_) == 0 {
                        v_a_5158_ = leanh::lean_ctor_get(v___x_5157_, 0);
                        v_isSharedCheck_5172_ =
                            (!leanh::lean_is_exclusive(v___x_5157_)) as u8;
                        if v_isSharedCheck_5172_ == 0 {
                            v___x_5160_ = v___x_5157_;
                            v_isShared_5161_ = v_isSharedCheck_5172_;
                            state = 6;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_5158_);
                            leanh::lean_dec(v___x_5157_);
                            v___x_5160_ = leanh::lean_box(0);
                            v_isShared_5161_ = v_isSharedCheck_5172_;
                            state = 6;
                            continue;
                        }
                    } else {
                        v_a_5173_ = leanh::lean_ctor_get(v___x_5157_, 0);
                        v_isSharedCheck_5180_ =
                            (!leanh::lean_is_exclusive(v___x_5157_)) as u8;
                        if v_isSharedCheck_5180_ == 0 {
                            v___x_5175_ = v___x_5157_;
                            v_isShared_5176_ = v_isSharedCheck_5180_;
                            state = 9;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_5173_);
                            leanh::lean_dec(v___x_5157_);
                            v___x_5175_ = leanh::lean_box(0);
                            v_isShared_5176_ = v_isSharedCheck_5180_;
                            state = 9;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v_fst_5133_ = leanh::lean_ctor_get(v_a_5129_, 0);
                if leanh::lean_obj_tag(v_fst_5133_) == 0 {
                    v_snd_5134_ = leanh::lean_ctor_get(v_a_5129_, 1);
                    leanh::lean_inc(v_snd_5134_);
                    leanh::lean_dec(v_a_5129_);
                    v___x_5135_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_5135_, 0, v_snd_5134_);
                    if v_isShared_5132_ == 0 {
                        leanh::lean_ctor_set(v___x_5131_, 0, v___x_5135_);
                        v___x_5137_ = v___x_5131_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_5138_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_5138_, 0, v___x_5135_);
                        v___x_5137_ = v_reuseFailAlloc_5138_;
                        state = 2;
                        continue;
                    }
                } else {
                    leanh::lean_inc_ref(v_fst_5133_);
                    leanh::lean_dec(v_a_5129_);
                    v_val_5139_ = leanh::lean_ctor_get(v_fst_5133_, 0);
                    leanh::lean_inc(v_val_5139_);
                    leanh::lean_dec_ref_known(v_fst_5133_, 1);
                    if v_isShared_5132_ == 0 {
                        leanh::lean_ctor_set(v___x_5131_, 0, v_val_5139_);
                        v___x_5141_ = v___x_5131_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_5142_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_5142_, 0, v_val_5139_);
                        v___x_5141_ = v_reuseFailAlloc_5142_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_5137_;
            }
            3 => {
                return v___x_5141_;
            }
            4 => {
                if v_isShared_5147_ == 0 {
                    v___x_5149_ = v___x_5146_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_5150_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5150_, 0, v_a_5144_);
                    v___x_5149_ = v_reuseFailAlloc_5150_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_5149_;
            }
            6 => {
                v_fst_5162_ = leanh::lean_ctor_get(v_a_5158_, 0);
                if leanh::lean_obj_tag(v_fst_5162_) == 0 {
                    v_snd_5163_ = leanh::lean_ctor_get(v_a_5158_, 1);
                    leanh::lean_inc(v_snd_5163_);
                    leanh::lean_dec(v_a_5158_);
                    v___x_5164_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_5164_, 0, v_snd_5163_);
                    if v_isShared_5161_ == 0 {
                        leanh::lean_ctor_set(v___x_5160_, 0, v___x_5164_);
                        v___x_5166_ = v___x_5160_;
                        state = 7;
                        continue;
                    } else {
                        v_reuseFailAlloc_5167_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_5167_, 0, v___x_5164_);
                        v___x_5166_ = v_reuseFailAlloc_5167_;
                        state = 7;
                        continue;
                    }
                } else {
                    leanh::lean_inc_ref(v_fst_5162_);
                    leanh::lean_dec(v_a_5158_);
                    v_val_5168_ = leanh::lean_ctor_get(v_fst_5162_, 0);
                    leanh::lean_inc(v_val_5168_);
                    leanh::lean_dec_ref_known(v_fst_5162_, 1);
                    if v_isShared_5161_ == 0 {
                        leanh::lean_ctor_set(v___x_5160_, 0, v_val_5168_);
                        v___x_5170_ = v___x_5160_;
                        state = 8;
                        continue;
                    } else {
                        v_reuseFailAlloc_5171_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_5171_, 0, v_val_5168_);
                        v___x_5170_ = v_reuseFailAlloc_5171_;
                        state = 8;
                        continue;
                    }
                }
            }
            7 => {
                return v___x_5166_;
            }
            8 => {
                return v___x_5170_;
            }
            9 => {
                if v_isShared_5176_ == 0 {
                    v___x_5178_ = v___x_5175_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_5179_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5179_, 0, v_a_5173_);
                    v___x_5178_ = v_reuseFailAlloc_5179_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_5178_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Try_Collect_0__Lean_Meta_Try_Collector_main_go_spec__0_spec__0_spec__1(
    mut v_init_5181_: *mut leanh::LeanObject,
    mut v_as_5182_: *mut leanh::LeanObject,
    mut v_sz_5183_: usize,
    mut v_i_5184_: usize,
    mut v_b_5185_: *mut leanh::LeanObject,
    mut v___y_5186_: *mut leanh::LeanObject,
    mut v___y_5187_: *mut leanh::LeanObject,
    mut v___y_5188_: *mut leanh::LeanObject,
    mut v___y_5189_: *mut leanh::LeanObject,
    mut v___y_5190_: *mut leanh::LeanObject,
    mut v___y_5191_: *mut leanh::LeanObject,
    mut v___y_5192_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5194_: u8 = 0;
    let mut v___x_5195_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_5196_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5198_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5199_: u8 = 0;
    let mut v_a_5200_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5201_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5202_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5204_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5205_: u8 = 0;
    let mut v___x_5206_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5208_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5210_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5211_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5212_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5213_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5214_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5216_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5217_: usize = 0;
    let mut v___x_5218_: usize = 0;
    let mut v_reuseFailAlloc_5220_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5221_: u8 = 0;
    let mut v_a_5222_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5224_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5225_: u8 = 0;
    let mut v___x_5227_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5228_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5229_: u8 = 0;
    let mut v_isSharedCheck_5230_: u8 = 0;
    let mut v_unused_5231_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5194_ = lean_usize_dec_lt(v_i_5184_, v_sz_5183_);
                if v___x_5194_ == 0 {
                    v___x_5195_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_5195_, 0, v_b_5185_);
                    return v___x_5195_;
                } else {
                    v_snd_5196_ = leanh::lean_ctor_get(v_b_5185_, 1);
                    v_isSharedCheck_5230_ = (!leanh::lean_is_exclusive(v_b_5185_)) as u8;
                    if v_isSharedCheck_5230_ == 0 {
                        v_unused_5231_ = leanh::lean_ctor_get(v_b_5185_, 0);
                        leanh::lean_dec(v_unused_5231_);
                        v___x_5198_ = v_b_5185_;
                        v_isShared_5199_ = v_isSharedCheck_5230_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_snd_5196_);
                        leanh::lean_dec(v_b_5185_);
                        v___x_5198_ = leanh::lean_box(0);
                        v_isShared_5199_ = v_isSharedCheck_5230_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_a_5200_ = lean_array_uget_borrowed(v_as_5182_, v_i_5184_);
                leanh::lean_inc(v_snd_5196_);
                v___x_5201_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Try_Collect_0__Lean_Meta_Try_Collector_main_go_spec__0_spec__0(v_init_5181_, v_a_5200_, v_snd_5196_, v___y_5186_, v___y_5187_, v___y_5188_, v___y_5189_, v___y_5190_, v___y_5191_, v___y_5192_);
                if leanh::lean_obj_tag(v___x_5201_) == 0 {
                    v_a_5202_ = leanh::lean_ctor_get(v___x_5201_, 0);
                    v_isSharedCheck_5221_ = (!leanh::lean_is_exclusive(v___x_5201_)) as u8;
                    if v_isSharedCheck_5221_ == 0 {
                        v___x_5204_ = v___x_5201_;
                        v_isShared_5205_ = v_isSharedCheck_5221_;
                        state = 2;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_5202_);
                        leanh::lean_dec(v___x_5201_);
                        v___x_5204_ = leanh::lean_box(0);
                        v_isShared_5205_ = v_isSharedCheck_5221_;
                        state = 2;
                        continue;
                    }
                } else {
                    leanh::lean_del_object(v___x_5198_);
                    leanh::lean_dec(v_snd_5196_);
                    v_a_5222_ = leanh::lean_ctor_get(v___x_5201_, 0);
                    v_isSharedCheck_5229_ = (!leanh::lean_is_exclusive(v___x_5201_)) as u8;
                    if v_isSharedCheck_5229_ == 0 {
                        v___x_5224_ = v___x_5201_;
                        v_isShared_5225_ = v_isSharedCheck_5229_;
                        state = 6;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_5222_);
                        leanh::lean_dec(v___x_5201_);
                        v___x_5224_ = leanh::lean_box(0);
                        v_isShared_5225_ = v_isSharedCheck_5229_;
                        state = 6;
                        continue;
                    }
                }
            }
            2 => {
                if leanh::lean_obj_tag(v_a_5202_) == 0 {
                    v___x_5206_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_5206_, 0, v_a_5202_);
                    if v_isShared_5199_ == 0 {
                        leanh::lean_ctor_set(v___x_5198_, 0, v___x_5206_);
                        v___x_5208_ = v___x_5198_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_5212_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_5212_, 0, v___x_5206_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_5212_, 1, v_snd_5196_);
                        v___x_5208_ = v_reuseFailAlloc_5212_;
                        state = 3;
                        continue;
                    }
                } else {
                    leanh::lean_del_object(v___x_5204_);
                    leanh::lean_dec(v_snd_5196_);
                    v_a_5213_ = leanh::lean_ctor_get(v_a_5202_, 0);
                    leanh::lean_inc(v_a_5213_);
                    leanh::lean_dec_ref_known(v_a_5202_, 1);
                    v___x_5214_ = leanh::lean_box(0);
                    if v_isShared_5199_ == 0 {
                        leanh::lean_ctor_set(v___x_5198_, 1, v_a_5213_);
                        leanh::lean_ctor_set(v___x_5198_, 0, v___x_5214_);
                        v___x_5216_ = v___x_5198_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_5220_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_5220_, 0, v___x_5214_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_5220_, 1, v_a_5213_);
                        v___x_5216_ = v_reuseFailAlloc_5220_;
                        state = 5;
                        continue;
                    }
                }
            }
            3 => {
                if v_isShared_5205_ == 0 {
                    leanh::lean_ctor_set(v___x_5204_, 0, v___x_5208_);
                    v___x_5210_ = v___x_5204_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_5211_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5211_, 0, v___x_5208_);
                    v___x_5210_ = v_reuseFailAlloc_5211_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_5210_;
            }
            5 => {
                v___x_5217_ = 1usize;
                v___x_5218_ = lean_usize_add(v_i_5184_, v___x_5217_);
                v_i_5184_ = v___x_5218_;
                v_b_5185_ = v___x_5216_;
                state = 0;
                continue;
            }
            6 => {
                if v_isShared_5225_ == 0 {
                    v___x_5227_ = v___x_5224_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_5228_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5228_, 0, v_a_5222_);
                    v___x_5227_ = v_reuseFailAlloc_5228_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_5227_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Try_Collect_0__Lean_Meta_Try_Collector_main_go_spec__0_spec__0_spec__1___boxed(
    mut v_init_5232_: *mut leanh::LeanObject,
    mut v_as_5233_: *mut leanh::LeanObject,
    mut v_sz_5234_: *mut leanh::LeanObject,
    mut v_i_5235_: *mut leanh::LeanObject,
    mut v_b_5236_: *mut leanh::LeanObject,
    mut v___y_5237_: *mut leanh::LeanObject,
    mut v___y_5238_: *mut leanh::LeanObject,
    mut v___y_5239_: *mut leanh::LeanObject,
    mut v___y_5240_: *mut leanh::LeanObject,
    mut v___y_5241_: *mut leanh::LeanObject,
    mut v___y_5242_: *mut leanh::LeanObject,
    mut v___y_5243_: *mut leanh::LeanObject,
    mut v___y_5244_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_sz_boxed_5245_: usize = 0;
    let mut v_i_boxed_5246_: usize = 0;
    let mut v_res_5247_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_5245_ = leanh::lean_unbox_usize(v_sz_5234_);
    leanh::lean_dec(v_sz_5234_);
    v_i_boxed_5246_ = leanh::lean_unbox_usize(v_i_5235_);
    leanh::lean_dec(v_i_5235_);
    v_res_5247_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Try_Collect_0__Lean_Meta_Try_Collector_main_go_spec__0_spec__0_spec__1(v_init_5232_, v_as_5233_, v_sz_boxed_5245_, v_i_boxed_5246_, v_b_5236_, v___y_5237_, v___y_5238_, v___y_5239_, v___y_5240_, v___y_5241_, v___y_5242_, v___y_5243_);
    leanh::lean_dec(v___y_5243_);
    leanh::lean_dec_ref(v___y_5242_);
    leanh::lean_dec(v___y_5241_);
    leanh::lean_dec_ref(v___y_5240_);
    leanh::lean_dec(v___y_5239_);
    leanh::lean_dec_ref(v___y_5238_);
    leanh::lean_dec(v___y_5237_);
    leanh::lean_dec_ref(v_as_5233_);
    return v_res_5247_;
}
pub unsafe fn l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Try_Collect_0__Lean_Meta_Try_Collector_main_go_spec__0_spec__0___boxed(
    mut v_init_5248_: *mut leanh::LeanObject,
    mut v_n_5249_: *mut leanh::LeanObject,
    mut v_b_5250_: *mut leanh::LeanObject,
    mut v___y_5251_: *mut leanh::LeanObject,
    mut v___y_5252_: *mut leanh::LeanObject,
    mut v___y_5253_: *mut leanh::LeanObject,
    mut v___y_5254_: *mut leanh::LeanObject,
    mut v___y_5255_: *mut leanh::LeanObject,
    mut v___y_5256_: *mut leanh::LeanObject,
    mut v___y_5257_: *mut leanh::LeanObject,
    mut v___y_5258_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5259_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5259_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Try_Collect_0__Lean_Meta_Try_Collector_main_go_spec__0_spec__0(v_init_5248_, v_n_5249_, v_b_5250_, v___y_5251_, v___y_5252_, v___y_5253_, v___y_5254_, v___y_5255_, v___y_5256_, v___y_5257_);
    leanh::lean_dec(v___y_5257_);
    leanh::lean_dec_ref(v___y_5256_);
    leanh::lean_dec(v___y_5255_);
    leanh::lean_dec_ref(v___y_5254_);
    leanh::lean_dec(v___y_5253_);
    leanh::lean_dec_ref(v___y_5252_);
    leanh::lean_dec(v___y_5251_);
    leanh::lean_dec_ref(v_n_5249_);
    return v_res_5259_;
}
pub unsafe fn l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Try_Collect_0__Lean_Meta_Try_Collector_main_go_spec__0(
    mut v_t_5260_: *mut leanh::LeanObject,
    mut v_init_5261_: *mut leanh::LeanObject,
    mut v___y_5262_: *mut leanh::LeanObject,
    mut v___y_5263_: *mut leanh::LeanObject,
    mut v___y_5264_: *mut leanh::LeanObject,
    mut v___y_5265_: *mut leanh::LeanObject,
    mut v___y_5266_: *mut leanh::LeanObject,
    mut v___y_5267_: *mut leanh::LeanObject,
    mut v___y_5268_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_root_5270_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_5271_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5272_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5273_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5275_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5276_: u8 = 0;
    let mut v_a_5277_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5279_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5280_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5281_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5282_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5283_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_5284_: usize = 0;
    let mut v___x_5285_: usize = 0;
    let mut v___x_5286_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5287_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5289_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5290_: u8 = 0;
    let mut v_fst_5291_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_5292_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5294_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5295_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_5296_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5298_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5299_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5300_: u8 = 0;
    let mut v_a_5301_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5303_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5304_: u8 = 0;
    let mut v___x_5306_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5307_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5308_: u8 = 0;
    let mut v_isSharedCheck_5309_: u8 = 0;
    let mut v_a_5310_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5312_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5313_: u8 = 0;
    let mut v___x_5315_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5316_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5317_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_root_5270_ = leanh::lean_ctor_get(v_t_5260_, 0);
                v_tail_5271_ = leanh::lean_ctor_get(v_t_5260_, 1);
                v___x_5272_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Try_Collect_0__Lean_Meta_Try_Collector_main_go_spec__0_spec__0(v_init_5261_, v_root_5270_, v_init_5261_, v___y_5262_, v___y_5263_, v___y_5264_, v___y_5265_, v___y_5266_, v___y_5267_, v___y_5268_);
                if leanh::lean_obj_tag(v___x_5272_) == 0 {
                    v_a_5273_ = leanh::lean_ctor_get(v___x_5272_, 0);
                    v_isSharedCheck_5309_ = (!leanh::lean_is_exclusive(v___x_5272_)) as u8;
                    if v_isSharedCheck_5309_ == 0 {
                        v___x_5275_ = v___x_5272_;
                        v_isShared_5276_ = v_isSharedCheck_5309_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_5273_);
                        leanh::lean_dec(v___x_5272_);
                        v___x_5275_ = leanh::lean_box(0);
                        v_isShared_5276_ = v_isSharedCheck_5309_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_5310_ = leanh::lean_ctor_get(v___x_5272_, 0);
                    v_isSharedCheck_5317_ = (!leanh::lean_is_exclusive(v___x_5272_)) as u8;
                    if v_isSharedCheck_5317_ == 0 {
                        v___x_5312_ = v___x_5272_;
                        v_isShared_5313_ = v_isSharedCheck_5317_;
                        state = 8;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_5310_);
                        leanh::lean_dec(v___x_5272_);
                        v___x_5312_ = leanh::lean_box(0);
                        v_isShared_5313_ = v_isSharedCheck_5317_;
                        state = 8;
                        continue;
                    }
                }
            }
            1 => {
                if leanh::lean_obj_tag(v_a_5273_) == 0 {
                    v_a_5277_ = leanh::lean_ctor_get(v_a_5273_, 0);
                    leanh::lean_inc(v_a_5277_);
                    leanh::lean_dec_ref_known(v_a_5273_, 1);
                    if v_isShared_5276_ == 0 {
                        leanh::lean_ctor_set(v___x_5275_, 0, v_a_5277_);
                        v___x_5279_ = v___x_5275_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_5280_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_5280_, 0, v_a_5277_);
                        v___x_5279_ = v_reuseFailAlloc_5280_;
                        state = 2;
                        continue;
                    }
                } else {
                    leanh::lean_del_object(v___x_5275_);
                    v_a_5281_ = leanh::lean_ctor_get(v_a_5273_, 0);
                    leanh::lean_inc(v_a_5281_);
                    leanh::lean_dec_ref_known(v_a_5273_, 1);
                    v___x_5282_ = leanh::lean_box(0);
                    v___x_5283_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_5283_, 0, v___x_5282_);
                    leanh::lean_ctor_set(v___x_5283_, 1, v_a_5281_);
                    v_sz_5284_ = lean_array_size(v_tail_5271_);
                    v___x_5285_ = 0usize;
                    v___x_5286_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Try_Collect_0__Lean_Meta_Try_Collector_main_go_spec__0_spec__1(v_tail_5271_, v_sz_5284_, v___x_5285_, v___x_5283_, v___y_5262_, v___y_5263_, v___y_5264_, v___y_5265_, v___y_5266_, v___y_5267_, v___y_5268_);
                    if leanh::lean_obj_tag(v___x_5286_) == 0 {
                        v_a_5287_ = leanh::lean_ctor_get(v___x_5286_, 0);
                        v_isSharedCheck_5300_ =
                            (!leanh::lean_is_exclusive(v___x_5286_)) as u8;
                        if v_isSharedCheck_5300_ == 0 {
                            v___x_5289_ = v___x_5286_;
                            v_isShared_5290_ = v_isSharedCheck_5300_;
                            state = 3;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_5287_);
                            leanh::lean_dec(v___x_5286_);
                            v___x_5289_ = leanh::lean_box(0);
                            v_isShared_5290_ = v_isSharedCheck_5300_;
                            state = 3;
                            continue;
                        }
                    } else {
                        v_a_5301_ = leanh::lean_ctor_get(v___x_5286_, 0);
                        v_isSharedCheck_5308_ =
                            (!leanh::lean_is_exclusive(v___x_5286_)) as u8;
                        if v_isSharedCheck_5308_ == 0 {
                            v___x_5303_ = v___x_5286_;
                            v_isShared_5304_ = v_isSharedCheck_5308_;
                            state = 6;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_5301_);
                            leanh::lean_dec(v___x_5286_);
                            v___x_5303_ = leanh::lean_box(0);
                            v_isShared_5304_ = v_isSharedCheck_5308_;
                            state = 6;
                            continue;
                        }
                    }
                }
            }
            2 => {
                return v___x_5279_;
            }
            3 => {
                v_fst_5291_ = leanh::lean_ctor_get(v_a_5287_, 0);
                if leanh::lean_obj_tag(v_fst_5291_) == 0 {
                    v_snd_5292_ = leanh::lean_ctor_get(v_a_5287_, 1);
                    leanh::lean_inc(v_snd_5292_);
                    leanh::lean_dec(v_a_5287_);
                    if v_isShared_5290_ == 0 {
                        leanh::lean_ctor_set(v___x_5289_, 0, v_snd_5292_);
                        v___x_5294_ = v___x_5289_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_5295_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_5295_, 0, v_snd_5292_);
                        v___x_5294_ = v_reuseFailAlloc_5295_;
                        state = 4;
                        continue;
                    }
                } else {
                    leanh::lean_inc_ref(v_fst_5291_);
                    leanh::lean_dec(v_a_5287_);
                    v_val_5296_ = leanh::lean_ctor_get(v_fst_5291_, 0);
                    leanh::lean_inc(v_val_5296_);
                    leanh::lean_dec_ref_known(v_fst_5291_, 1);
                    if v_isShared_5290_ == 0 {
                        leanh::lean_ctor_set(v___x_5289_, 0, v_val_5296_);
                        v___x_5298_ = v___x_5289_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_5299_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_5299_, 0, v_val_5296_);
                        v___x_5298_ = v_reuseFailAlloc_5299_;
                        state = 5;
                        continue;
                    }
                }
            }
            4 => {
                return v___x_5294_;
            }
            5 => {
                return v___x_5298_;
            }
            6 => {
                if v_isShared_5304_ == 0 {
                    v___x_5306_ = v___x_5303_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_5307_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5307_, 0, v_a_5301_);
                    v___x_5306_ = v_reuseFailAlloc_5307_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_5306_;
            }
            8 => {
                if v_isShared_5313_ == 0 {
                    v___x_5315_ = v___x_5312_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_5316_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5316_, 0, v_a_5310_);
                    v___x_5315_ = v_reuseFailAlloc_5316_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_5315_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Try_Collect_0__Lean_Meta_Try_Collector_main_go_spec__0___boxed(
    mut v_t_5318_: *mut leanh::LeanObject,
    mut v_init_5319_: *mut leanh::LeanObject,
    mut v___y_5320_: *mut leanh::LeanObject,
    mut v___y_5321_: *mut leanh::LeanObject,
    mut v___y_5322_: *mut leanh::LeanObject,
    mut v___y_5323_: *mut leanh::LeanObject,
    mut v___y_5324_: *mut leanh::LeanObject,
    mut v___y_5325_: *mut leanh::LeanObject,
    mut v___y_5326_: *mut leanh::LeanObject,
    mut v___y_5327_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5328_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5328_ = l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Try_Collect_0__Lean_Meta_Try_Collector_main_go_spec__0(v_t_5318_, v_init_5319_, v___y_5320_, v___y_5321_, v___y_5322_, v___y_5323_, v___y_5324_, v___y_5325_, v___y_5326_);
    leanh::lean_dec(v___y_5326_);
    leanh::lean_dec_ref(v___y_5325_);
    leanh::lean_dec(v___y_5324_);
    leanh::lean_dec_ref(v___y_5323_);
    leanh::lean_dec(v___y_5322_);
    leanh::lean_dec_ref(v___y_5321_);
    leanh::lean_dec(v___y_5320_);
    leanh::lean_dec_ref(v_t_5318_);
    return v_res_5328_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Try_Collect_0__Lean_Meta_Try_Collector_main_go(
    mut v_mvarId_5329_: *mut leanh::LeanObject,
    mut v_a_5330_: *mut leanh::LeanObject,
    mut v_a_5331_: *mut leanh::LeanObject,
    mut v_a_5332_: *mut leanh::LeanObject,
    mut v_a_5333_: *mut leanh::LeanObject,
    mut v_a_5334_: *mut leanh::LeanObject,
    mut v_a_5335_: *mut leanh::LeanObject,
    mut v_a_5336_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___y_5339_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5340_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5341_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5342_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5343_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5344_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5345_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5346_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5347_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5348_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5349_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5351_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5352_: u8 = 0;
    let mut v___x_5354_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5355_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5356_: u8 = 0;
    let mut v_targetOnly_5357_: u8 = 0;
    let mut v_lctx_5358_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_decls_5359_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5360_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5361_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_targetOnly_5357_ = leanh::lean_ctor_get_uint8(
                    v_a_5331_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 1 + 2) as u32,
                );
                if v_targetOnly_5357_ == 0 {
                    v_lctx_5358_ = leanh::lean_ctor_get(v_a_5333_, 2);
                    v_decls_5359_ = leanh::lean_ctor_get(v_lctx_5358_, 1);
                    v___x_5360_ = leanh::lean_box(0);
                    v___x_5361_ = l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Try_Collect_0__Lean_Meta_Try_Collector_main_go_spec__0(v_decls_5359_, v___x_5360_, v_a_5330_, v_a_5331_, v_a_5332_, v_a_5333_, v_a_5334_, v_a_5335_, v_a_5336_);
                    if leanh::lean_obj_tag(v___x_5361_) == 0 {
                        leanh::lean_dec_ref_known(v___x_5361_, 1);
                        v___y_5339_ = v_a_5330_;
                        v___y_5340_ = v_a_5331_;
                        v___y_5341_ = v_a_5332_;
                        v___y_5342_ = v_a_5333_;
                        v___y_5343_ = v_a_5334_;
                        v___y_5344_ = v_a_5335_;
                        v___y_5345_ = v_a_5336_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_dec(v_mvarId_5329_);
                        return v___x_5361_;
                    }
                } else {
                    v___y_5339_ = v_a_5330_;
                    v___y_5340_ = v_a_5331_;
                    v___y_5341_ = v_a_5332_;
                    v___y_5342_ = v_a_5333_;
                    v___y_5343_ = v_a_5334_;
                    v___y_5344_ = v_a_5335_;
                    v___y_5345_ = v_a_5336_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_5346_ = l_Lean_MVarId_getType(
                    v_mvarId_5329_,
                    v___y_5342_,
                    v___y_5343_,
                    v___y_5344_,
                    v___y_5345_,
                );
                if leanh::lean_obj_tag(v___x_5346_) == 0 {
                    v_a_5347_ = leanh::lean_ctor_get(v___x_5346_, 0);
                    leanh::lean_inc(v_a_5347_);
                    leanh::lean_dec_ref_known(v___x_5346_, 1);
                    v___x_5348_ = l_Lean_Meta_Try_Collector_visit(
                        v_a_5347_,
                        v___y_5339_,
                        v___y_5340_,
                        v___y_5341_,
                        v___y_5342_,
                        v___y_5343_,
                        v___y_5344_,
                        v___y_5345_,
                    );
                    return v___x_5348_;
                } else {
                    v_a_5349_ = leanh::lean_ctor_get(v___x_5346_, 0);
                    v_isSharedCheck_5356_ = (!leanh::lean_is_exclusive(v___x_5346_)) as u8;
                    if v_isSharedCheck_5356_ == 0 {
                        v___x_5351_ = v___x_5346_;
                        v_isShared_5352_ = v_isSharedCheck_5356_;
                        state = 2;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_5349_);
                        leanh::lean_dec(v___x_5346_);
                        v___x_5351_ = leanh::lean_box(0);
                        v_isShared_5352_ = v_isSharedCheck_5356_;
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                if v_isShared_5352_ == 0 {
                    v___x_5354_ = v___x_5351_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_5355_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5355_, 0, v_a_5349_);
                    v___x_5354_ = v_reuseFailAlloc_5355_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_5354_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_Try_Collect_0__Lean_Meta_Try_Collector_main_go___boxed(
    mut v_mvarId_5362_: *mut leanh::LeanObject,
    mut v_a_5363_: *mut leanh::LeanObject,
    mut v_a_5364_: *mut leanh::LeanObject,
    mut v_a_5365_: *mut leanh::LeanObject,
    mut v_a_5366_: *mut leanh::LeanObject,
    mut v_a_5367_: *mut leanh::LeanObject,
    mut v_a_5368_: *mut leanh::LeanObject,
    mut v_a_5369_: *mut leanh::LeanObject,
    mut v_a_5370_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5371_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5371_ = l___private_Lean_Meta_Tactic_Try_Collect_0__Lean_Meta_Try_Collector_main_go(
        v_mvarId_5362_,
        v_a_5363_,
        v_a_5364_,
        v_a_5365_,
        v_a_5366_,
        v_a_5367_,
        v_a_5368_,
        v_a_5369_,
    );
    leanh::lean_dec(v_a_5369_);
    leanh::lean_dec_ref(v_a_5368_);
    leanh::lean_dec(v_a_5367_);
    leanh::lean_dec_ref(v_a_5366_);
    leanh::lean_dec(v_a_5365_);
    leanh::lean_dec_ref(v_a_5364_);
    leanh::lean_dec(v_a_5363_);
    return v_res_5371_;
}
pub unsafe fn l_Lean_MVarId_withContext___at___00Lean_Meta_Try_Collector_main_spec__0___redArg(
    mut v_mvarId_5372_: *mut leanh::LeanObject,
    mut v_x_5373_: *mut leanh::LeanObject,
    mut v___y_5374_: *mut leanh::LeanObject,
    mut v___y_5375_: *mut leanh::LeanObject,
    mut v___y_5376_: *mut leanh::LeanObject,
    mut v___y_5377_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5379_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5380_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5382_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5383_: u8 = 0;
    let mut v___x_5385_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5386_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5387_: u8 = 0;
    let mut v_a_5388_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5390_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5391_: u8 = 0;
    let mut v___x_5393_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5394_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5395_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5379_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(
                    leanh::lean_box(0),
                    v_mvarId_5372_,
                    v_x_5373_,
                    v___y_5374_,
                    v___y_5375_,
                    v___y_5376_,
                    v___y_5377_,
                );
                if leanh::lean_obj_tag(v___x_5379_) == 0 {
                    v_a_5380_ = leanh::lean_ctor_get(v___x_5379_, 0);
                    v_isSharedCheck_5387_ = (!leanh::lean_is_exclusive(v___x_5379_)) as u8;
                    if v_isSharedCheck_5387_ == 0 {
                        v___x_5382_ = v___x_5379_;
                        v_isShared_5383_ = v_isSharedCheck_5387_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_5380_);
                        leanh::lean_dec(v___x_5379_);
                        v___x_5382_ = leanh::lean_box(0);
                        v_isShared_5383_ = v_isSharedCheck_5387_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_5388_ = leanh::lean_ctor_get(v___x_5379_, 0);
                    v_isSharedCheck_5395_ = (!leanh::lean_is_exclusive(v___x_5379_)) as u8;
                    if v_isSharedCheck_5395_ == 0 {
                        v___x_5390_ = v___x_5379_;
                        v_isShared_5391_ = v_isSharedCheck_5395_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_5388_);
                        leanh::lean_dec(v___x_5379_);
                        v___x_5390_ = leanh::lean_box(0);
                        v_isShared_5391_ = v_isSharedCheck_5395_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_5383_ == 0 {
                    v___x_5385_ = v___x_5382_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5386_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5386_, 0, v_a_5380_);
                    v___x_5385_ = v_reuseFailAlloc_5386_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_5385_;
            }
            3 => {
                if v_isShared_5391_ == 0 {
                    v___x_5393_ = v___x_5390_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_5394_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5394_, 0, v_a_5388_);
                    v___x_5393_ = v_reuseFailAlloc_5394_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_5393_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_MVarId_withContext___at___00Lean_Meta_Try_Collector_main_spec__0___redArg___boxed(
    mut v_mvarId_5396_: *mut leanh::LeanObject,
    mut v_x_5397_: *mut leanh::LeanObject,
    mut v___y_5398_: *mut leanh::LeanObject,
    mut v___y_5399_: *mut leanh::LeanObject,
    mut v___y_5400_: *mut leanh::LeanObject,
    mut v___y_5401_: *mut leanh::LeanObject,
    mut v___y_5402_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5403_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5403_ = l_Lean_MVarId_withContext___at___00Lean_Meta_Try_Collector_main_spec__0___redArg(
        v_mvarId_5396_,
        v_x_5397_,
        v___y_5398_,
        v___y_5399_,
        v___y_5400_,
        v___y_5401_,
    );
    leanh::lean_dec(v___y_5401_);
    leanh::lean_dec_ref(v___y_5400_);
    leanh::lean_dec(v___y_5399_);
    leanh::lean_dec_ref(v___y_5398_);
    return v_res_5403_;
}
pub unsafe fn l_Lean_MVarId_withContext___at___00Lean_Meta_Try_Collector_main_spec__0(
    mut v_00_u03b1_5404_: *mut leanh::LeanObject,
    mut v_mvarId_5405_: *mut leanh::LeanObject,
    mut v_x_5406_: *mut leanh::LeanObject,
    mut v___y_5407_: *mut leanh::LeanObject,
    mut v___y_5408_: *mut leanh::LeanObject,
    mut v___y_5409_: *mut leanh::LeanObject,
    mut v___y_5410_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5412_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5412_ = l_Lean_MVarId_withContext___at___00Lean_Meta_Try_Collector_main_spec__0___redArg(
        v_mvarId_5405_,
        v_x_5406_,
        v___y_5407_,
        v___y_5408_,
        v___y_5409_,
        v___y_5410_,
    );
    return v___x_5412_;
}
pub unsafe fn l_Lean_MVarId_withContext___at___00Lean_Meta_Try_Collector_main_spec__0___boxed(
    mut v_00_u03b1_5413_: *mut leanh::LeanObject,
    mut v_mvarId_5414_: *mut leanh::LeanObject,
    mut v_x_5415_: *mut leanh::LeanObject,
    mut v___y_5416_: *mut leanh::LeanObject,
    mut v___y_5417_: *mut leanh::LeanObject,
    mut v___y_5418_: *mut leanh::LeanObject,
    mut v___y_5419_: *mut leanh::LeanObject,
    mut v___y_5420_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5421_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5421_ = l_Lean_MVarId_withContext___at___00Lean_Meta_Try_Collector_main_spec__0(
        v_00_u03b1_5413_,
        v_mvarId_5414_,
        v_x_5415_,
        v___y_5416_,
        v___y_5417_,
        v___y_5418_,
        v___y_5419_,
    );
    leanh::lean_dec(v___y_5419_);
    leanh::lean_dec_ref(v___y_5418_);
    leanh::lean_dec(v___y_5417_);
    leanh::lean_dec_ref(v___y_5416_);
    return v_res_5421_;
}
pub unsafe fn l_Lean_Meta_Try_Collector_main___lam__0(
    mut v___x_5422_: *mut leanh::LeanObject,
    mut v___x_5423_: *mut leanh::LeanObject,
    mut v_mvarId_5424_: *mut leanh::LeanObject,
    mut v_config_5425_: *mut leanh::LeanObject,
    mut v___y_5426_: *mut leanh::LeanObject,
    mut v___y_5427_: *mut leanh::LeanObject,
    mut v___y_5428_: *mut leanh::LeanObject,
    mut v___y_5429_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5431_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5432_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5433_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5435_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5436_: u8 = 0;
    let mut v___x_5437_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5438_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5440_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5441_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5442_: u8 = 0;
    let mut v_unused_5443_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5444_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5446_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5447_: u8 = 0;
    let mut v___x_5449_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5450_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5451_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5431_ = lean_st_mk_ref(v___x_5422_);
                v___x_5432_ = lean_st_mk_ref(v___x_5423_);
                v___x_5433_ =
                    l___private_Lean_Meta_Tactic_Try_Collect_0__Lean_Meta_Try_Collector_main_go(
                        v_mvarId_5424_,
                        v___x_5432_,
                        v_config_5425_,
                        v___x_5431_,
                        v___y_5426_,
                        v___y_5427_,
                        v___y_5428_,
                        v___y_5429_,
                    );
                if leanh::lean_obj_tag(v___x_5433_) == 0 {
                    v_isSharedCheck_5442_ = (!leanh::lean_is_exclusive(v___x_5433_)) as u8;
                    if v_isSharedCheck_5442_ == 0 {
                        v_unused_5443_ = leanh::lean_ctor_get(v___x_5433_, 0);
                        leanh::lean_dec(v_unused_5443_);
                        v___x_5435_ = v___x_5433_;
                        v_isShared_5436_ = v_isSharedCheck_5442_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_dec(v___x_5433_);
                        v___x_5435_ = leanh::lean_box(0);
                        v_isShared_5436_ = v_isSharedCheck_5442_;
                        state = 1;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v___x_5432_);
                    leanh::lean_dec(v___x_5431_);
                    v_a_5444_ = leanh::lean_ctor_get(v___x_5433_, 0);
                    v_isSharedCheck_5451_ = (!leanh::lean_is_exclusive(v___x_5433_)) as u8;
                    if v_isSharedCheck_5451_ == 0 {
                        v___x_5446_ = v___x_5433_;
                        v_isShared_5447_ = v_isSharedCheck_5451_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_5444_);
                        leanh::lean_dec(v___x_5433_);
                        v___x_5446_ = leanh::lean_box(0);
                        v_isShared_5447_ = v_isSharedCheck_5451_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v___x_5437_ = lean_st_ref_get(v___x_5432_);
                leanh::lean_dec(v___x_5432_);
                leanh::lean_dec(v___x_5437_);
                v___x_5438_ = lean_st_ref_get(v___x_5431_);
                leanh::lean_dec(v___x_5431_);
                if v_isShared_5436_ == 0 {
                    leanh::lean_ctor_set(v___x_5435_, 0, v___x_5438_);
                    v___x_5440_ = v___x_5435_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5441_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5441_, 0, v___x_5438_);
                    v___x_5440_ = v_reuseFailAlloc_5441_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_5440_;
            }
            3 => {
                if v_isShared_5447_ == 0 {
                    v___x_5449_ = v___x_5446_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_5450_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5450_, 0, v_a_5444_);
                    v___x_5449_ = v_reuseFailAlloc_5450_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_5449_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Try_Collector_main___lam__0___boxed(
    mut v___x_5452_: *mut leanh::LeanObject,
    mut v___x_5453_: *mut leanh::LeanObject,
    mut v_mvarId_5454_: *mut leanh::LeanObject,
    mut v_config_5455_: *mut leanh::LeanObject,
    mut v___y_5456_: *mut leanh::LeanObject,
    mut v___y_5457_: *mut leanh::LeanObject,
    mut v___y_5458_: *mut leanh::LeanObject,
    mut v___y_5459_: *mut leanh::LeanObject,
    mut v___y_5460_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5461_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5461_ = l_Lean_Meta_Try_Collector_main___lam__0(
        v___x_5452_,
        v___x_5453_,
        v_mvarId_5454_,
        v_config_5455_,
        v___y_5456_,
        v___y_5457_,
        v___y_5458_,
        v___y_5459_,
    );
    leanh::lean_dec(v___y_5459_);
    leanh::lean_dec_ref(v___y_5458_);
    leanh::lean_dec(v___y_5457_);
    leanh::lean_dec_ref(v___y_5456_);
    leanh::lean_dec_ref(v_config_5455_);
    return v_res_5461_;
}
pub unsafe fn _init_l_Lean_Meta_Try_Collector_main___closed__0() -> *mut leanh::LeanObject {
    let mut v___x_5462_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5463_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5462_ = leanh::lean_unsigned_to_nat(64);
    v___x_5463_ = l_Lean_mkPtrSet___redArg(v___x_5462_);
    return v___x_5463_;
}
pub unsafe fn _init_l_Lean_Meta_Try_Collector_main___closed__2() -> *mut leanh::LeanObject {
    let mut v___x_5466_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5467_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5468_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5466_ = leanh::lean_box(0);
    v___x_5467_ = leanh::lean_unsigned_to_nat(16);
    v___x_5468_ = lean_mk_array(v___x_5467_, v___x_5466_);
    return v___x_5468_;
}
pub unsafe fn _init_l_Lean_Meta_Try_Collector_main___closed__3() -> *mut leanh::LeanObject {
    let mut v___x_5469_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5470_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5471_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5469_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Try_Collector_main___closed__2),
        core::ptr::addr_of_mut!(l_Lean_Meta_Try_Collector_main___closed__2_once),
        _init_l_Lean_Meta_Try_Collector_main___closed__2,
    );
    v___x_5470_ = leanh::lean_unsigned_to_nat(0);
    v___x_5471_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_5471_, 0, v___x_5470_);
    leanh::lean_ctor_set(v___x_5471_, 1, v___x_5469_);
    return v___x_5471_;
}
pub unsafe fn _init_l_Lean_Meta_Try_Collector_main___closed__4() -> *mut leanh::LeanObject {
    let mut v___x_5472_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5473_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5474_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5472_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Try_Collector_main___closed__3),
        core::ptr::addr_of_mut!(l_Lean_Meta_Try_Collector_main___closed__3_once),
        _init_l_Lean_Meta_Try_Collector_main___closed__3,
    );
    v___x_5473_ = l_Lean_Meta_Try_Collector_main___closed__1;
    v___x_5474_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_5474_, 0, v___x_5473_);
    leanh::lean_ctor_set(v___x_5474_, 1, v___x_5472_);
    return v___x_5474_;
}
pub unsafe fn _init_l_Lean_Meta_Try_Collector_main___closed__5() -> *mut leanh::LeanObject {
    let mut v___x_5475_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5476_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5477_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5475_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Try_Collector_main___closed__3),
        core::ptr::addr_of_mut!(l_Lean_Meta_Try_Collector_main___closed__3_once),
        _init_l_Lean_Meta_Try_Collector_main___closed__3,
    );
    v___x_5476_ = l_Lean_Meta_Try_Collector_main___closed__1;
    v___x_5477_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_5477_, 0, v___x_5476_);
    leanh::lean_ctor_set(v___x_5477_, 1, v___x_5475_);
    return v___x_5477_;
}
pub unsafe fn _init_l_Lean_Meta_Try_Collector_main___closed__6() -> *mut leanh::LeanObject {
    let mut v___x_5478_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5479_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5480_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5481_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5478_ = l_Lean_Meta_Try_Collector_main___closed__1;
    v___x_5479_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Try_Collector_main___closed__5),
        core::ptr::addr_of_mut!(l_Lean_Meta_Try_Collector_main___closed__5_once),
        _init_l_Lean_Meta_Try_Collector_main___closed__5,
    );
    v___x_5480_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Try_Collector_main___closed__4),
        core::ptr::addr_of_mut!(l_Lean_Meta_Try_Collector_main___closed__4_once),
        _init_l_Lean_Meta_Try_Collector_main___closed__4,
    );
    v___x_5481_ = leanh::lean_alloc_ctor(0, 6, (0) as u32);
    leanh::lean_ctor_set(v___x_5481_, 0, v___x_5480_);
    leanh::lean_ctor_set(v___x_5481_, 1, v___x_5480_);
    leanh::lean_ctor_set(v___x_5481_, 2, v___x_5480_);
    leanh::lean_ctor_set(v___x_5481_, 3, v___x_5479_);
    leanh::lean_ctor_set(v___x_5481_, 4, v___x_5478_);
    leanh::lean_ctor_set(v___x_5481_, 5, v___x_5480_);
    return v___x_5481_;
}
pub unsafe fn l_Lean_Meta_Try_Collector_main(
    mut v_mvarId_5482_: *mut leanh::LeanObject,
    mut v_config_5483_: *mut leanh::LeanObject,
    mut v_a_5484_: *mut leanh::LeanObject,
    mut v_a_5485_: *mut leanh::LeanObject,
    mut v_a_5486_: *mut leanh::LeanObject,
    mut v_a_5487_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5489_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5490_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5491_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5492_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5489_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Try_Collector_main___closed__0),
        core::ptr::addr_of_mut!(l_Lean_Meta_Try_Collector_main___closed__0_once),
        _init_l_Lean_Meta_Try_Collector_main___closed__0,
    );
    v___x_5490_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Try_Collector_main___closed__6),
        core::ptr::addr_of_mut!(l_Lean_Meta_Try_Collector_main___closed__6_once),
        _init_l_Lean_Meta_Try_Collector_main___closed__6,
    );
    leanh::lean_inc(v_mvarId_5482_);
    v___f_5491_ = leanh::lean_alloc_closure(
        l_Lean_Meta_Try_Collector_main___lam__0___boxed as *mut core::ffi::c_void,
        9,
        4,
    );
    leanh::lean_closure_set(v___f_5491_, 0, v___x_5490_);
    leanh::lean_closure_set(v___f_5491_, 1, v___x_5489_);
    leanh::lean_closure_set(v___f_5491_, 2, v_mvarId_5482_);
    leanh::lean_closure_set(v___f_5491_, 3, v_config_5483_);
    v___x_5492_ = l_Lean_MVarId_withContext___at___00Lean_Meta_Try_Collector_main_spec__0___redArg(
        v_mvarId_5482_,
        v___f_5491_,
        v_a_5484_,
        v_a_5485_,
        v_a_5486_,
        v_a_5487_,
    );
    return v___x_5492_;
}
pub unsafe fn l_Lean_Meta_Try_Collector_main___boxed(
    mut v_mvarId_5493_: *mut leanh::LeanObject,
    mut v_config_5494_: *mut leanh::LeanObject,
    mut v_a_5495_: *mut leanh::LeanObject,
    mut v_a_5496_: *mut leanh::LeanObject,
    mut v_a_5497_: *mut leanh::LeanObject,
    mut v_a_5498_: *mut leanh::LeanObject,
    mut v_a_5499_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5500_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5500_ = l_Lean_Meta_Try_Collector_main(
        v_mvarId_5493_,
        v_config_5494_,
        v_a_5495_,
        v_a_5496_,
        v_a_5497_,
        v_a_5498_,
    );
    leanh::lean_dec(v_a_5498_);
    leanh::lean_dec_ref(v_a_5497_);
    leanh::lean_dec(v_a_5496_);
    leanh::lean_dec_ref(v_a_5495_);
    return v_res_5500_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Try_Collect_0__Lean_Meta_Try_collect_unsafe__1(
    mut v_mvarId_5501_: *mut leanh::LeanObject,
    mut v_config_5502_: *mut leanh::LeanObject,
    mut v_a_5503_: *mut leanh::LeanObject,
    mut v_a_5504_: *mut leanh::LeanObject,
    mut v_a_5505_: *mut leanh::LeanObject,
    mut v_a_5506_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5508_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5508_ = l_Lean_Meta_Try_Collector_main(
        v_mvarId_5501_,
        v_config_5502_,
        v_a_5503_,
        v_a_5504_,
        v_a_5505_,
        v_a_5506_,
    );
    return v___x_5508_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Try_Collect_0__Lean_Meta_Try_collect_unsafe__1___boxed(
    mut v_mvarId_5509_: *mut leanh::LeanObject,
    mut v_config_5510_: *mut leanh::LeanObject,
    mut v_a_5511_: *mut leanh::LeanObject,
    mut v_a_5512_: *mut leanh::LeanObject,
    mut v_a_5513_: *mut leanh::LeanObject,
    mut v_a_5514_: *mut leanh::LeanObject,
    mut v_a_5515_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5516_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5516_ = l___private_Lean_Meta_Tactic_Try_Collect_0__Lean_Meta_Try_collect_unsafe__1(
        v_mvarId_5509_,
        v_config_5510_,
        v_a_5511_,
        v_a_5512_,
        v_a_5513_,
        v_a_5514_,
    );
    leanh::lean_dec(v_a_5514_);
    leanh::lean_dec_ref(v_a_5513_);
    leanh::lean_dec(v_a_5512_);
    leanh::lean_dec_ref(v_a_5511_);
    return v_res_5516_;
}
pub unsafe fn l_Lean_Meta_Try_collect(
    mut v_mvarId_5517_: *mut leanh::LeanObject,
    mut v_config_5518_: *mut leanh::LeanObject,
    mut v_a_5519_: *mut leanh::LeanObject,
    mut v_a_5520_: *mut leanh::LeanObject,
    mut v_a_5521_: *mut leanh::LeanObject,
    mut v_a_5522_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5524_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5524_ = l_Lean_Meta_Try_Collector_main(
        v_mvarId_5517_,
        v_config_5518_,
        v_a_5519_,
        v_a_5520_,
        v_a_5521_,
        v_a_5522_,
    );
    return v___x_5524_;
}
pub unsafe fn l_Lean_Meta_Try_collect___boxed(
    mut v_mvarId_5525_: *mut leanh::LeanObject,
    mut v_config_5526_: *mut leanh::LeanObject,
    mut v_a_5527_: *mut leanh::LeanObject,
    mut v_a_5528_: *mut leanh::LeanObject,
    mut v_a_5529_: *mut leanh::LeanObject,
    mut v_a_5530_: *mut leanh::LeanObject,
    mut v_a_5531_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5532_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5532_ = l_Lean_Meta_Try_collect(
        v_mvarId_5525_,
        v_config_5526_,
        v_a_5527_,
        v_a_5528_,
        v_a_5529_,
        v_a_5530_,
    );
    leanh::lean_dec(v_a_5530_);
    leanh::lean_dec_ref(v_a_5529_);
    leanh::lean_dec(v_a_5528_);
    leanh::lean_dec_ref(v_a_5527_);
    return v_res_5532_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Meta_Tactic_Try_Collect(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Try(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_LibrarySearch(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_FunIndCollect(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Meta_Tactic_Try_Collect(
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
pub unsafe fn initialize_Lean_Meta_Tactic_Try_Collect(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_Try(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Lean_Meta_Tactic_LibrarySearch(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Lean_Meta_Tactic_FunIndCollect(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Try_Collect(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Meta_Tactic_Try_Collect(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return initialize_Lean_Meta_Tactic_Try_Collect(builtin);
}