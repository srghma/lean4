// Lean compiler output
// Module: Lean.Meta.Tactic.Try.Collect
// Imports: Init.Try Lean.Meta.Tactic.LibrarySearch Lean.Meta.Tactic.FunIndCollect
use crate::r#gen::Init::Prelude::{
    l_Lean_Name_append, l_Lean_Name_hasMacroScopes, l_Lean_Name_mkStr1, l_Lean_replaceRef,
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
use crate::lean_imports_rs::Init::Data::Array::Basic::{
    lean_array_size, lean_array_uget, lean_array_uget_borrowed, lean_array_uset, lean_mk_array,
};
use crate::lean_imports_rs::Init::Data::Array::Set::{lean_array_fset, lean_array_set};
use crate::lean_imports_rs::Init::Data::UInt::Basic::{
    lean_uint64_shift_right, lean_uint64_to_usize, lean_uint64_xor, lean_usize_land,
    lean_usize_to_uint64,
};
use crate::lean_imports_rs::Init::Data::UInt::BasicAux::{
    lean_usize_add, lean_usize_dec_lt, lean_usize_of_nat, lean_usize_sub,
};
use crate::lean_imports_rs::Init::Prelude::{
    lean_array_fget, lean_array_get, lean_array_get_size, lean_array_push,
    lean_mk_empty_array_with_capacity, lean_name_eq, lean_nat_add, lean_nat_dec_eq,
    lean_nat_dec_le, lean_nat_dec_lt, lean_nat_div, lean_nat_mul, lean_nat_sub,
    lean_uint64_mix_hash, lean_uint64_of_nat, lean_usize_dec_eq,
};
use crate::lean_imports_rs::Init::System::ST::{
    lean_st_mk_ref, lean_st_ref_get, lean_st_ref_set, lean_st_ref_take,
};
use crate::lean_imports_rs::Init::Util::lean_ptr_addr;
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_alloc_closure, lean_alloc_ctor, lean_box,
    lean_closure_set, lean_ctor_get, lean_ctor_get_uint8, lean_ctor_get_uint64, lean_ctor_set,
    lean_ctor_set_tag, lean_ctor_set_uint8, lean_ctor_set_usize, lean_dec, lean_dec_ref,
    lean_dec_ref_known, lean_del_object, lean_inc, lean_inc_n, lean_inc_ref,
    lean_io_result_is_error, lean_io_result_mk_ok, lean_is_exclusive, lean_obj_once, lean_obj_tag,
    lean_uint64_once, lean_unbox, lean_unbox_usize, lean_unsigned_to_nat,
};
pub static l_Lean_Meta_Try_Collector_instInhabitedOrdSet_default___closed__0_value:
    LeanArrayObject<0> = LeanArrayObject {
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
static mut l_Lean_Meta_Try_Collector_instInhabitedOrdSet_default___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Try_Collector_instInhabitedOrdSet_default___closed__0_value)
        as *mut LeanObject;
static mut l_Lean_Meta_Try_Collector_instInhabitedOrdSet_default___closed__1_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Try_Collector_instInhabitedOrdSet_default___closed__1: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Meta_Try_Collector_instInhabitedOrdSet_default___closed__2_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Try_Collector_instInhabitedOrdSet_default___closed__2: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Meta_Try_Collector_instInhabitedOrdSet_default___closed__3_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Try_Collector_instInhabitedOrdSet_default___closed__3: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Try_Collector_OrdSet_insert___at___00Lean_Meta_Try_Collector_saveConst_spec__0_spec__0___redArg___closed__0_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Try_Collector_OrdSet_insert___at___00Lean_Meta_Try_Collector_saveConst_spec__0_spec__0___redArg___closed__0: u64 = 0;
pub static l_Lean_Meta_Try_Collector_getEqDefDecl_x3f___redArg___closed__0_value: LeanStringObject<
    7,
> = LeanStringObject {
    m_header: LeanObject {
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
static mut l_Lean_Meta_Try_Collector_getEqDefDecl_x3f___redArg___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Try_Collector_getEqDefDecl_x3f___redArg___closed__0_value)
        as *mut LeanObject;
pub static l_Lean_Meta_Try_Collector_getEqDefDecl_x3f___redArg___closed__1_value: LeanCtorObject<
    3,
> = LeanCtorObject {
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
        core::ptr::addr_of!(l_Lean_Meta_Try_Collector_getEqDefDecl_x3f___redArg___closed__0_value)
            as *mut LeanObject,
        17192571042771754225 as *mut LeanObject,
    ],
};
static mut l_Lean_Meta_Try_Collector_getEqDefDecl_x3f___redArg___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Try_Collector_getEqDefDecl_x3f___redArg___closed__1_value)
        as *mut LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Try_Collector_checkInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__0_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Try_Collector_checkInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__0: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Try_Collector_checkInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__1_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Try_Collector_checkInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__1: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Try_Collector_checkInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__2_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Try_Collector_checkInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__2: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Try_Collector_checkInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__3_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Try_Collector_checkInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__3: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Try_Collector_checkInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__4_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Try_Collector_checkInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__4: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Try_Collector_checkInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__5_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Try_Collector_checkInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__5: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Try_Collector_checkInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__6_value: LeanStringObject<24> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 24, m_capacity: 24, m_length: 23, m_data: [65, 32, 112, 114, 105, 118, 97, 116, 101, 32, 100, 101, 99, 108, 97, 114, 97, 116, 105, 111, 110, 32, 96, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Try_Collector_checkInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__6: *mut LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Try_Collector_checkInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__6_value) as *mut LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Try_Collector_checkInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__7_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Try_Collector_checkInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__7: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Try_Collector_checkInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__8_value: LeanStringObject<79> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 79, m_capacity: 79, m_length: 78, m_data: [96, 32, 40, 102, 114, 111, 109, 32, 116, 104, 101, 32, 99, 117, 114, 114, 101, 110, 116, 32, 109, 111, 100, 117, 108, 101, 41, 32, 101, 120, 105, 115, 116, 115, 32, 98, 117, 116, 32, 119, 111, 117, 108, 100, 32, 110, 101, 101, 100, 32, 116, 111, 32, 98, 101, 32, 112, 117, 98, 108, 105, 99, 32, 116, 111, 32, 97, 99, 99, 101, 115, 115, 32, 104, 101, 114, 101, 46, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Try_Collector_checkInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__8: *mut LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Try_Collector_checkInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__8_value) as *mut LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Try_Collector_checkInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__9_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Try_Collector_checkInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__9: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Try_Collector_checkInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__10_value: LeanStringObject<23> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 23, m_capacity: 23, m_length: 22, m_data: [65, 32, 112, 117, 98, 108, 105, 99, 32, 100, 101, 99, 108, 97, 114, 97, 116, 105, 111, 110, 32, 96, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Try_Collector_checkInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__10: *mut LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Try_Collector_checkInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__10_value) as *mut LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Try_Collector_checkInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__11_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Try_Collector_checkInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__11: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Try_Collector_checkInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__12_value: LeanStringObject<68> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 68, m_capacity: 68, m_length: 67, m_data: [96, 32, 101, 120, 105, 115, 116, 115, 32, 98, 117, 116, 32, 105, 115, 32, 105, 109, 112, 111, 114, 116, 101, 100, 32, 112, 114, 105, 118, 97, 116, 101, 108, 121, 59, 32, 99, 111, 110, 115, 105, 100, 101, 114, 32, 97, 100, 100, 105, 110, 103, 32, 96, 112, 117, 98, 108, 105, 99, 32, 105, 109, 112, 111, 114, 116, 32, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Try_Collector_checkInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__12: *mut LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Try_Collector_checkInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__12_value) as *mut LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Try_Collector_checkInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__13_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Try_Collector_checkInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__13: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Try_Collector_checkInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__14_value: LeanStringObject<3> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [96, 46, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Try_Collector_checkInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__14: *mut LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Try_Collector_checkInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__14_value) as *mut LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Try_Collector_checkInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__15_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Try_Collector_checkInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__15: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Try_Collector_checkInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__16_value: LeanStringObject<10> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [96, 32, 40, 102, 114, 111, 109, 32, 96, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Try_Collector_checkInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__16: *mut LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Try_Collector_checkInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__16_value) as *mut LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Try_Collector_checkInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__17_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Try_Collector_checkInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__17: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Try_Collector_checkInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__18_value: LeanStringObject<54> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 54, m_capacity: 54, m_length: 53, m_data: [96, 41, 32, 101, 120, 105, 115, 116, 115, 32, 98, 117, 116, 32, 119, 111, 117, 108, 100, 32, 110, 101, 101, 100, 32, 116, 111, 32, 98, 101, 32, 112, 117, 98, 108, 105, 99, 32, 116, 111, 32, 97, 99, 99, 101, 115, 115, 32, 104, 101, 114, 101, 46, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Try_Collector_checkInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__18: *mut LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Try_Collector_checkInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__18_value) as *mut LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Try_Collector_checkInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__19_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Try_Collector_checkInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__19: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Try_Collector_checkInductive_spec__0_spec__0_spec__1___redArg___closed__0_value: LeanStringObject<19> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 19, m_capacity: 19, m_length: 18, m_data: [85, 110, 107, 110, 111, 119, 110, 32, 99, 111, 110, 115, 116, 97, 110, 116, 32, 96, 0]};
static mut l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Try_Collector_checkInductive_spec__0_spec__0_spec__1___redArg___closed__0: *mut LeanObject = core::ptr::addr_of!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Try_Collector_checkInductive_spec__0_spec__0_spec__1___redArg___closed__0_value) as *mut LeanObject;
static mut l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Try_Collector_checkInductive_spec__0_spec__0_spec__1___redArg___closed__1_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Try_Collector_checkInductive_spec__0_spec__0_spec__1___redArg___closed__1: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Try_Collector_checkInductive_spec__0_spec__0_spec__1___redArg___closed__2_value: LeanStringObject<2> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [96, 0]};
static mut l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Try_Collector_checkInductive_spec__0_spec__0_spec__1___redArg___closed__2: *mut LeanObject = core::ptr::addr_of!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Try_Collector_checkInductive_spec__0_spec__0_spec__1___redArg___closed__2_value) as *mut LeanObject;
static mut l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Try_Collector_checkInductive_spec__0_spec__0_spec__1___redArg___closed__3_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Try_Collector_checkInductive_spec__0_spec__0_spec__1___redArg___closed__3: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Meta_Try_Collector_visit___closed__0_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Try_Collector_visit___closed__0: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Meta_Try_Collector_main___closed__0_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Try_Collector_main___closed__0: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Meta_Try_Collector_main___closed__1_value: LeanArrayObject<0> = LeanArrayObject {
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
static mut l_Lean_Meta_Try_Collector_main___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Try_Collector_main___closed__1_value) as *mut LeanObject;
static mut l_Lean_Meta_Try_Collector_main___closed__2_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Try_Collector_main___closed__2: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Meta_Try_Collector_main___closed__3_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Try_Collector_main___closed__3: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Meta_Try_Collector_main___closed__4_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Try_Collector_main___closed__4: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Meta_Try_Collector_main___closed__5_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Try_Collector_main___closed__5: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Meta_Try_Collector_main___closed__6_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Try_Collector_main___closed__6: *mut LeanObject = core::ptr::null_mut();
pub unsafe fn _init_l_Lean_Meta_Try_Collector_instInhabitedOrdSet_default___closed__1()
-> *mut LeanObject {
    let mut v___x_2769_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2770_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2771_: *mut LeanObject = core::ptr::null_mut();
    v___x_2769_ = lean_box(0);
    v___x_2770_ = lean_unsigned_to_nat(16);
    v___x_2771_ = lean_mk_array(v___x_2770_, v___x_2769_);
    return v___x_2771_;
}
pub unsafe fn _init_l_Lean_Meta_Try_Collector_instInhabitedOrdSet_default___closed__2()
-> *mut LeanObject {
    let mut v___x_2772_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2773_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2774_: *mut LeanObject = core::ptr::null_mut();
    v___x_2772_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Try_Collector_instInhabitedOrdSet_default___closed__1),
        core::ptr::addr_of_mut!(
            l_Lean_Meta_Try_Collector_instInhabitedOrdSet_default___closed__1_once
        ),
        _init_l_Lean_Meta_Try_Collector_instInhabitedOrdSet_default___closed__1,
    );
    v___x_2773_ = lean_unsigned_to_nat(0);
    v___x_2774_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_2774_, 0, v___x_2773_);
    lean_ctor_set(v___x_2774_, 1, v___x_2772_);
    return v___x_2774_;
}
pub unsafe fn _init_l_Lean_Meta_Try_Collector_instInhabitedOrdSet_default___closed__3()
-> *mut LeanObject {
    let mut v___x_2775_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2776_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2777_: *mut LeanObject = core::ptr::null_mut();
    v___x_2775_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Try_Collector_instInhabitedOrdSet_default___closed__2),
        core::ptr::addr_of_mut!(
            l_Lean_Meta_Try_Collector_instInhabitedOrdSet_default___closed__2_once
        ),
        _init_l_Lean_Meta_Try_Collector_instInhabitedOrdSet_default___closed__2,
    );
    v___x_2776_ = l_Lean_Meta_Try_Collector_instInhabitedOrdSet_default___closed__0;
    v___x_2777_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_2777_, 0, v___x_2776_);
    lean_ctor_set(v___x_2777_, 1, v___x_2775_);
    return v___x_2777_;
}
pub unsafe fn l_Lean_Meta_Try_Collector_instInhabitedOrdSet_default(
    mut v_00_u03b1_2778_: *mut LeanObject,
    mut v_inst_2779_: *mut LeanObject,
    mut v_inst_2780_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2781_: *mut LeanObject = core::ptr::null_mut();
    v___x_2781_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Try_Collector_instInhabitedOrdSet_default___closed__3),
        core::ptr::addr_of_mut!(
            l_Lean_Meta_Try_Collector_instInhabitedOrdSet_default___closed__3_once
        ),
        _init_l_Lean_Meta_Try_Collector_instInhabitedOrdSet_default___closed__3,
    );
    return v___x_2781_;
}
pub unsafe fn l_Lean_Meta_Try_Collector_instInhabitedOrdSet_default___boxed(
    mut v_00_u03b1_2782_: *mut LeanObject,
    mut v_inst_2783_: *mut LeanObject,
    mut v_inst_2784_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2785_: *mut LeanObject = core::ptr::null_mut();
    v_res_2785_ = l_Lean_Meta_Try_Collector_instInhabitedOrdSet_default(
        v_00_u03b1_2782_,
        v_inst_2783_,
        v_inst_2784_,
    );
    lean_dec_ref(v_inst_2784_);
    lean_dec_ref(v_inst_2783_);
    return v_res_2785_;
}
pub unsafe fn l_Lean_Meta_Try_Collector_instInhabitedOrdSet___redArg(
    mut v_a_2786_: *mut LeanObject,
    mut v_a_2787_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2788_: *mut LeanObject = core::ptr::null_mut();
    v___x_2788_ =
        l_Lean_Meta_Try_Collector_instInhabitedOrdSet_default(lean_box(0), v_a_2786_, v_a_2787_);
    return v___x_2788_;
}
pub unsafe fn l_Lean_Meta_Try_Collector_instInhabitedOrdSet___redArg___boxed(
    mut v_a_2789_: *mut LeanObject,
    mut v_a_2790_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2791_: *mut LeanObject = core::ptr::null_mut();
    v_res_2791_ = l_Lean_Meta_Try_Collector_instInhabitedOrdSet___redArg(v_a_2789_, v_a_2790_);
    lean_dec_ref(v_a_2790_);
    lean_dec_ref(v_a_2789_);
    return v_res_2791_;
}
pub unsafe fn l_Lean_Meta_Try_Collector_instInhabitedOrdSet(
    mut v_a_2792_: *mut LeanObject,
    mut v_a_2793_: *mut LeanObject,
    mut v_a_2794_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2795_: *mut LeanObject = core::ptr::null_mut();
    v___x_2795_ =
        l_Lean_Meta_Try_Collector_instInhabitedOrdSet_default(lean_box(0), v_a_2793_, v_a_2794_);
    return v___x_2795_;
}
pub unsafe fn l_Lean_Meta_Try_Collector_instInhabitedOrdSet___boxed(
    mut v_a_2796_: *mut LeanObject,
    mut v_a_2797_: *mut LeanObject,
    mut v_a_2798_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2799_: *mut LeanObject = core::ptr::null_mut();
    v_res_2799_ = l_Lean_Meta_Try_Collector_instInhabitedOrdSet(v_a_2796_, v_a_2797_, v_a_2798_);
    lean_dec_ref(v_a_2798_);
    lean_dec_ref(v_a_2797_);
    return v_res_2799_;
}
pub unsafe fn l_Lean_Meta_Try_Collector_OrdSet_insert___redArg(
    mut v_x_2800_: *mut LeanObject,
    mut v_x_2801_: *mut LeanObject,
    mut v_s_2802_: *mut LeanObject,
    mut v_a_2803_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_elems_2804_: *mut LeanObject = core::ptr::null_mut();
    let mut v_set_2805_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2806_: u8 = 0;
    let mut v___x_2808_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2809_: u8 = 0;
    let mut v___x_2810_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2811_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2812_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2814_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2815_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2816_: u8 = 0;
    let mut v_unused_2817_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_2818_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_elems_2804_ = lean_ctor_get(v_s_2802_, 0);
                v_set_2805_ = lean_ctor_get(v_s_2802_, 1);
                lean_inc(v_a_2803_);
                lean_inc_ref(v_x_2800_);
                lean_inc_ref(v_x_2801_);
                v___x_2806_ = l_Std_DHashMap_Internal_Raw_u2080_contains___redArg(
                    v_x_2801_,
                    v_x_2800_,
                    v_set_2805_,
                    v_a_2803_,
                );
                if v___x_2806_ == 0 {
                    lean_inc_ref(v_set_2805_);
                    lean_inc_ref(v_elems_2804_);
                    v_isSharedCheck_2816_ = (!lean_is_exclusive(v_s_2802_)) as u8;
                    if v_isSharedCheck_2816_ == 0 {
                        v_unused_2817_ = lean_ctor_get(v_s_2802_, 1);
                        lean_dec(v_unused_2817_);
                        v_unused_2818_ = lean_ctor_get(v_s_2802_, 0);
                        lean_dec(v_unused_2818_);
                        v___x_2808_ = v_s_2802_;
                        v_isShared_2809_ = v_isSharedCheck_2816_;
                        state = 1;
                        continue;
                    } else {
                        lean_dec(v_s_2802_);
                        v___x_2808_ = lean_box(0);
                        v_isShared_2809_ = v_isSharedCheck_2816_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec(v_a_2803_);
                    lean_dec_ref(v_x_2801_);
                    lean_dec_ref(v_x_2800_);
                    return v_s_2802_;
                }
            }
            1 => {
                lean_inc(v_a_2803_);
                v___x_2810_ = lean_array_push(v_elems_2804_, v_a_2803_);
                v___x_2811_ = lean_box(0);
                v___x_2812_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___redArg(
                    v_x_2801_,
                    v_x_2800_,
                    v_set_2805_,
                    v_a_2803_,
                    v___x_2811_,
                );
                if v_isShared_2809_ == 0 {
                    lean_ctor_set(v___x_2808_, 1, v___x_2812_);
                    lean_ctor_set(v___x_2808_, 0, v___x_2810_);
                    v___x_2814_ = v___x_2808_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2815_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2815_, 0, v___x_2810_);
                    lean_ctor_set(v_reuseFailAlloc_2815_, 1, v___x_2812_);
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
    mut v_00_u03b1_2819_: *mut LeanObject,
    mut v_x_2820_: *mut LeanObject,
    mut v_x_2821_: *mut LeanObject,
    mut v_s_2822_: *mut LeanObject,
    mut v_a_2823_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2824_: *mut LeanObject = core::ptr::null_mut();
    v___x_2824_ = l_Lean_Meta_Try_Collector_OrdSet_insert___redArg(
        v_x_2820_, v_x_2821_, v_s_2822_, v_a_2823_,
    );
    return v___x_2824_;
}
pub unsafe fn l_Lean_Meta_Try_Collector_OrdSet_isEmpty___redArg(
    mut v_s_2825_: *mut LeanObject,
) -> u8 {
    let mut v_elems_2826_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2827_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2828_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2829_: u8 = 0;
    v_elems_2826_ = lean_ctor_get(v_s_2825_, 0);
    v___x_2827_ = lean_array_get_size(v_elems_2826_);
    v___x_2828_ = lean_unsigned_to_nat(0);
    v___x_2829_ = lean_nat_dec_eq(v___x_2827_, v___x_2828_);
    return v___x_2829_;
}
pub unsafe fn l_Lean_Meta_Try_Collector_OrdSet_isEmpty___redArg___boxed(
    mut v_s_2830_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2831_: u8 = 0;
    let mut v_r_2832_: *mut LeanObject = core::ptr::null_mut();
    v_res_2831_ = l_Lean_Meta_Try_Collector_OrdSet_isEmpty___redArg(v_s_2830_);
    lean_dec_ref(v_s_2830_);
    v_r_2832_ = lean_box((v_res_2831_) as usize);
    return v_r_2832_;
}
pub unsafe fn l_Lean_Meta_Try_Collector_OrdSet_isEmpty(
    mut v_00_u03b1_2833_: *mut LeanObject,
    mut v_x_2834_: *mut LeanObject,
    mut v_x_2835_: *mut LeanObject,
    mut v_s_2836_: *mut LeanObject,
) -> u8 {
    let mut v___x_2837_: u8 = 0;
    v___x_2837_ = l_Lean_Meta_Try_Collector_OrdSet_isEmpty___redArg(v_s_2836_);
    return v___x_2837_;
}
pub unsafe fn l_Lean_Meta_Try_Collector_OrdSet_isEmpty___boxed(
    mut v_00_u03b1_2838_: *mut LeanObject,
    mut v_x_2839_: *mut LeanObject,
    mut v_x_2840_: *mut LeanObject,
    mut v_s_2841_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2842_: u8 = 0;
    let mut v_r_2843_: *mut LeanObject = core::ptr::null_mut();
    v_res_2842_ =
        l_Lean_Meta_Try_Collector_OrdSet_isEmpty(v_00_u03b1_2838_, v_x_2839_, v_x_2840_, v_s_2841_);
    lean_dec_ref(v_s_2841_);
    lean_dec_ref(v_x_2840_);
    lean_dec_ref(v_x_2839_);
    v_r_2843_ = lean_box((v_res_2842_) as usize);
    return v_r_2843_;
}
pub unsafe fn l_Lean_Meta_Try_Collector_getConfig___redArg(
    mut v_a_2844_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2846_: *mut LeanObject = core::ptr::null_mut();
    lean_inc_ref(v_a_2844_);
    v___x_2846_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_2846_, 0, v_a_2844_);
    return v___x_2846_;
}
pub unsafe fn l_Lean_Meta_Try_Collector_getConfig___redArg___boxed(
    mut v_a_2847_: *mut LeanObject,
    mut v_a_2848_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2849_: *mut LeanObject = core::ptr::null_mut();
    v_res_2849_ = l_Lean_Meta_Try_Collector_getConfig___redArg(v_a_2847_);
    lean_dec_ref(v_a_2847_);
    return v_res_2849_;
}
pub unsafe fn l_Lean_Meta_Try_Collector_getConfig(
    mut v_a_2850_: *mut LeanObject,
    mut v_a_2851_: *mut LeanObject,
    mut v_a_2852_: *mut LeanObject,
    mut v_a_2853_: *mut LeanObject,
    mut v_a_2854_: *mut LeanObject,
    mut v_a_2855_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2857_: *mut LeanObject = core::ptr::null_mut();
    lean_inc_ref(v_a_2850_);
    v___x_2857_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_2857_, 0, v_a_2850_);
    return v___x_2857_;
}
pub unsafe fn l_Lean_Meta_Try_Collector_getConfig___boxed(
    mut v_a_2858_: *mut LeanObject,
    mut v_a_2859_: *mut LeanObject,
    mut v_a_2860_: *mut LeanObject,
    mut v_a_2861_: *mut LeanObject,
    mut v_a_2862_: *mut LeanObject,
    mut v_a_2863_: *mut LeanObject,
    mut v_a_2864_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2865_: *mut LeanObject = core::ptr::null_mut();
    v_res_2865_ = l_Lean_Meta_Try_Collector_getConfig(
        v_a_2858_, v_a_2859_, v_a_2860_, v_a_2861_, v_a_2862_, v_a_2863_,
    );
    lean_dec(v_a_2863_);
    lean_dec_ref(v_a_2862_);
    lean_dec(v_a_2861_);
    lean_dec_ref(v_a_2860_);
    lean_dec(v_a_2859_);
    lean_dec_ref(v_a_2858_);
    return v_res_2865_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Try_Collector_OrdSet_insert___at___00Lean_Meta_Try_Collector_saveConst_spec__0_spec__0_spec__1___redArg(
    mut v_a_2866_: *mut LeanObject,
    mut v_x_2867_: *mut LeanObject,
) -> u8 {
    let mut v___x_2868_: u8 = 0;
    let mut v_key_2869_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_2870_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2871_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_2867_) == 0 {
                    v___x_2868_ = 0;
                    return v___x_2868_;
                } else {
                    v_key_2869_ = lean_ctor_get(v_x_2867_, 0);
                    v_tail_2870_ = lean_ctor_get(v_x_2867_, 2);
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
    mut v_a_2873_: *mut LeanObject,
    mut v_x_2874_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2875_: u8 = 0;
    let mut v_r_2876_: *mut LeanObject = core::ptr::null_mut();
    v_res_2875_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Try_Collector_OrdSet_insert___at___00Lean_Meta_Try_Collector_saveConst_spec__0_spec__0_spec__1___redArg(v_a_2873_, v_x_2874_);
    lean_dec(v_x_2874_);
    lean_dec(v_a_2873_);
    v_r_2876_ = lean_box((v_res_2875_) as usize);
    return v_r_2876_;
}
pub unsafe fn _init_l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Try_Collector_OrdSet_insert___at___00Lean_Meta_Try_Collector_saveConst_spec__0_spec__0___redArg___closed__0()
-> u64 {
    let mut v___x_2877_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2878_: u64 = 0;
    v___x_2877_ = lean_unsigned_to_nat(1723);
    v___x_2878_ = lean_uint64_of_nat(v___x_2877_);
    return v___x_2878_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Try_Collector_OrdSet_insert___at___00Lean_Meta_Try_Collector_saveConst_spec__0_spec__0___redArg(
    mut v_m_2879_: *mut LeanObject,
    mut v_a_2880_: *mut LeanObject,
) -> u8 {
    let mut v_buckets_2881_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2882_: *mut LeanObject = core::ptr::null_mut();
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
    let mut v___x_2896_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2897_: u8 = 0;
    let mut v___x_2898_: u64 = 0;
    let mut v_hash_2899_: u64 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_buckets_2881_ = lean_ctor_get(v_m_2879_, 1);
                v___x_2882_ = lean_array_get_size(v_buckets_2881_);
                if lean_obj_tag(v_a_2880_) == 0 {
                    v___x_2898_ = lean_uint64_once(core::ptr::addr_of_mut!(l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Try_Collector_OrdSet_insert___at___00Lean_Meta_Try_Collector_saveConst_spec__0_spec__0___redArg___closed__0), core::ptr::addr_of_mut!(l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Try_Collector_OrdSet_insert___at___00Lean_Meta_Try_Collector_saveConst_spec__0_spec__0___redArg___closed__0_once), _init_l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Try_Collector_OrdSet_insert___at___00Lean_Meta_Try_Collector_saveConst_spec__0_spec__0___redArg___closed__0);
                    v___y_2884_ = v___x_2898_;
                    state = 1;
                    continue;
                } else {
                    v_hash_2899_ = lean_ctor_get_uint64(
                        v_a_2880_,
                        (core::mem::size_of::<*mut LeanObject>() * 2) as u32,
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
    mut v_m_2900_: *mut LeanObject,
    mut v_a_2901_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2902_: u8 = 0;
    let mut v_r_2903_: *mut LeanObject = core::ptr::null_mut();
    v_res_2902_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Try_Collector_OrdSet_insert___at___00Lean_Meta_Try_Collector_saveConst_spec__0_spec__0___redArg(v_m_2900_, v_a_2901_);
    lean_dec(v_a_2901_);
    lean_dec_ref(v_m_2900_);
    v_r_2903_ = lean_box((v_res_2902_) as usize);
    return v_r_2903_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Try_Collector_OrdSet_insert___at___00Lean_Meta_Try_Collector_saveConst_spec__0_spec__1_spec__3_spec__4_spec__5___redArg(
    mut v_x_2904_: *mut LeanObject,
    mut v_x_2905_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_key_2906_: *mut LeanObject = core::ptr::null_mut();
    let mut v_value_2907_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_2908_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2910_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2911_: u8 = 0;
    let mut v___x_2912_: *mut LeanObject = core::ptr::null_mut();
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
    let mut v___x_2926_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2928_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2929_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2931_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2932_: u64 = 0;
    let mut v_hash_2933_: u64 = 0;
    let mut v_isSharedCheck_2934_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_2905_) == 0 {
                    return v_x_2904_;
                } else {
                    v_key_2906_ = lean_ctor_get(v_x_2905_, 0);
                    v_value_2907_ = lean_ctor_get(v_x_2905_, 1);
                    v_tail_2908_ = lean_ctor_get(v_x_2905_, 2);
                    v_isSharedCheck_2934_ = (!lean_is_exclusive(v_x_2905_)) as u8;
                    if v_isSharedCheck_2934_ == 0 {
                        v___x_2910_ = v_x_2905_;
                        v_isShared_2911_ = v_isSharedCheck_2934_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_tail_2908_);
                        lean_inc(v_value_2907_);
                        lean_inc(v_key_2906_);
                        lean_dec(v_x_2905_);
                        v___x_2910_ = lean_box(0);
                        v_isShared_2911_ = v_isSharedCheck_2934_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_2912_ = lean_array_get_size(v_x_2904_);
                if lean_obj_tag(v_key_2906_) == 0 {
                    v___x_2932_ = lean_uint64_once(core::ptr::addr_of_mut!(l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Try_Collector_OrdSet_insert___at___00Lean_Meta_Try_Collector_saveConst_spec__0_spec__0___redArg___closed__0), core::ptr::addr_of_mut!(l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Try_Collector_OrdSet_insert___at___00Lean_Meta_Try_Collector_saveConst_spec__0_spec__0___redArg___closed__0_once), _init_l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Try_Collector_OrdSet_insert___at___00Lean_Meta_Try_Collector_saveConst_spec__0_spec__0___redArg___closed__0);
                    v___y_2914_ = v___x_2932_;
                    state = 2;
                    continue;
                } else {
                    v_hash_2933_ = lean_ctor_get_uint64(
                        v_key_2906_,
                        (core::mem::size_of::<*mut LeanObject>() * 2) as u32,
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
                lean_inc(v___x_2926_);
                if v_isShared_2911_ == 0 {
                    lean_ctor_set(v___x_2910_, 2, v___x_2926_);
                    v___x_2928_ = v___x_2910_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2931_ = lean_alloc_ctor(1, 3, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2931_, 0, v_key_2906_);
                    lean_ctor_set(v_reuseFailAlloc_2931_, 1, v_value_2907_);
                    lean_ctor_set(v_reuseFailAlloc_2931_, 2, v___x_2926_);
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
    mut v_i_2935_: *mut LeanObject,
    mut v_source_2936_: *mut LeanObject,
    mut v_target_2937_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2938_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2939_: u8 = 0;
    let mut v_es_2940_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2941_: *mut LeanObject = core::ptr::null_mut();
    let mut v_source_2942_: *mut LeanObject = core::ptr::null_mut();
    let mut v_target_2943_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2944_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2945_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2938_ = lean_array_get_size(v_source_2936_);
                v___x_2939_ = lean_nat_dec_lt(v_i_2935_, v___x_2938_);
                if v___x_2939_ == 0 {
                    lean_dec_ref(v_source_2936_);
                    lean_dec(v_i_2935_);
                    return v_target_2937_;
                } else {
                    v_es_2940_ = lean_array_fget(v_source_2936_, v_i_2935_);
                    v___x_2941_ = lean_box(0);
                    v_source_2942_ = lean_array_fset(v_source_2936_, v_i_2935_, v___x_2941_);
                    v_target_2943_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Try_Collector_OrdSet_insert___at___00Lean_Meta_Try_Collector_saveConst_spec__0_spec__1_spec__3_spec__4_spec__5___redArg(v_target_2937_, v_es_2940_);
                    v___x_2944_ = lean_unsigned_to_nat(1);
                    v___x_2945_ = lean_nat_add(v_i_2935_, v___x_2944_);
                    lean_dec(v_i_2935_);
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
    mut v_data_2947_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2948_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2949_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nbuckets_2950_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2951_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2952_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2953_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2954_: *mut LeanObject = core::ptr::null_mut();
    v___x_2948_ = lean_array_get_size(v_data_2947_);
    v___x_2949_ = lean_unsigned_to_nat(2);
    v_nbuckets_2950_ = lean_nat_mul(v___x_2948_, v___x_2949_);
    v___x_2951_ = lean_unsigned_to_nat(0);
    v___x_2952_ = lean_box(0);
    v___x_2953_ = lean_mk_array(v_nbuckets_2950_, v___x_2952_);
    v___x_2954_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Try_Collector_OrdSet_insert___at___00Lean_Meta_Try_Collector_saveConst_spec__0_spec__1_spec__3_spec__4___redArg(v___x_2951_, v_data_2947_, v___x_2953_);
    return v___x_2954_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Try_Collector_OrdSet_insert___at___00Lean_Meta_Try_Collector_saveConst_spec__0_spec__1___redArg(
    mut v_m_2955_: *mut LeanObject,
    mut v_a_2956_: *mut LeanObject,
    mut v_b_2957_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_size_2958_: *mut LeanObject = core::ptr::null_mut();
    let mut v_buckets_2959_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2960_: *mut LeanObject = core::ptr::null_mut();
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
    let mut v_bkt_2974_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2975_: u8 = 0;
    let mut v___x_2977_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2978_: u8 = 0;
    let mut v___x_2979_: *mut LeanObject = core::ptr::null_mut();
    let mut v_size_x27_2980_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2981_: *mut LeanObject = core::ptr::null_mut();
    let mut v_buckets_x27_2982_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2983_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2984_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2985_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2986_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2987_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2988_: u8 = 0;
    let mut v_val_2989_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2991_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2992_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2994_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2995_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2996_: u8 = 0;
    let mut v_unused_2997_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_2998_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2999_: u64 = 0;
    let mut v_hash_3000_: u64 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_size_2958_ = lean_ctor_get(v_m_2955_, 0);
                v_buckets_2959_ = lean_ctor_get(v_m_2955_, 1);
                v___x_2960_ = lean_array_get_size(v_buckets_2959_);
                if lean_obj_tag(v_a_2956_) == 0 {
                    v___x_2999_ = lean_uint64_once(core::ptr::addr_of_mut!(l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Try_Collector_OrdSet_insert___at___00Lean_Meta_Try_Collector_saveConst_spec__0_spec__0___redArg___closed__0), core::ptr::addr_of_mut!(l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Try_Collector_OrdSet_insert___at___00Lean_Meta_Try_Collector_saveConst_spec__0_spec__0___redArg___closed__0_once), _init_l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Try_Collector_OrdSet_insert___at___00Lean_Meta_Try_Collector_saveConst_spec__0_spec__0___redArg___closed__0);
                    v___y_2962_ = v___x_2999_;
                    state = 1;
                    continue;
                } else {
                    v_hash_3000_ = lean_ctor_get_uint64(
                        v_a_2956_,
                        (core::mem::size_of::<*mut LeanObject>() * 2) as u32,
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
                    lean_inc_ref(v_buckets_2959_);
                    lean_inc(v_size_2958_);
                    v_isSharedCheck_2996_ = (!lean_is_exclusive(v_m_2955_)) as u8;
                    if v_isSharedCheck_2996_ == 0 {
                        v_unused_2997_ = lean_ctor_get(v_m_2955_, 1);
                        lean_dec(v_unused_2997_);
                        v_unused_2998_ = lean_ctor_get(v_m_2955_, 0);
                        lean_dec(v_unused_2998_);
                        v___x_2977_ = v_m_2955_;
                        v_isShared_2978_ = v_isSharedCheck_2996_;
                        state = 2;
                        continue;
                    } else {
                        lean_dec(v_m_2955_);
                        v___x_2977_ = lean_box(0);
                        v_isShared_2978_ = v_isSharedCheck_2996_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_dec(v_b_2957_);
                    lean_dec(v_a_2956_);
                    return v_m_2955_;
                }
            }
            2 => {
                v___x_2979_ = lean_unsigned_to_nat(1);
                v_size_x27_2980_ = lean_nat_add(v_size_2958_, v___x_2979_);
                lean_dec(v_size_2958_);
                lean_inc(v_bkt_2974_);
                v___x_2981_ = lean_alloc_ctor(1, 3, (0) as u32);
                lean_ctor_set(v___x_2981_, 0, v_a_2956_);
                lean_ctor_set(v___x_2981_, 1, v_b_2957_);
                lean_ctor_set(v___x_2981_, 2, v_bkt_2974_);
                v_buckets_x27_2982_ = lean_array_uset(v_buckets_2959_, v___x_2973_, v___x_2981_);
                v___x_2983_ = lean_unsigned_to_nat(4);
                v___x_2984_ = lean_nat_mul(v_size_x27_2980_, v___x_2983_);
                v___x_2985_ = lean_unsigned_to_nat(3);
                v___x_2986_ = lean_nat_div(v___x_2984_, v___x_2985_);
                lean_dec(v___x_2984_);
                v___x_2987_ = lean_array_get_size(v_buckets_x27_2982_);
                v___x_2988_ = lean_nat_dec_le(v___x_2986_, v___x_2987_);
                lean_dec(v___x_2986_);
                if v___x_2988_ == 0 {
                    v_val_2989_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Try_Collector_OrdSet_insert___at___00Lean_Meta_Try_Collector_saveConst_spec__0_spec__1_spec__3___redArg(v_buckets_x27_2982_);
                    if v_isShared_2978_ == 0 {
                        lean_ctor_set(v___x_2977_, 1, v_val_2989_);
                        lean_ctor_set(v___x_2977_, 0, v_size_x27_2980_);
                        v___x_2991_ = v___x_2977_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_2992_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_2992_, 0, v_size_x27_2980_);
                        lean_ctor_set(v_reuseFailAlloc_2992_, 1, v_val_2989_);
                        v___x_2991_ = v_reuseFailAlloc_2992_;
                        state = 3;
                        continue;
                    }
                } else {
                    if v_isShared_2978_ == 0 {
                        lean_ctor_set(v___x_2977_, 1, v_buckets_x27_2982_);
                        lean_ctor_set(v___x_2977_, 0, v_size_x27_2980_);
                        v___x_2994_ = v___x_2977_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_2995_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_2995_, 0, v_size_x27_2980_);
                        lean_ctor_set(v_reuseFailAlloc_2995_, 1, v_buckets_x27_2982_);
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
    mut v_s_3001_: *mut LeanObject,
    mut v_a_3002_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_elems_3003_: *mut LeanObject = core::ptr::null_mut();
    let mut v_set_3004_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3005_: u8 = 0;
    let mut v___x_3007_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3008_: u8 = 0;
    let mut v___x_3009_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3010_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3011_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3013_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3014_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3015_: u8 = 0;
    let mut v_unused_3016_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_3017_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_elems_3003_ = lean_ctor_get(v_s_3001_, 0);
                v_set_3004_ = lean_ctor_get(v_s_3001_, 1);
                v___x_3005_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Try_Collector_OrdSet_insert___at___00Lean_Meta_Try_Collector_saveConst_spec__0_spec__0___redArg(v_set_3004_, v_a_3002_);
                if v___x_3005_ == 0 {
                    lean_inc_ref(v_set_3004_);
                    lean_inc_ref(v_elems_3003_);
                    v_isSharedCheck_3015_ = (!lean_is_exclusive(v_s_3001_)) as u8;
                    if v_isSharedCheck_3015_ == 0 {
                        v_unused_3016_ = lean_ctor_get(v_s_3001_, 1);
                        lean_dec(v_unused_3016_);
                        v_unused_3017_ = lean_ctor_get(v_s_3001_, 0);
                        lean_dec(v_unused_3017_);
                        v___x_3007_ = v_s_3001_;
                        v_isShared_3008_ = v_isSharedCheck_3015_;
                        state = 1;
                        continue;
                    } else {
                        lean_dec(v_s_3001_);
                        v___x_3007_ = lean_box(0);
                        v_isShared_3008_ = v_isSharedCheck_3015_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec(v_a_3002_);
                    return v_s_3001_;
                }
            }
            1 => {
                lean_inc(v_a_3002_);
                v___x_3009_ = lean_array_push(v_elems_3003_, v_a_3002_);
                v___x_3010_ = lean_box(0);
                v___x_3011_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Try_Collector_OrdSet_insert___at___00Lean_Meta_Try_Collector_saveConst_spec__0_spec__1___redArg(v_set_3004_, v_a_3002_, v___x_3010_);
                if v_isShared_3008_ == 0 {
                    lean_ctor_set(v___x_3007_, 1, v___x_3011_);
                    lean_ctor_set(v___x_3007_, 0, v___x_3009_);
                    v___x_3013_ = v___x_3007_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3014_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3014_, 0, v___x_3009_);
                    lean_ctor_set(v_reuseFailAlloc_3014_, 1, v___x_3011_);
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
    mut v_declName_3018_: *mut LeanObject,
    mut v_a_3019_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3021_: *mut LeanObject = core::ptr::null_mut();
    let mut v_allConsts_3022_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unfoldCandidates_3023_: *mut LeanObject = core::ptr::null_mut();
    let mut v_eqnCandidates_3024_: *mut LeanObject = core::ptr::null_mut();
    let mut v_funIndCandidates_3025_: *mut LeanObject = core::ptr::null_mut();
    let mut v_indCandidates_3026_: *mut LeanObject = core::ptr::null_mut();
    let mut v_libSearchResults_3027_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3029_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3030_: u8 = 0;
    let mut v___x_3031_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3033_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3034_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3035_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3036_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3037_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3038_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3021_ = lean_st_ref_take(v_a_3019_);
                v_allConsts_3022_ = lean_ctor_get(v___x_3021_, 0);
                v_unfoldCandidates_3023_ = lean_ctor_get(v___x_3021_, 1);
                v_eqnCandidates_3024_ = lean_ctor_get(v___x_3021_, 2);
                v_funIndCandidates_3025_ = lean_ctor_get(v___x_3021_, 3);
                v_indCandidates_3026_ = lean_ctor_get(v___x_3021_, 4);
                v_libSearchResults_3027_ = lean_ctor_get(v___x_3021_, 5);
                v_isSharedCheck_3038_ = (!lean_is_exclusive(v___x_3021_)) as u8;
                if v_isSharedCheck_3038_ == 0 {
                    v___x_3029_ = v___x_3021_;
                    v_isShared_3030_ = v_isSharedCheck_3038_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_libSearchResults_3027_);
                    lean_inc(v_indCandidates_3026_);
                    lean_inc(v_funIndCandidates_3025_);
                    lean_inc(v_eqnCandidates_3024_);
                    lean_inc(v_unfoldCandidates_3023_);
                    lean_inc(v_allConsts_3022_);
                    lean_dec(v___x_3021_);
                    v___x_3029_ = lean_box(0);
                    v_isShared_3030_ = v_isSharedCheck_3038_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_3031_ = l_Lean_Meta_Try_Collector_OrdSet_insert___at___00Lean_Meta_Try_Collector_saveConst_spec__0(v_allConsts_3022_, v_declName_3018_);
                if v_isShared_3030_ == 0 {
                    lean_ctor_set(v___x_3029_, 0, v___x_3031_);
                    v___x_3033_ = v___x_3029_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3037_ = lean_alloc_ctor(0, 6, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3037_, 0, v___x_3031_);
                    lean_ctor_set(v_reuseFailAlloc_3037_, 1, v_unfoldCandidates_3023_);
                    lean_ctor_set(v_reuseFailAlloc_3037_, 2, v_eqnCandidates_3024_);
                    lean_ctor_set(v_reuseFailAlloc_3037_, 3, v_funIndCandidates_3025_);
                    lean_ctor_set(v_reuseFailAlloc_3037_, 4, v_indCandidates_3026_);
                    lean_ctor_set(v_reuseFailAlloc_3037_, 5, v_libSearchResults_3027_);
                    v___x_3033_ = v_reuseFailAlloc_3037_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_3034_ = lean_st_ref_set(v_a_3019_, v___x_3033_);
                v___x_3035_ = lean_box(0);
                v___x_3036_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_3036_, 0, v___x_3035_);
                return v___x_3036_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Try_Collector_saveConst___redArg___boxed(
    mut v_declName_3039_: *mut LeanObject,
    mut v_a_3040_: *mut LeanObject,
    mut v_a_3041_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3042_: *mut LeanObject = core::ptr::null_mut();
    v_res_3042_ = l_Lean_Meta_Try_Collector_saveConst___redArg(v_declName_3039_, v_a_3040_);
    lean_dec(v_a_3040_);
    return v_res_3042_;
}
pub unsafe fn l_Lean_Meta_Try_Collector_saveConst(
    mut v_declName_3043_: *mut LeanObject,
    mut v_a_3044_: *mut LeanObject,
    mut v_a_3045_: *mut LeanObject,
    mut v_a_3046_: *mut LeanObject,
    mut v_a_3047_: *mut LeanObject,
    mut v_a_3048_: *mut LeanObject,
    mut v_a_3049_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3051_: *mut LeanObject = core::ptr::null_mut();
    v___x_3051_ = l_Lean_Meta_Try_Collector_saveConst___redArg(v_declName_3043_, v_a_3045_);
    return v___x_3051_;
}
pub unsafe fn l_Lean_Meta_Try_Collector_saveConst___boxed(
    mut v_declName_3052_: *mut LeanObject,
    mut v_a_3053_: *mut LeanObject,
    mut v_a_3054_: *mut LeanObject,
    mut v_a_3055_: *mut LeanObject,
    mut v_a_3056_: *mut LeanObject,
    mut v_a_3057_: *mut LeanObject,
    mut v_a_3058_: *mut LeanObject,
    mut v_a_3059_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3060_: *mut LeanObject = core::ptr::null_mut();
    v_res_3060_ = l_Lean_Meta_Try_Collector_saveConst(
        v_declName_3052_,
        v_a_3053_,
        v_a_3054_,
        v_a_3055_,
        v_a_3056_,
        v_a_3057_,
        v_a_3058_,
    );
    lean_dec(v_a_3058_);
    lean_dec_ref(v_a_3057_);
    lean_dec(v_a_3056_);
    lean_dec_ref(v_a_3055_);
    lean_dec(v_a_3054_);
    lean_dec_ref(v_a_3053_);
    return v_res_3060_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Try_Collector_OrdSet_insert___at___00Lean_Meta_Try_Collector_saveConst_spec__0_spec__0(
    mut v_00_u03b2_3061_: *mut LeanObject,
    mut v_m_3062_: *mut LeanObject,
    mut v_a_3063_: *mut LeanObject,
) -> u8 {
    let mut v___x_3064_: u8 = 0;
    v___x_3064_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Try_Collector_OrdSet_insert___at___00Lean_Meta_Try_Collector_saveConst_spec__0_spec__0___redArg(v_m_3062_, v_a_3063_);
    return v___x_3064_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Try_Collector_OrdSet_insert___at___00Lean_Meta_Try_Collector_saveConst_spec__0_spec__0___boxed(
    mut v_00_u03b2_3065_: *mut LeanObject,
    mut v_m_3066_: *mut LeanObject,
    mut v_a_3067_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3068_: u8 = 0;
    let mut v_r_3069_: *mut LeanObject = core::ptr::null_mut();
    v_res_3068_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Try_Collector_OrdSet_insert___at___00Lean_Meta_Try_Collector_saveConst_spec__0_spec__0(v_00_u03b2_3065_, v_m_3066_, v_a_3067_);
    lean_dec(v_a_3067_);
    lean_dec_ref(v_m_3066_);
    v_r_3069_ = lean_box((v_res_3068_) as usize);
    return v_r_3069_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Try_Collector_OrdSet_insert___at___00Lean_Meta_Try_Collector_saveConst_spec__0_spec__1(
    mut v_00_u03b2_3070_: *mut LeanObject,
    mut v_m_3071_: *mut LeanObject,
    mut v_a_3072_: *mut LeanObject,
    mut v_b_3073_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3074_: *mut LeanObject = core::ptr::null_mut();
    v___x_3074_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Try_Collector_OrdSet_insert___at___00Lean_Meta_Try_Collector_saveConst_spec__0_spec__1___redArg(v_m_3071_, v_a_3072_, v_b_3073_);
    return v___x_3074_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Try_Collector_OrdSet_insert___at___00Lean_Meta_Try_Collector_saveConst_spec__0_spec__0_spec__1(
    mut v_00_u03b2_3075_: *mut LeanObject,
    mut v_a_3076_: *mut LeanObject,
    mut v_x_3077_: *mut LeanObject,
) -> u8 {
    let mut v___x_3078_: u8 = 0;
    v___x_3078_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Try_Collector_OrdSet_insert___at___00Lean_Meta_Try_Collector_saveConst_spec__0_spec__0_spec__1___redArg(v_a_3076_, v_x_3077_);
    return v___x_3078_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Try_Collector_OrdSet_insert___at___00Lean_Meta_Try_Collector_saveConst_spec__0_spec__0_spec__1___boxed(
    mut v_00_u03b2_3079_: *mut LeanObject,
    mut v_a_3080_: *mut LeanObject,
    mut v_x_3081_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3082_: u8 = 0;
    let mut v_r_3083_: *mut LeanObject = core::ptr::null_mut();
    v_res_3082_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Try_Collector_OrdSet_insert___at___00Lean_Meta_Try_Collector_saveConst_spec__0_spec__0_spec__1(v_00_u03b2_3079_, v_a_3080_, v_x_3081_);
    lean_dec(v_x_3081_);
    lean_dec(v_a_3080_);
    v_r_3083_ = lean_box((v_res_3082_) as usize);
    return v_r_3083_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Try_Collector_OrdSet_insert___at___00Lean_Meta_Try_Collector_saveConst_spec__0_spec__1_spec__3(
    mut v_00_u03b2_3084_: *mut LeanObject,
    mut v_data_3085_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3086_: *mut LeanObject = core::ptr::null_mut();
    v___x_3086_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Try_Collector_OrdSet_insert___at___00Lean_Meta_Try_Collector_saveConst_spec__0_spec__1_spec__3___redArg(v_data_3085_);
    return v___x_3086_;
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Try_Collector_OrdSet_insert___at___00Lean_Meta_Try_Collector_saveConst_spec__0_spec__1_spec__3_spec__4(
    mut v_00_u03b2_3087_: *mut LeanObject,
    mut v_i_3088_: *mut LeanObject,
    mut v_source_3089_: *mut LeanObject,
    mut v_target_3090_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3091_: *mut LeanObject = core::ptr::null_mut();
    v___x_3091_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Try_Collector_OrdSet_insert___at___00Lean_Meta_Try_Collector_saveConst_spec__0_spec__1_spec__3_spec__4___redArg(v_i_3088_, v_source_3089_, v_target_3090_);
    return v___x_3091_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Try_Collector_OrdSet_insert___at___00Lean_Meta_Try_Collector_saveConst_spec__0_spec__1_spec__3_spec__4_spec__5(
    mut v_00_u03b2_3092_: *mut LeanObject,
    mut v_x_3093_: *mut LeanObject,
    mut v_x_3094_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3095_: *mut LeanObject = core::ptr::null_mut();
    v___x_3095_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Try_Collector_OrdSet_insert___at___00Lean_Meta_Try_Collector_saveConst_spec__0_spec__1_spec__3_spec__4_spec__5___redArg(v_x_3093_, v_x_3094_);
    return v___x_3095_;
}
pub unsafe fn l_Lean_Meta_Try_Collector_inCurrentModule___redArg(
    mut v_declName_3096_: *mut LeanObject,
    mut v_a_3097_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3099_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_3100_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3101_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3102_: u8 = 0;
    let mut v___x_3103_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3104_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3106_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3107_: u8 = 0;
    let mut v___x_3108_: u8 = 0;
    let mut v___x_3109_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3111_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3112_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3113_: u8 = 0;
    let mut v_unused_3114_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3099_ = lean_st_ref_get(v_a_3097_);
                v_env_3100_ = lean_ctor_get(v___x_3099_, 0);
                lean_inc_ref(v_env_3100_);
                lean_dec(v___x_3099_);
                v___x_3101_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_3100_, v_declName_3096_);
                lean_dec_ref(v_env_3100_);
                if lean_obj_tag(v___x_3101_) == 0 {
                    v___x_3102_ = 1;
                    v___x_3103_ = lean_box((v___x_3102_) as usize);
                    v___x_3104_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_3104_, 0, v___x_3103_);
                    return v___x_3104_;
                } else {
                    v_isSharedCheck_3113_ = (!lean_is_exclusive(v___x_3101_)) as u8;
                    if v_isSharedCheck_3113_ == 0 {
                        v_unused_3114_ = lean_ctor_get(v___x_3101_, 0);
                        lean_dec(v_unused_3114_);
                        v___x_3106_ = v___x_3101_;
                        v_isShared_3107_ = v_isSharedCheck_3113_;
                        state = 1;
                        continue;
                    } else {
                        lean_dec(v___x_3101_);
                        v___x_3106_ = lean_box(0);
                        v_isShared_3107_ = v_isSharedCheck_3113_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_3108_ = 0;
                v___x_3109_ = lean_box((v___x_3108_) as usize);
                if v_isShared_3107_ == 0 {
                    lean_ctor_set_tag(v___x_3106_, 0);
                    lean_ctor_set(v___x_3106_, 0, v___x_3109_);
                    v___x_3111_ = v___x_3106_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3112_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3112_, 0, v___x_3109_);
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
    mut v_declName_3115_: *mut LeanObject,
    mut v_a_3116_: *mut LeanObject,
    mut v_a_3117_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3118_: *mut LeanObject = core::ptr::null_mut();
    v_res_3118_ = l_Lean_Meta_Try_Collector_inCurrentModule___redArg(v_declName_3115_, v_a_3116_);
    lean_dec(v_a_3116_);
    lean_dec(v_declName_3115_);
    return v_res_3118_;
}
pub unsafe fn l_Lean_Meta_Try_Collector_inCurrentModule(
    mut v_declName_3119_: *mut LeanObject,
    mut v_a_3120_: *mut LeanObject,
    mut v_a_3121_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3123_: *mut LeanObject = core::ptr::null_mut();
    v___x_3123_ = l_Lean_Meta_Try_Collector_inCurrentModule___redArg(v_declName_3119_, v_a_3121_);
    return v___x_3123_;
}
pub unsafe fn l_Lean_Meta_Try_Collector_inCurrentModule___boxed(
    mut v_declName_3124_: *mut LeanObject,
    mut v_a_3125_: *mut LeanObject,
    mut v_a_3126_: *mut LeanObject,
    mut v_a_3127_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3128_: *mut LeanObject = core::ptr::null_mut();
    v_res_3128_ = l_Lean_Meta_Try_Collector_inCurrentModule(v_declName_3124_, v_a_3125_, v_a_3126_);
    lean_dec(v_a_3126_);
    lean_dec_ref(v_a_3125_);
    lean_dec(v_declName_3124_);
    return v_res_3128_;
}
pub unsafe fn l_Lean_Meta_Try_Collector_isEligible___redArg(
    mut v_declName_3129_: *mut LeanObject,
    mut v_a_3130_: *mut LeanObject,
    mut v_a_3131_: *mut LeanObject,
    mut v_a_3132_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3134_: u8 = 0;
    v___x_3134_ = l_Lean_Name_hasMacroScopes(v_declName_3129_);
    if v___x_3134_ == 0 {
        let mut v_main_3135_: u8 = 0;
        v_main_3135_ = lean_ctor_get_uint8(
            v_a_3130_,
            (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
        );
        if v_main_3135_ == 0 {
            let mut v_name_3136_: u8 = 0;
            v_name_3136_ = lean_ctor_get_uint8(
                v_a_3130_,
                (core::mem::size_of::<*mut LeanObject>() * 1 + 1) as u32,
            );
            if v_name_3136_ == 0 {
                let mut v___x_3137_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_3138_: *mut LeanObject = core::ptr::null_mut();
                v___x_3137_ = lean_box((v_name_3136_) as usize);
                v___x_3138_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_3138_, 0, v___x_3137_);
                return v___x_3138_;
            } else {
                let mut v_currNamespace_3139_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_3140_: u8 = 0;
                let mut v___x_3141_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_3142_: *mut LeanObject = core::ptr::null_mut();
                v_currNamespace_3139_ = lean_ctor_get(v_a_3131_, 6);
                v___x_3140_ = l_Lean_Name_isPrefixOf(v_currNamespace_3139_, v_declName_3129_);
                v___x_3141_ = lean_box((v___x_3140_) as usize);
                v___x_3142_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_3142_, 0, v___x_3141_);
                return v___x_3142_;
            }
        } else {
            let mut v___x_3143_: *mut LeanObject = core::ptr::null_mut();
            v___x_3143_ =
                l_Lean_Meta_Try_Collector_inCurrentModule___redArg(v_declName_3129_, v_a_3132_);
            return v___x_3143_;
        }
    } else {
        let mut v___x_3144_: u8 = 0;
        let mut v___x_3145_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3146_: *mut LeanObject = core::ptr::null_mut();
        v___x_3144_ = 0;
        v___x_3145_ = lean_box((v___x_3144_) as usize);
        v___x_3146_ = lean_alloc_ctor(0, 1, (0) as u32);
        lean_ctor_set(v___x_3146_, 0, v___x_3145_);
        return v___x_3146_;
    }
}
pub unsafe fn l_Lean_Meta_Try_Collector_isEligible___redArg___boxed(
    mut v_declName_3147_: *mut LeanObject,
    mut v_a_3148_: *mut LeanObject,
    mut v_a_3149_: *mut LeanObject,
    mut v_a_3150_: *mut LeanObject,
    mut v_a_3151_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3152_: *mut LeanObject = core::ptr::null_mut();
    v_res_3152_ = l_Lean_Meta_Try_Collector_isEligible___redArg(
        v_declName_3147_,
        v_a_3148_,
        v_a_3149_,
        v_a_3150_,
    );
    lean_dec(v_a_3150_);
    lean_dec_ref(v_a_3149_);
    lean_dec_ref(v_a_3148_);
    lean_dec(v_declName_3147_);
    return v_res_3152_;
}
pub unsafe fn l_Lean_Meta_Try_Collector_isEligible(
    mut v_declName_3153_: *mut LeanObject,
    mut v_a_3154_: *mut LeanObject,
    mut v_a_3155_: *mut LeanObject,
    mut v_a_3156_: *mut LeanObject,
    mut v_a_3157_: *mut LeanObject,
    mut v_a_3158_: *mut LeanObject,
    mut v_a_3159_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3161_: *mut LeanObject = core::ptr::null_mut();
    v___x_3161_ = l_Lean_Meta_Try_Collector_isEligible___redArg(
        v_declName_3153_,
        v_a_3154_,
        v_a_3158_,
        v_a_3159_,
    );
    return v___x_3161_;
}
pub unsafe fn l_Lean_Meta_Try_Collector_isEligible___boxed(
    mut v_declName_3162_: *mut LeanObject,
    mut v_a_3163_: *mut LeanObject,
    mut v_a_3164_: *mut LeanObject,
    mut v_a_3165_: *mut LeanObject,
    mut v_a_3166_: *mut LeanObject,
    mut v_a_3167_: *mut LeanObject,
    mut v_a_3168_: *mut LeanObject,
    mut v_a_3169_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3170_: *mut LeanObject = core::ptr::null_mut();
    v_res_3170_ = l_Lean_Meta_Try_Collector_isEligible(
        v_declName_3162_,
        v_a_3163_,
        v_a_3164_,
        v_a_3165_,
        v_a_3166_,
        v_a_3167_,
        v_a_3168_,
    );
    lean_dec(v_a_3168_);
    lean_dec_ref(v_a_3167_);
    lean_dec(v_a_3166_);
    lean_dec_ref(v_a_3165_);
    lean_dec(v_a_3164_);
    lean_dec_ref(v_a_3163_);
    lean_dec(v_declName_3162_);
    return v_res_3170_;
}
pub unsafe fn l_Lean_Meta_Try_Collector_saveEqnCandidate(
    mut v_declName_3171_: *mut LeanObject,
    mut v_a_3172_: *mut LeanObject,
    mut v_a_3173_: *mut LeanObject,
    mut v_a_3174_: *mut LeanObject,
    mut v_a_3175_: *mut LeanObject,
    mut v_a_3176_: *mut LeanObject,
    mut v_a_3177_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3179_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3180_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3182_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3183_: u8 = 0;
    let mut v___x_3184_: u8 = 0;
    let mut v___x_3185_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3187_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3188_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3189_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3190_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3192_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3193_: u8 = 0;
    let mut v_val_3194_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3195_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3196_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3197_: u8 = 0;
    let mut v___x_3198_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3199_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3200_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3201_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3202_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3204_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3205_: u8 = 0;
    let mut v___x_3206_: u8 = 0;
    let mut v___x_3207_: *mut LeanObject = core::ptr::null_mut();
    let mut v_allConsts_3208_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unfoldCandidates_3209_: *mut LeanObject = core::ptr::null_mut();
    let mut v_eqnCandidates_3210_: *mut LeanObject = core::ptr::null_mut();
    let mut v_funIndCandidates_3211_: *mut LeanObject = core::ptr::null_mut();
    let mut v_indCandidates_3212_: *mut LeanObject = core::ptr::null_mut();
    let mut v_libSearchResults_3213_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3215_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3216_: u8 = 0;
    let mut v___x_3217_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3219_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3220_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3221_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3223_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3224_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3225_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3226_: u8 = 0;
    let mut v___x_3227_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3229_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3230_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3231_: u8 = 0;
    let mut v_a_3232_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3234_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3235_: u8 = 0;
    let mut v___x_3237_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3238_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3239_: u8 = 0;
    let mut v___x_3240_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3242_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3243_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3244_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3246_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3247_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3248_: u8 = 0;
    let mut v_a_3249_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3251_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3252_: u8 = 0;
    let mut v___x_3254_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3255_: *mut LeanObject = core::ptr::null_mut();
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
                v_a_3180_ = lean_ctor_get(v___x_3179_, 0);
                v_isSharedCheck_3257_ = (!lean_is_exclusive(v___x_3179_)) as u8;
                if v_isSharedCheck_3257_ == 0 {
                    v___x_3182_ = v___x_3179_;
                    v_isShared_3183_ = v_isSharedCheck_3257_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_a_3180_);
                    lean_dec(v___x_3179_);
                    v___x_3182_ = lean_box(0);
                    v_isShared_3183_ = v_isSharedCheck_3257_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_3184_ = (lean_unbox(v_a_3180_) as u8);
                lean_dec(v_a_3180_);
                if v___x_3184_ == 0 {
                    lean_dec(v_declName_3171_);
                    v___x_3185_ = lean_box(0);
                    if v_isShared_3183_ == 0 {
                        lean_ctor_set(v___x_3182_, 0, v___x_3185_);
                        v___x_3187_ = v___x_3182_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_3188_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_3188_, 0, v___x_3185_);
                        v___x_3187_ = v_reuseFailAlloc_3188_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_3182_);
                    lean_inc(v_declName_3171_);
                    v___x_3189_ = l_Lean_Meta_getEqnsFor_x3f(
                        v_declName_3171_,
                        v_a_3174_,
                        v_a_3175_,
                        v_a_3176_,
                        v_a_3177_,
                    );
                    if lean_obj_tag(v___x_3189_) == 0 {
                        v_a_3190_ = lean_ctor_get(v___x_3189_, 0);
                        v_isSharedCheck_3248_ = (!lean_is_exclusive(v___x_3189_)) as u8;
                        if v_isSharedCheck_3248_ == 0 {
                            v___x_3192_ = v___x_3189_;
                            v_isShared_3193_ = v_isSharedCheck_3248_;
                            state = 3;
                            continue;
                        } else {
                            lean_inc(v_a_3190_);
                            lean_dec(v___x_3189_);
                            v___x_3192_ = lean_box(0);
                            v_isShared_3193_ = v_isSharedCheck_3248_;
                            state = 3;
                            continue;
                        }
                    } else {
                        lean_dec(v_declName_3171_);
                        v_a_3249_ = lean_ctor_get(v___x_3189_, 0);
                        v_isSharedCheck_3256_ = (!lean_is_exclusive(v___x_3189_)) as u8;
                        if v_isSharedCheck_3256_ == 0 {
                            v___x_3251_ = v___x_3189_;
                            v_isShared_3252_ = v_isSharedCheck_3256_;
                            state = 13;
                            continue;
                        } else {
                            lean_inc(v_a_3249_);
                            lean_dec(v___x_3189_);
                            v___x_3251_ = lean_box(0);
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
                if lean_obj_tag(v_a_3190_) == 1 {
                    v_val_3194_ = lean_ctor_get(v_a_3190_, 0);
                    lean_inc(v_val_3194_);
                    lean_dec_ref_known(v_a_3190_, 1);
                    v___x_3195_ = lean_array_get_size(v_val_3194_);
                    v___x_3196_ = lean_unsigned_to_nat(0);
                    v___x_3197_ = lean_nat_dec_eq(v___x_3195_, v___x_3196_);
                    if v___x_3197_ == 0 {
                        lean_del_object(v___x_3192_);
                        v___x_3198_ = l_Lean_Meta_Grind_grindExt;
                        v___x_3199_ = lean_box(0);
                        v___x_3200_ = lean_array_get(v___x_3199_, v_val_3194_, v___x_3196_);
                        lean_dec(v_val_3194_);
                        v___x_3201_ = l_Lean_Meta_Grind_Extension_isEMatchTheorem___redArg(
                            v___x_3198_,
                            v___x_3200_,
                            v_a_3177_,
                        );
                        if lean_obj_tag(v___x_3201_) == 0 {
                            v_a_3202_ = lean_ctor_get(v___x_3201_, 0);
                            v_isSharedCheck_3231_ = (!lean_is_exclusive(v___x_3201_)) as u8;
                            if v_isSharedCheck_3231_ == 0 {
                                v___x_3204_ = v___x_3201_;
                                v_isShared_3205_ = v_isSharedCheck_3231_;
                                state = 4;
                                continue;
                            } else {
                                lean_inc(v_a_3202_);
                                lean_dec(v___x_3201_);
                                v___x_3204_ = lean_box(0);
                                v_isShared_3205_ = v_isSharedCheck_3231_;
                                state = 4;
                                continue;
                            }
                        } else {
                            lean_dec(v_declName_3171_);
                            v_a_3232_ = lean_ctor_get(v___x_3201_, 0);
                            v_isSharedCheck_3239_ = (!lean_is_exclusive(v___x_3201_)) as u8;
                            if v_isSharedCheck_3239_ == 0 {
                                v___x_3234_ = v___x_3201_;
                                v_isShared_3235_ = v_isSharedCheck_3239_;
                                state = 9;
                                continue;
                            } else {
                                lean_inc(v_a_3232_);
                                lean_dec(v___x_3201_);
                                v___x_3234_ = lean_box(0);
                                v_isShared_3235_ = v_isSharedCheck_3239_;
                                state = 9;
                                continue;
                            }
                        }
                    } else {
                        lean_dec(v_val_3194_);
                        lean_dec(v_declName_3171_);
                        v___x_3240_ = lean_box(0);
                        if v_isShared_3193_ == 0 {
                            lean_ctor_set(v___x_3192_, 0, v___x_3240_);
                            v___x_3242_ = v___x_3192_;
                            state = 11;
                            continue;
                        } else {
                            v_reuseFailAlloc_3243_ = lean_alloc_ctor(0, 1, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_3243_, 0, v___x_3240_);
                            v___x_3242_ = v_reuseFailAlloc_3243_;
                            state = 11;
                            continue;
                        }
                    }
                } else {
                    lean_dec(v_a_3190_);
                    lean_dec(v_declName_3171_);
                    v___x_3244_ = lean_box(0);
                    if v_isShared_3193_ == 0 {
                        lean_ctor_set(v___x_3192_, 0, v___x_3244_);
                        v___x_3246_ = v___x_3192_;
                        state = 12;
                        continue;
                    } else {
                        v_reuseFailAlloc_3247_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_3247_, 0, v___x_3244_);
                        v___x_3246_ = v_reuseFailAlloc_3247_;
                        state = 12;
                        continue;
                    }
                }
            }
            4 => {
                v___x_3206_ = (lean_unbox(v_a_3202_) as u8);
                lean_dec(v_a_3202_);
                if v___x_3206_ == 0 {
                    v___x_3207_ = lean_st_ref_take(v_a_3173_);
                    v_allConsts_3208_ = lean_ctor_get(v___x_3207_, 0);
                    v_unfoldCandidates_3209_ = lean_ctor_get(v___x_3207_, 1);
                    v_eqnCandidates_3210_ = lean_ctor_get(v___x_3207_, 2);
                    v_funIndCandidates_3211_ = lean_ctor_get(v___x_3207_, 3);
                    v_indCandidates_3212_ = lean_ctor_get(v___x_3207_, 4);
                    v_libSearchResults_3213_ = lean_ctor_get(v___x_3207_, 5);
                    v_isSharedCheck_3226_ = (!lean_is_exclusive(v___x_3207_)) as u8;
                    if v_isSharedCheck_3226_ == 0 {
                        v___x_3215_ = v___x_3207_;
                        v_isShared_3216_ = v_isSharedCheck_3226_;
                        state = 5;
                        continue;
                    } else {
                        lean_inc(v_libSearchResults_3213_);
                        lean_inc(v_indCandidates_3212_);
                        lean_inc(v_funIndCandidates_3211_);
                        lean_inc(v_eqnCandidates_3210_);
                        lean_inc(v_unfoldCandidates_3209_);
                        lean_inc(v_allConsts_3208_);
                        lean_dec(v___x_3207_);
                        v___x_3215_ = lean_box(0);
                        v_isShared_3216_ = v_isSharedCheck_3226_;
                        state = 5;
                        continue;
                    }
                } else {
                    lean_dec(v_declName_3171_);
                    v___x_3227_ = lean_box(0);
                    if v_isShared_3205_ == 0 {
                        lean_ctor_set(v___x_3204_, 0, v___x_3227_);
                        v___x_3229_ = v___x_3204_;
                        state = 8;
                        continue;
                    } else {
                        v_reuseFailAlloc_3230_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_3230_, 0, v___x_3227_);
                        v___x_3229_ = v_reuseFailAlloc_3230_;
                        state = 8;
                        continue;
                    }
                }
            }
            5 => {
                v___x_3217_ = l_Lean_Meta_Try_Collector_OrdSet_insert___at___00Lean_Meta_Try_Collector_saveConst_spec__0(v_eqnCandidates_3210_, v_declName_3171_);
                if v_isShared_3216_ == 0 {
                    lean_ctor_set(v___x_3215_, 2, v___x_3217_);
                    v___x_3219_ = v___x_3215_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_3225_ = lean_alloc_ctor(0, 6, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3225_, 0, v_allConsts_3208_);
                    lean_ctor_set(v_reuseFailAlloc_3225_, 1, v_unfoldCandidates_3209_);
                    lean_ctor_set(v_reuseFailAlloc_3225_, 2, v___x_3217_);
                    lean_ctor_set(v_reuseFailAlloc_3225_, 3, v_funIndCandidates_3211_);
                    lean_ctor_set(v_reuseFailAlloc_3225_, 4, v_indCandidates_3212_);
                    lean_ctor_set(v_reuseFailAlloc_3225_, 5, v_libSearchResults_3213_);
                    v___x_3219_ = v_reuseFailAlloc_3225_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                v___x_3220_ = lean_st_ref_set(v_a_3173_, v___x_3219_);
                v___x_3221_ = lean_box(0);
                if v_isShared_3205_ == 0 {
                    lean_ctor_set(v___x_3204_, 0, v___x_3221_);
                    v___x_3223_ = v___x_3204_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_3224_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3224_, 0, v___x_3221_);
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
                    v_reuseFailAlloc_3238_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3238_, 0, v_a_3232_);
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
                    v_reuseFailAlloc_3255_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3255_, 0, v_a_3249_);
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
    mut v_declName_3258_: *mut LeanObject,
    mut v_a_3259_: *mut LeanObject,
    mut v_a_3260_: *mut LeanObject,
    mut v_a_3261_: *mut LeanObject,
    mut v_a_3262_: *mut LeanObject,
    mut v_a_3263_: *mut LeanObject,
    mut v_a_3264_: *mut LeanObject,
    mut v_a_3265_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3266_: *mut LeanObject = core::ptr::null_mut();
    v_res_3266_ = l_Lean_Meta_Try_Collector_saveEqnCandidate(
        v_declName_3258_,
        v_a_3259_,
        v_a_3260_,
        v_a_3261_,
        v_a_3262_,
        v_a_3263_,
        v_a_3264_,
    );
    lean_dec(v_a_3264_);
    lean_dec_ref(v_a_3263_);
    lean_dec(v_a_3262_);
    lean_dec_ref(v_a_3261_);
    lean_dec(v_a_3260_);
    lean_dec_ref(v_a_3259_);
    return v_res_3266_;
}
pub unsafe fn l_Lean_Meta_Try_Collector_getEqDefDecl_x3f___redArg(
    mut v_declName_3270_: *mut LeanObject,
    mut v_a_3271_: *mut LeanObject,
    mut v_a_3272_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3274_: *mut LeanObject = core::ptr::null_mut();
    let mut v_declName_3275_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3276_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3277_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3278_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3280_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3281_: u8 = 0;
    let mut v___x_3282_: u8 = 0;
    let mut v___x_3283_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3284_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3286_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3287_: u8 = 0;
    let mut v___x_3288_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3290_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3291_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3292_: u8 = 0;
    let mut v_a_3293_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3295_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3296_: u8 = 0;
    let mut v___y_3298_: u8 = 0;
    let mut v___x_3299_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3301_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3302_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3304_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3305_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3306_: u8 = 0;
    let mut v___x_3307_: u8 = 0;
    let mut v_isSharedCheck_3308_: u8 = 0;
    let mut v___x_3309_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3311_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3312_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3313_: u8 = 0;
    let mut v_a_3314_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3316_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3317_: u8 = 0;
    let mut v___x_3319_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3320_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3321_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3274_ = l_Lean_Meta_Try_Collector_getEqDefDecl_x3f___redArg___closed__1;
                v_declName_3275_ = l_Lean_Name_append(v_declName_3270_, v___x_3274_);
                v___x_3276_ = l_Lean_Meta_Grind_grindExt;
                lean_inc(v_declName_3275_);
                v___x_3277_ = l_Lean_Meta_Grind_Extension_isEMatchTheorem___redArg(
                    v___x_3276_,
                    v_declName_3275_,
                    v_a_3272_,
                );
                if lean_obj_tag(v___x_3277_) == 0 {
                    v_a_3278_ = lean_ctor_get(v___x_3277_, 0);
                    v_isSharedCheck_3313_ = (!lean_is_exclusive(v___x_3277_)) as u8;
                    if v_isSharedCheck_3313_ == 0 {
                        v___x_3280_ = v___x_3277_;
                        v_isShared_3281_ = v_isSharedCheck_3313_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_3278_);
                        lean_dec(v___x_3277_);
                        v___x_3280_ = lean_box(0);
                        v_isShared_3281_ = v_isSharedCheck_3313_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec(v_declName_3275_);
                    v_a_3314_ = lean_ctor_get(v___x_3277_, 0);
                    v_isSharedCheck_3321_ = (!lean_is_exclusive(v___x_3277_)) as u8;
                    if v_isSharedCheck_3321_ == 0 {
                        v___x_3316_ = v___x_3277_;
                        v_isShared_3317_ = v_isSharedCheck_3321_;
                        state = 9;
                        continue;
                    } else {
                        lean_inc(v_a_3314_);
                        lean_dec(v___x_3277_);
                        v___x_3316_ = lean_box(0);
                        v_isShared_3317_ = v_isSharedCheck_3321_;
                        state = 9;
                        continue;
                    }
                }
            }
            1 => {
                v___x_3282_ = (lean_unbox(v_a_3278_) as u8);
                lean_dec(v_a_3278_);
                if v___x_3282_ == 0 {
                    lean_del_object(v___x_3280_);
                    v___x_3283_ = l_Lean_realizeGlobalConstNoOverloadCore(
                        v_declName_3275_,
                        v_a_3271_,
                        v_a_3272_,
                    );
                    if lean_obj_tag(v___x_3283_) == 0 {
                        v_a_3284_ = lean_ctor_get(v___x_3283_, 0);
                        v_isSharedCheck_3292_ = (!lean_is_exclusive(v___x_3283_)) as u8;
                        if v_isSharedCheck_3292_ == 0 {
                            v___x_3286_ = v___x_3283_;
                            v_isShared_3287_ = v_isSharedCheck_3292_;
                            state = 2;
                            continue;
                        } else {
                            lean_inc(v_a_3284_);
                            lean_dec(v___x_3283_);
                            v___x_3286_ = lean_box(0);
                            v_isShared_3287_ = v_isSharedCheck_3292_;
                            state = 2;
                            continue;
                        }
                    } else {
                        v_a_3293_ = lean_ctor_get(v___x_3283_, 0);
                        v_isSharedCheck_3308_ = (!lean_is_exclusive(v___x_3283_)) as u8;
                        if v_isSharedCheck_3308_ == 0 {
                            v___x_3295_ = v___x_3283_;
                            v_isShared_3296_ = v_isSharedCheck_3308_;
                            state = 4;
                            continue;
                        } else {
                            lean_inc(v_a_3293_);
                            lean_dec(v___x_3283_);
                            v___x_3295_ = lean_box(0);
                            v_isShared_3296_ = v_isSharedCheck_3308_;
                            state = 4;
                            continue;
                        }
                    }
                } else {
                    lean_dec(v_declName_3275_);
                    v___x_3309_ = lean_box(0);
                    if v_isShared_3281_ == 0 {
                        lean_ctor_set(v___x_3280_, 0, v___x_3309_);
                        v___x_3311_ = v___x_3280_;
                        state = 8;
                        continue;
                    } else {
                        v_reuseFailAlloc_3312_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_3312_, 0, v___x_3309_);
                        v___x_3311_ = v_reuseFailAlloc_3312_;
                        state = 8;
                        continue;
                    }
                }
            }
            2 => {
                v___x_3288_ = lean_alloc_ctor(1, 1, (0) as u32);
                lean_ctor_set(v___x_3288_, 0, v_a_3284_);
                if v_isShared_3287_ == 0 {
                    lean_ctor_set(v___x_3286_, 0, v___x_3288_);
                    v___x_3290_ = v___x_3286_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_3291_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3291_, 0, v___x_3288_);
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
                    lean_inc(v_a_3293_);
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
                    lean_dec(v_a_3293_);
                    v___x_3299_ = lean_box(0);
                    if v_isShared_3296_ == 0 {
                        lean_ctor_set_tag(v___x_3295_, 0);
                        lean_ctor_set(v___x_3295_, 0, v___x_3299_);
                        v___x_3301_ = v___x_3295_;
                        state = 6;
                        continue;
                    } else {
                        v_reuseFailAlloc_3302_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_3302_, 0, v___x_3299_);
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
                        v_reuseFailAlloc_3305_ = lean_alloc_ctor(1, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_3305_, 0, v_a_3293_);
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
                    v_reuseFailAlloc_3320_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3320_, 0, v_a_3314_);
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
    mut v_declName_3322_: *mut LeanObject,
    mut v_a_3323_: *mut LeanObject,
    mut v_a_3324_: *mut LeanObject,
    mut v_a_3325_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3326_: *mut LeanObject = core::ptr::null_mut();
    v_res_3326_ =
        l_Lean_Meta_Try_Collector_getEqDefDecl_x3f___redArg(v_declName_3322_, v_a_3323_, v_a_3324_);
    lean_dec(v_a_3324_);
    lean_dec_ref(v_a_3323_);
    return v_res_3326_;
}
pub unsafe fn l_Lean_Meta_Try_Collector_getEqDefDecl_x3f(
    mut v_declName_3327_: *mut LeanObject,
    mut v_a_3328_: *mut LeanObject,
    mut v_a_3329_: *mut LeanObject,
    mut v_a_3330_: *mut LeanObject,
    mut v_a_3331_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3333_: *mut LeanObject = core::ptr::null_mut();
    v___x_3333_ =
        l_Lean_Meta_Try_Collector_getEqDefDecl_x3f___redArg(v_declName_3327_, v_a_3330_, v_a_3331_);
    return v___x_3333_;
}
pub unsafe fn l_Lean_Meta_Try_Collector_getEqDefDecl_x3f___boxed(
    mut v_declName_3334_: *mut LeanObject,
    mut v_a_3335_: *mut LeanObject,
    mut v_a_3336_: *mut LeanObject,
    mut v_a_3337_: *mut LeanObject,
    mut v_a_3338_: *mut LeanObject,
    mut v_a_3339_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3340_: *mut LeanObject = core::ptr::null_mut();
    v_res_3340_ = l_Lean_Meta_Try_Collector_getEqDefDecl_x3f(
        v_declName_3334_,
        v_a_3335_,
        v_a_3336_,
        v_a_3337_,
        v_a_3338_,
    );
    lean_dec(v_a_3338_);
    lean_dec_ref(v_a_3337_);
    lean_dec(v_a_3336_);
    lean_dec_ref(v_a_3335_);
    return v_res_3340_;
}
pub unsafe fn l_Lean_Meta_Try_Collector_saveUnfoldCandidate___redArg(
    mut v_declName_3341_: *mut LeanObject,
    mut v_a_3342_: *mut LeanObject,
    mut v_a_3343_: *mut LeanObject,
    mut v_a_3344_: *mut LeanObject,
    mut v_a_3345_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3347_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3348_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3350_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3351_: u8 = 0;
    let mut v___x_3352_: u8 = 0;
    let mut v___x_3353_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3355_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3356_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3357_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3358_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3360_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3361_: u8 = 0;
    let mut v_val_3362_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3363_: *mut LeanObject = core::ptr::null_mut();
    let mut v_allConsts_3364_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unfoldCandidates_3365_: *mut LeanObject = core::ptr::null_mut();
    let mut v_eqnCandidates_3366_: *mut LeanObject = core::ptr::null_mut();
    let mut v_funIndCandidates_3367_: *mut LeanObject = core::ptr::null_mut();
    let mut v_indCandidates_3368_: *mut LeanObject = core::ptr::null_mut();
    let mut v_libSearchResults_3369_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3371_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3372_: u8 = 0;
    let mut v___x_3373_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3375_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3376_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3377_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3379_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3380_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3381_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3382_: u8 = 0;
    let mut v___x_3383_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3385_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3386_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3387_: u8 = 0;
    let mut v_a_3388_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3390_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3391_: u8 = 0;
    let mut v___x_3393_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3394_: *mut LeanObject = core::ptr::null_mut();
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
                v_a_3348_ = lean_ctor_get(v___x_3347_, 0);
                v_isSharedCheck_3396_ = (!lean_is_exclusive(v___x_3347_)) as u8;
                if v_isSharedCheck_3396_ == 0 {
                    v___x_3350_ = v___x_3347_;
                    v_isShared_3351_ = v_isSharedCheck_3396_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_a_3348_);
                    lean_dec(v___x_3347_);
                    v___x_3350_ = lean_box(0);
                    v_isShared_3351_ = v_isSharedCheck_3396_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_3352_ = (lean_unbox(v_a_3348_) as u8);
                lean_dec(v_a_3348_);
                if v___x_3352_ == 0 {
                    lean_dec(v_declName_3341_);
                    v___x_3353_ = lean_box(0);
                    if v_isShared_3351_ == 0 {
                        lean_ctor_set(v___x_3350_, 0, v___x_3353_);
                        v___x_3355_ = v___x_3350_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_3356_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_3356_, 0, v___x_3353_);
                        v___x_3355_ = v_reuseFailAlloc_3356_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_3350_);
                    v___x_3357_ = l_Lean_Meta_Try_Collector_getEqDefDecl_x3f___redArg(
                        v_declName_3341_,
                        v_a_3344_,
                        v_a_3345_,
                    );
                    if lean_obj_tag(v___x_3357_) == 0 {
                        v_a_3358_ = lean_ctor_get(v___x_3357_, 0);
                        v_isSharedCheck_3387_ = (!lean_is_exclusive(v___x_3357_)) as u8;
                        if v_isSharedCheck_3387_ == 0 {
                            v___x_3360_ = v___x_3357_;
                            v_isShared_3361_ = v_isSharedCheck_3387_;
                            state = 3;
                            continue;
                        } else {
                            lean_inc(v_a_3358_);
                            lean_dec(v___x_3357_);
                            v___x_3360_ = lean_box(0);
                            v_isShared_3361_ = v_isSharedCheck_3387_;
                            state = 3;
                            continue;
                        }
                    } else {
                        v_a_3388_ = lean_ctor_get(v___x_3357_, 0);
                        v_isSharedCheck_3395_ = (!lean_is_exclusive(v___x_3357_)) as u8;
                        if v_isSharedCheck_3395_ == 0 {
                            v___x_3390_ = v___x_3357_;
                            v_isShared_3391_ = v_isSharedCheck_3395_;
                            state = 8;
                            continue;
                        } else {
                            lean_inc(v_a_3388_);
                            lean_dec(v___x_3357_);
                            v___x_3390_ = lean_box(0);
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
                if lean_obj_tag(v_a_3358_) == 1 {
                    v_val_3362_ = lean_ctor_get(v_a_3358_, 0);
                    lean_inc(v_val_3362_);
                    lean_dec_ref_known(v_a_3358_, 1);
                    v___x_3363_ = lean_st_ref_take(v_a_3343_);
                    v_allConsts_3364_ = lean_ctor_get(v___x_3363_, 0);
                    v_unfoldCandidates_3365_ = lean_ctor_get(v___x_3363_, 1);
                    v_eqnCandidates_3366_ = lean_ctor_get(v___x_3363_, 2);
                    v_funIndCandidates_3367_ = lean_ctor_get(v___x_3363_, 3);
                    v_indCandidates_3368_ = lean_ctor_get(v___x_3363_, 4);
                    v_libSearchResults_3369_ = lean_ctor_get(v___x_3363_, 5);
                    v_isSharedCheck_3382_ = (!lean_is_exclusive(v___x_3363_)) as u8;
                    if v_isSharedCheck_3382_ == 0 {
                        v___x_3371_ = v___x_3363_;
                        v_isShared_3372_ = v_isSharedCheck_3382_;
                        state = 4;
                        continue;
                    } else {
                        lean_inc(v_libSearchResults_3369_);
                        lean_inc(v_indCandidates_3368_);
                        lean_inc(v_funIndCandidates_3367_);
                        lean_inc(v_eqnCandidates_3366_);
                        lean_inc(v_unfoldCandidates_3365_);
                        lean_inc(v_allConsts_3364_);
                        lean_dec(v___x_3363_);
                        v___x_3371_ = lean_box(0);
                        v_isShared_3372_ = v_isSharedCheck_3382_;
                        state = 4;
                        continue;
                    }
                } else {
                    lean_dec(v_a_3358_);
                    v___x_3383_ = lean_box(0);
                    if v_isShared_3361_ == 0 {
                        lean_ctor_set(v___x_3360_, 0, v___x_3383_);
                        v___x_3385_ = v___x_3360_;
                        state = 7;
                        continue;
                    } else {
                        v_reuseFailAlloc_3386_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_3386_, 0, v___x_3383_);
                        v___x_3385_ = v_reuseFailAlloc_3386_;
                        state = 7;
                        continue;
                    }
                }
            }
            4 => {
                v___x_3373_ = l_Lean_Meta_Try_Collector_OrdSet_insert___at___00Lean_Meta_Try_Collector_saveConst_spec__0(v_unfoldCandidates_3365_, v_val_3362_);
                if v_isShared_3372_ == 0 {
                    lean_ctor_set(v___x_3371_, 1, v___x_3373_);
                    v___x_3375_ = v___x_3371_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_3381_ = lean_alloc_ctor(0, 6, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3381_, 0, v_allConsts_3364_);
                    lean_ctor_set(v_reuseFailAlloc_3381_, 1, v___x_3373_);
                    lean_ctor_set(v_reuseFailAlloc_3381_, 2, v_eqnCandidates_3366_);
                    lean_ctor_set(v_reuseFailAlloc_3381_, 3, v_funIndCandidates_3367_);
                    lean_ctor_set(v_reuseFailAlloc_3381_, 4, v_indCandidates_3368_);
                    lean_ctor_set(v_reuseFailAlloc_3381_, 5, v_libSearchResults_3369_);
                    v___x_3375_ = v_reuseFailAlloc_3381_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v___x_3376_ = lean_st_ref_set(v_a_3343_, v___x_3375_);
                v___x_3377_ = lean_box(0);
                if v_isShared_3361_ == 0 {
                    lean_ctor_set(v___x_3360_, 0, v___x_3377_);
                    v___x_3379_ = v___x_3360_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_3380_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3380_, 0, v___x_3377_);
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
                    v_reuseFailAlloc_3394_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3394_, 0, v_a_3388_);
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
    mut v_declName_3397_: *mut LeanObject,
    mut v_a_3398_: *mut LeanObject,
    mut v_a_3399_: *mut LeanObject,
    mut v_a_3400_: *mut LeanObject,
    mut v_a_3401_: *mut LeanObject,
    mut v_a_3402_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3403_: *mut LeanObject = core::ptr::null_mut();
    v_res_3403_ = l_Lean_Meta_Try_Collector_saveUnfoldCandidate___redArg(
        v_declName_3397_,
        v_a_3398_,
        v_a_3399_,
        v_a_3400_,
        v_a_3401_,
    );
    lean_dec(v_a_3401_);
    lean_dec_ref(v_a_3400_);
    lean_dec(v_a_3399_);
    lean_dec_ref(v_a_3398_);
    return v_res_3403_;
}
pub unsafe fn l_Lean_Meta_Try_Collector_saveUnfoldCandidate(
    mut v_declName_3404_: *mut LeanObject,
    mut v_a_3405_: *mut LeanObject,
    mut v_a_3406_: *mut LeanObject,
    mut v_a_3407_: *mut LeanObject,
    mut v_a_3408_: *mut LeanObject,
    mut v_a_3409_: *mut LeanObject,
    mut v_a_3410_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3412_: *mut LeanObject = core::ptr::null_mut();
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
    mut v_declName_3413_: *mut LeanObject,
    mut v_a_3414_: *mut LeanObject,
    mut v_a_3415_: *mut LeanObject,
    mut v_a_3416_: *mut LeanObject,
    mut v_a_3417_: *mut LeanObject,
    mut v_a_3418_: *mut LeanObject,
    mut v_a_3419_: *mut LeanObject,
    mut v_a_3420_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3421_: *mut LeanObject = core::ptr::null_mut();
    v_res_3421_ = l_Lean_Meta_Try_Collector_saveUnfoldCandidate(
        v_declName_3413_,
        v_a_3414_,
        v_a_3415_,
        v_a_3416_,
        v_a_3417_,
        v_a_3418_,
        v_a_3419_,
    );
    lean_dec(v_a_3419_);
    lean_dec_ref(v_a_3418_);
    lean_dec(v_a_3417_);
    lean_dec_ref(v_a_3416_);
    lean_dec(v_a_3415_);
    lean_dec_ref(v_a_3414_);
    return v_res_3421_;
}
pub unsafe fn l_Lean_Meta_Try_Collector_visitConst___redArg(
    mut v_declName_3422_: *mut LeanObject,
    mut v_a_3423_: *mut LeanObject,
    mut v_a_3424_: *mut LeanObject,
    mut v_a_3425_: *mut LeanObject,
    mut v_a_3426_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3428_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3429_: *mut LeanObject = core::ptr::null_mut();
    lean_inc(v_declName_3422_);
    v___x_3428_ = l_Lean_Meta_Try_Collector_saveConst___redArg(v_declName_3422_, v_a_3424_);
    lean_dec_ref(v___x_3428_);
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
    mut v_declName_3430_: *mut LeanObject,
    mut v_a_3431_: *mut LeanObject,
    mut v_a_3432_: *mut LeanObject,
    mut v_a_3433_: *mut LeanObject,
    mut v_a_3434_: *mut LeanObject,
    mut v_a_3435_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3436_: *mut LeanObject = core::ptr::null_mut();
    v_res_3436_ = l_Lean_Meta_Try_Collector_visitConst___redArg(
        v_declName_3430_,
        v_a_3431_,
        v_a_3432_,
        v_a_3433_,
        v_a_3434_,
    );
    lean_dec(v_a_3434_);
    lean_dec_ref(v_a_3433_);
    lean_dec(v_a_3432_);
    lean_dec_ref(v_a_3431_);
    return v_res_3436_;
}
pub unsafe fn l_Lean_Meta_Try_Collector_visitConst(
    mut v_declName_3437_: *mut LeanObject,
    mut v_a_3438_: *mut LeanObject,
    mut v_a_3439_: *mut LeanObject,
    mut v_a_3440_: *mut LeanObject,
    mut v_a_3441_: *mut LeanObject,
    mut v_a_3442_: *mut LeanObject,
    mut v_a_3443_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3445_: *mut LeanObject = core::ptr::null_mut();
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
    mut v_declName_3446_: *mut LeanObject,
    mut v_a_3447_: *mut LeanObject,
    mut v_a_3448_: *mut LeanObject,
    mut v_a_3449_: *mut LeanObject,
    mut v_a_3450_: *mut LeanObject,
    mut v_a_3451_: *mut LeanObject,
    mut v_a_3452_: *mut LeanObject,
    mut v_a_3453_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3454_: *mut LeanObject = core::ptr::null_mut();
    v_res_3454_ = l_Lean_Meta_Try_Collector_visitConst(
        v_declName_3446_,
        v_a_3447_,
        v_a_3448_,
        v_a_3449_,
        v_a_3450_,
        v_a_3451_,
        v_a_3452_,
    );
    lean_dec(v_a_3452_);
    lean_dec_ref(v_a_3451_);
    lean_dec(v_a_3450_);
    lean_dec_ref(v_a_3449_);
    lean_dec(v_a_3448_);
    lean_dec_ref(v_a_3447_);
    return v_res_3454_;
}
pub unsafe fn l_Lean_Meta_Try_Collector_saveFunInd(
    mut v_e_3455_: *mut LeanObject,
    mut v_declName_3456_: *mut LeanObject,
    mut v_args_3457_: *mut LeanObject,
    mut v_a_3458_: *mut LeanObject,
    mut v_a_3459_: *mut LeanObject,
    mut v_a_3460_: *mut LeanObject,
    mut v_a_3461_: *mut LeanObject,
    mut v_a_3462_: *mut LeanObject,
    mut v_a_3463_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3465_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3466_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3468_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3469_: u8 = 0;
    let mut v___x_3470_: u8 = 0;
    let mut v___x_3471_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3473_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3474_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3475_: u8 = 0;
    let mut v___x_3476_: u8 = 0;
    let mut v___x_3477_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3478_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3480_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3481_: u8 = 0;
    let mut v_val_3482_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3483_: *mut LeanObject = core::ptr::null_mut();
    let mut v_funIndCandidates_3484_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3485_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3486_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3488_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3489_: u8 = 0;
    let mut v___x_3490_: *mut LeanObject = core::ptr::null_mut();
    let mut v_allConsts_3491_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unfoldCandidates_3492_: *mut LeanObject = core::ptr::null_mut();
    let mut v_eqnCandidates_3493_: *mut LeanObject = core::ptr::null_mut();
    let mut v_indCandidates_3494_: *mut LeanObject = core::ptr::null_mut();
    let mut v_libSearchResults_3495_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3497_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3498_: u8 = 0;
    let mut v___x_3500_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3501_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3502_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3504_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3505_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3506_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3507_: u8 = 0;
    let mut v_unused_3508_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3509_: u8 = 0;
    let mut v_a_3510_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3512_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3513_: u8 = 0;
    let mut v___x_3515_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3516_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3517_: u8 = 0;
    let mut v___x_3518_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3520_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3521_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3522_: u8 = 0;
    let mut v_a_3523_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3525_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3526_: u8 = 0;
    let mut v___x_3528_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3529_: *mut LeanObject = core::ptr::null_mut();
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
                v_a_3466_ = lean_ctor_get(v___x_3465_, 0);
                v_isSharedCheck_3531_ = (!lean_is_exclusive(v___x_3465_)) as u8;
                if v_isSharedCheck_3531_ == 0 {
                    v___x_3468_ = v___x_3465_;
                    v_isShared_3469_ = v_isSharedCheck_3531_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_a_3466_);
                    lean_dec(v___x_3465_);
                    v___x_3468_ = lean_box(0);
                    v_isShared_3469_ = v_isSharedCheck_3531_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_3470_ = (lean_unbox(v_a_3466_) as u8);
                if v___x_3470_ == 0 {
                    lean_dec(v_a_3466_);
                    lean_dec(v_declName_3456_);
                    lean_dec_ref(v_e_3455_);
                    v___x_3471_ = lean_box(0);
                    if v_isShared_3469_ == 0 {
                        lean_ctor_set(v___x_3468_, 0, v___x_3471_);
                        v___x_3473_ = v___x_3468_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_3474_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_3474_, 0, v___x_3471_);
                        v___x_3473_ = v_reuseFailAlloc_3474_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_3468_);
                    v___x_3475_ = 0;
                    v___x_3476_ = (lean_unbox(v_a_3466_) as u8);
                    lean_dec(v_a_3466_);
                    v___x_3477_ = l_Lean_Meta_getFunIndInfo_x3f(
                        v___x_3475_,
                        v___x_3476_,
                        v_declName_3456_,
                        v_a_3462_,
                        v_a_3463_,
                    );
                    if lean_obj_tag(v___x_3477_) == 0 {
                        v_a_3478_ = lean_ctor_get(v___x_3477_, 0);
                        v_isSharedCheck_3522_ = (!lean_is_exclusive(v___x_3477_)) as u8;
                        if v_isSharedCheck_3522_ == 0 {
                            v___x_3480_ = v___x_3477_;
                            v_isShared_3481_ = v_isSharedCheck_3522_;
                            state = 3;
                            continue;
                        } else {
                            lean_inc(v_a_3478_);
                            lean_dec(v___x_3477_);
                            v___x_3480_ = lean_box(0);
                            v_isShared_3481_ = v_isSharedCheck_3522_;
                            state = 3;
                            continue;
                        }
                    } else {
                        lean_dec_ref(v_e_3455_);
                        v_a_3523_ = lean_ctor_get(v___x_3477_, 0);
                        v_isSharedCheck_3530_ = (!lean_is_exclusive(v___x_3477_)) as u8;
                        if v_isSharedCheck_3530_ == 0 {
                            v___x_3525_ = v___x_3477_;
                            v_isShared_3526_ = v_isSharedCheck_3530_;
                            state = 11;
                            continue;
                        } else {
                            lean_inc(v_a_3523_);
                            lean_dec(v___x_3477_);
                            v___x_3525_ = lean_box(0);
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
                if lean_obj_tag(v_a_3478_) == 1 {
                    lean_del_object(v___x_3480_);
                    v_val_3482_ = lean_ctor_get(v_a_3478_, 0);
                    lean_inc(v_val_3482_);
                    lean_dec_ref_known(v_a_3478_, 1);
                    v___x_3483_ = lean_st_ref_get(v_a_3459_);
                    v_funIndCandidates_3484_ = lean_ctor_get(v___x_3483_, 3);
                    lean_inc_ref(v_funIndCandidates_3484_);
                    lean_dec(v___x_3483_);
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
                    if lean_obj_tag(v___x_3485_) == 0 {
                        v_a_3486_ = lean_ctor_get(v___x_3485_, 0);
                        v_isSharedCheck_3509_ = (!lean_is_exclusive(v___x_3485_)) as u8;
                        if v_isSharedCheck_3509_ == 0 {
                            v___x_3488_ = v___x_3485_;
                            v_isShared_3489_ = v_isSharedCheck_3509_;
                            state = 4;
                            continue;
                        } else {
                            lean_inc(v_a_3486_);
                            lean_dec(v___x_3485_);
                            v___x_3488_ = lean_box(0);
                            v_isShared_3489_ = v_isSharedCheck_3509_;
                            state = 4;
                            continue;
                        }
                    } else {
                        v_a_3510_ = lean_ctor_get(v___x_3485_, 0);
                        v_isSharedCheck_3517_ = (!lean_is_exclusive(v___x_3485_)) as u8;
                        if v_isSharedCheck_3517_ == 0 {
                            v___x_3512_ = v___x_3485_;
                            v_isShared_3513_ = v_isSharedCheck_3517_;
                            state = 8;
                            continue;
                        } else {
                            lean_inc(v_a_3510_);
                            lean_dec(v___x_3485_);
                            v___x_3512_ = lean_box(0);
                            v_isShared_3513_ = v_isSharedCheck_3517_;
                            state = 8;
                            continue;
                        }
                    }
                } else {
                    lean_dec(v_a_3478_);
                    lean_dec_ref(v_e_3455_);
                    v___x_3518_ = lean_box(0);
                    if v_isShared_3481_ == 0 {
                        lean_ctor_set(v___x_3480_, 0, v___x_3518_);
                        v___x_3520_ = v___x_3480_;
                        state = 10;
                        continue;
                    } else {
                        v_reuseFailAlloc_3521_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_3521_, 0, v___x_3518_);
                        v___x_3520_ = v_reuseFailAlloc_3521_;
                        state = 10;
                        continue;
                    }
                }
            }
            4 => {
                v___x_3490_ = lean_st_ref_take(v_a_3459_);
                v_allConsts_3491_ = lean_ctor_get(v___x_3490_, 0);
                v_unfoldCandidates_3492_ = lean_ctor_get(v___x_3490_, 1);
                v_eqnCandidates_3493_ = lean_ctor_get(v___x_3490_, 2);
                v_indCandidates_3494_ = lean_ctor_get(v___x_3490_, 4);
                v_libSearchResults_3495_ = lean_ctor_get(v___x_3490_, 5);
                v_isSharedCheck_3507_ = (!lean_is_exclusive(v___x_3490_)) as u8;
                if v_isSharedCheck_3507_ == 0 {
                    v_unused_3508_ = lean_ctor_get(v___x_3490_, 3);
                    lean_dec(v_unused_3508_);
                    v___x_3497_ = v___x_3490_;
                    v_isShared_3498_ = v_isSharedCheck_3507_;
                    state = 5;
                    continue;
                } else {
                    lean_inc(v_libSearchResults_3495_);
                    lean_inc(v_indCandidates_3494_);
                    lean_inc(v_eqnCandidates_3493_);
                    lean_inc(v_unfoldCandidates_3492_);
                    lean_inc(v_allConsts_3491_);
                    lean_dec(v___x_3490_);
                    v___x_3497_ = lean_box(0);
                    v_isShared_3498_ = v_isSharedCheck_3507_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                if v_isShared_3498_ == 0 {
                    lean_ctor_set(v___x_3497_, 3, v_a_3486_);
                    v___x_3500_ = v___x_3497_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_3506_ = lean_alloc_ctor(0, 6, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3506_, 0, v_allConsts_3491_);
                    lean_ctor_set(v_reuseFailAlloc_3506_, 1, v_unfoldCandidates_3492_);
                    lean_ctor_set(v_reuseFailAlloc_3506_, 2, v_eqnCandidates_3493_);
                    lean_ctor_set(v_reuseFailAlloc_3506_, 3, v_a_3486_);
                    lean_ctor_set(v_reuseFailAlloc_3506_, 4, v_indCandidates_3494_);
                    lean_ctor_set(v_reuseFailAlloc_3506_, 5, v_libSearchResults_3495_);
                    v___x_3500_ = v_reuseFailAlloc_3506_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                v___x_3501_ = lean_st_ref_set(v_a_3459_, v___x_3500_);
                v___x_3502_ = lean_box(0);
                if v_isShared_3489_ == 0 {
                    lean_ctor_set(v___x_3488_, 0, v___x_3502_);
                    v___x_3504_ = v___x_3488_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_3505_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3505_, 0, v___x_3502_);
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
                    v_reuseFailAlloc_3516_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3516_, 0, v_a_3510_);
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
                    v_reuseFailAlloc_3529_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3529_, 0, v_a_3523_);
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
    mut v_e_3532_: *mut LeanObject,
    mut v_declName_3533_: *mut LeanObject,
    mut v_args_3534_: *mut LeanObject,
    mut v_a_3535_: *mut LeanObject,
    mut v_a_3536_: *mut LeanObject,
    mut v_a_3537_: *mut LeanObject,
    mut v_a_3538_: *mut LeanObject,
    mut v_a_3539_: *mut LeanObject,
    mut v_a_3540_: *mut LeanObject,
    mut v_a_3541_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3542_: *mut LeanObject = core::ptr::null_mut();
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
    lean_dec(v_a_3540_);
    lean_dec_ref(v_a_3539_);
    lean_dec(v_a_3538_);
    lean_dec_ref(v_a_3537_);
    lean_dec(v_a_3536_);
    lean_dec_ref(v_a_3535_);
    lean_dec_ref(v_args_3534_);
    return v_res_3542_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Try_Collector_OrdSet_insert___at___00Lean_Meta_Try_Collector_saveLibSearchCandidates_spec__0_spec__0_spec__1___redArg(
    mut v_a_3543_: *mut LeanObject,
    mut v_x_3544_: *mut LeanObject,
) -> u8 {
    let mut v___x_3545_: u8 = 0;
    let mut v_key_3546_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_3547_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3549_: u8 = 0;
    let mut v_fst_3551_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_3552_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_3553_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_3554_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3555_: u8 = 0;
    let mut v___x_3556_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_3544_) == 0 {
                    v___x_3545_ = 0;
                    return v___x_3545_;
                } else {
                    v_key_3546_ = lean_ctor_get(v_x_3544_, 0);
                    v_tail_3547_ = lean_ctor_get(v_x_3544_, 2);
                    v_fst_3551_ = lean_ctor_get(v_key_3546_, 0);
                    v_snd_3552_ = lean_ctor_get(v_key_3546_, 1);
                    v_fst_3553_ = lean_ctor_get(v_a_3543_, 0);
                    v_snd_3554_ = lean_ctor_get(v_a_3543_, 1);
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
    mut v_a_3557_: *mut LeanObject,
    mut v_x_3558_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3559_: u8 = 0;
    let mut v_r_3560_: *mut LeanObject = core::ptr::null_mut();
    v_res_3559_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Try_Collector_OrdSet_insert___at___00Lean_Meta_Try_Collector_saveLibSearchCandidates_spec__0_spec__0_spec__1___redArg(v_a_3557_, v_x_3558_);
    lean_dec(v_x_3558_);
    lean_dec_ref(v_a_3557_);
    v_r_3560_ = lean_box((v_res_3559_) as usize);
    return v_r_3560_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Try_Collector_OrdSet_insert___at___00Lean_Meta_Try_Collector_saveLibSearchCandidates_spec__0_spec__0___redArg(
    mut v_m_3561_: *mut LeanObject,
    mut v_a_3562_: *mut LeanObject,
) -> u8 {
    let mut v_buckets_3563_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_3564_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_3565_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3566_: *mut LeanObject = core::ptr::null_mut();
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
    let mut v___x_3582_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3583_: u8 = 0;
    let mut v___x_3584_: u64 = 0;
    let mut v_hash_3585_: u64 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_buckets_3563_ = lean_ctor_get(v_m_3561_, 1);
                v_fst_3564_ = lean_ctor_get(v_a_3562_, 0);
                v_snd_3565_ = lean_ctor_get(v_a_3562_, 1);
                v___x_3566_ = lean_array_get_size(v_buckets_3563_);
                if lean_obj_tag(v_fst_3564_) == 0 {
                    v___x_3584_ = lean_uint64_once(core::ptr::addr_of_mut!(l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Try_Collector_OrdSet_insert___at___00Lean_Meta_Try_Collector_saveConst_spec__0_spec__0___redArg___closed__0), core::ptr::addr_of_mut!(l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Try_Collector_OrdSet_insert___at___00Lean_Meta_Try_Collector_saveConst_spec__0_spec__0___redArg___closed__0_once), _init_l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Try_Collector_OrdSet_insert___at___00Lean_Meta_Try_Collector_saveConst_spec__0_spec__0___redArg___closed__0);
                    v___y_3568_ = v___x_3584_;
                    state = 1;
                    continue;
                } else {
                    v_hash_3585_ = lean_ctor_get_uint64(
                        v_fst_3564_,
                        (core::mem::size_of::<*mut LeanObject>() * 2) as u32,
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
    mut v_m_3586_: *mut LeanObject,
    mut v_a_3587_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3588_: u8 = 0;
    let mut v_r_3589_: *mut LeanObject = core::ptr::null_mut();
    v_res_3588_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Try_Collector_OrdSet_insert___at___00Lean_Meta_Try_Collector_saveLibSearchCandidates_spec__0_spec__0___redArg(v_m_3586_, v_a_3587_);
    lean_dec_ref(v_a_3587_);
    lean_dec_ref(v_m_3586_);
    v_r_3589_ = lean_box((v_res_3588_) as usize);
    return v_r_3589_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Try_Collector_OrdSet_insert___at___00Lean_Meta_Try_Collector_saveLibSearchCandidates_spec__0_spec__1_spec__3_spec__5_spec__6___redArg(
    mut v_x_3590_: *mut LeanObject,
    mut v_x_3591_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_key_3592_: *mut LeanObject = core::ptr::null_mut();
    let mut v_value_3593_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_3594_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3596_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3597_: u8 = 0;
    let mut v_fst_3598_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_3599_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3600_: *mut LeanObject = core::ptr::null_mut();
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
    let mut v___x_3616_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3618_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3619_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3621_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3622_: u64 = 0;
    let mut v_hash_3623_: u64 = 0;
    let mut v_isSharedCheck_3624_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_3591_) == 0 {
                    return v_x_3590_;
                } else {
                    v_key_3592_ = lean_ctor_get(v_x_3591_, 0);
                    v_value_3593_ = lean_ctor_get(v_x_3591_, 1);
                    v_tail_3594_ = lean_ctor_get(v_x_3591_, 2);
                    v_isSharedCheck_3624_ = (!lean_is_exclusive(v_x_3591_)) as u8;
                    if v_isSharedCheck_3624_ == 0 {
                        v___x_3596_ = v_x_3591_;
                        v_isShared_3597_ = v_isSharedCheck_3624_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_tail_3594_);
                        lean_inc(v_value_3593_);
                        lean_inc(v_key_3592_);
                        lean_dec(v_x_3591_);
                        v___x_3596_ = lean_box(0);
                        v_isShared_3597_ = v_isSharedCheck_3624_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_fst_3598_ = lean_ctor_get(v_key_3592_, 0);
                v_snd_3599_ = lean_ctor_get(v_key_3592_, 1);
                v___x_3600_ = lean_array_get_size(v_x_3590_);
                if lean_obj_tag(v_fst_3598_) == 0 {
                    v___x_3622_ = lean_uint64_once(core::ptr::addr_of_mut!(l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Try_Collector_OrdSet_insert___at___00Lean_Meta_Try_Collector_saveConst_spec__0_spec__0___redArg___closed__0), core::ptr::addr_of_mut!(l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Try_Collector_OrdSet_insert___at___00Lean_Meta_Try_Collector_saveConst_spec__0_spec__0___redArg___closed__0_once), _init_l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Try_Collector_OrdSet_insert___at___00Lean_Meta_Try_Collector_saveConst_spec__0_spec__0___redArg___closed__0);
                    v___y_3602_ = v___x_3622_;
                    state = 2;
                    continue;
                } else {
                    v_hash_3623_ = lean_ctor_get_uint64(
                        v_fst_3598_,
                        (core::mem::size_of::<*mut LeanObject>() * 2) as u32,
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
                lean_inc(v___x_3616_);
                if v_isShared_3597_ == 0 {
                    lean_ctor_set(v___x_3596_, 2, v___x_3616_);
                    v___x_3618_ = v___x_3596_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_3621_ = lean_alloc_ctor(1, 3, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3621_, 0, v_key_3592_);
                    lean_ctor_set(v_reuseFailAlloc_3621_, 1, v_value_3593_);
                    lean_ctor_set(v_reuseFailAlloc_3621_, 2, v___x_3616_);
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
    mut v_i_3625_: *mut LeanObject,
    mut v_source_3626_: *mut LeanObject,
    mut v_target_3627_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3628_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3629_: u8 = 0;
    let mut v_es_3630_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3631_: *mut LeanObject = core::ptr::null_mut();
    let mut v_source_3632_: *mut LeanObject = core::ptr::null_mut();
    let mut v_target_3633_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3634_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3635_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3628_ = lean_array_get_size(v_source_3626_);
                v___x_3629_ = lean_nat_dec_lt(v_i_3625_, v___x_3628_);
                if v___x_3629_ == 0 {
                    lean_dec_ref(v_source_3626_);
                    lean_dec(v_i_3625_);
                    return v_target_3627_;
                } else {
                    v_es_3630_ = lean_array_fget(v_source_3626_, v_i_3625_);
                    v___x_3631_ = lean_box(0);
                    v_source_3632_ = lean_array_fset(v_source_3626_, v_i_3625_, v___x_3631_);
                    v_target_3633_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Try_Collector_OrdSet_insert___at___00Lean_Meta_Try_Collector_saveLibSearchCandidates_spec__0_spec__1_spec__3_spec__5_spec__6___redArg(v_target_3627_, v_es_3630_);
                    v___x_3634_ = lean_unsigned_to_nat(1);
                    v___x_3635_ = lean_nat_add(v_i_3625_, v___x_3634_);
                    lean_dec(v_i_3625_);
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
    mut v_data_3637_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3638_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3639_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nbuckets_3640_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3641_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3642_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3643_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3644_: *mut LeanObject = core::ptr::null_mut();
    v___x_3638_ = lean_array_get_size(v_data_3637_);
    v___x_3639_ = lean_unsigned_to_nat(2);
    v_nbuckets_3640_ = lean_nat_mul(v___x_3638_, v___x_3639_);
    v___x_3641_ = lean_unsigned_to_nat(0);
    v___x_3642_ = lean_box(0);
    v___x_3643_ = lean_mk_array(v_nbuckets_3640_, v___x_3642_);
    v___x_3644_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Try_Collector_OrdSet_insert___at___00Lean_Meta_Try_Collector_saveLibSearchCandidates_spec__0_spec__1_spec__3_spec__5___redArg(v___x_3641_, v_data_3637_, v___x_3643_);
    return v___x_3644_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Try_Collector_OrdSet_insert___at___00Lean_Meta_Try_Collector_saveLibSearchCandidates_spec__0_spec__1___redArg(
    mut v_m_3645_: *mut LeanObject,
    mut v_a_3646_: *mut LeanObject,
    mut v_b_3647_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_size_3648_: *mut LeanObject = core::ptr::null_mut();
    let mut v_buckets_3649_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_3650_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_3651_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3652_: *mut LeanObject = core::ptr::null_mut();
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
    let mut v_bkt_3668_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3669_: u8 = 0;
    let mut v___x_3671_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3672_: u8 = 0;
    let mut v___x_3673_: *mut LeanObject = core::ptr::null_mut();
    let mut v_size_x27_3674_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3675_: *mut LeanObject = core::ptr::null_mut();
    let mut v_buckets_x27_3676_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3677_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3678_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3679_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3680_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3681_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3682_: u8 = 0;
    let mut v_val_3683_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3685_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3686_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3688_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3689_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3690_: u8 = 0;
    let mut v_unused_3691_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_3692_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3693_: u64 = 0;
    let mut v_hash_3694_: u64 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_size_3648_ = lean_ctor_get(v_m_3645_, 0);
                v_buckets_3649_ = lean_ctor_get(v_m_3645_, 1);
                v_fst_3650_ = lean_ctor_get(v_a_3646_, 0);
                v_snd_3651_ = lean_ctor_get(v_a_3646_, 1);
                v___x_3652_ = lean_array_get_size(v_buckets_3649_);
                if lean_obj_tag(v_fst_3650_) == 0 {
                    v___x_3693_ = lean_uint64_once(core::ptr::addr_of_mut!(l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Try_Collector_OrdSet_insert___at___00Lean_Meta_Try_Collector_saveConst_spec__0_spec__0___redArg___closed__0), core::ptr::addr_of_mut!(l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Try_Collector_OrdSet_insert___at___00Lean_Meta_Try_Collector_saveConst_spec__0_spec__0___redArg___closed__0_once), _init_l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Try_Collector_OrdSet_insert___at___00Lean_Meta_Try_Collector_saveConst_spec__0_spec__0___redArg___closed__0);
                    v___y_3654_ = v___x_3693_;
                    state = 1;
                    continue;
                } else {
                    v_hash_3694_ = lean_ctor_get_uint64(
                        v_fst_3650_,
                        (core::mem::size_of::<*mut LeanObject>() * 2) as u32,
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
                    lean_inc_ref(v_buckets_3649_);
                    lean_inc(v_size_3648_);
                    v_isSharedCheck_3690_ = (!lean_is_exclusive(v_m_3645_)) as u8;
                    if v_isSharedCheck_3690_ == 0 {
                        v_unused_3691_ = lean_ctor_get(v_m_3645_, 1);
                        lean_dec(v_unused_3691_);
                        v_unused_3692_ = lean_ctor_get(v_m_3645_, 0);
                        lean_dec(v_unused_3692_);
                        v___x_3671_ = v_m_3645_;
                        v_isShared_3672_ = v_isSharedCheck_3690_;
                        state = 2;
                        continue;
                    } else {
                        lean_dec(v_m_3645_);
                        v___x_3671_ = lean_box(0);
                        v_isShared_3672_ = v_isSharedCheck_3690_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_dec(v_b_3647_);
                    lean_dec_ref(v_a_3646_);
                    return v_m_3645_;
                }
            }
            2 => {
                v___x_3673_ = lean_unsigned_to_nat(1);
                v_size_x27_3674_ = lean_nat_add(v_size_3648_, v___x_3673_);
                lean_dec(v_size_3648_);
                lean_inc(v_bkt_3668_);
                v___x_3675_ = lean_alloc_ctor(1, 3, (0) as u32);
                lean_ctor_set(v___x_3675_, 0, v_a_3646_);
                lean_ctor_set(v___x_3675_, 1, v_b_3647_);
                lean_ctor_set(v___x_3675_, 2, v_bkt_3668_);
                v_buckets_x27_3676_ = lean_array_uset(v_buckets_3649_, v___x_3667_, v___x_3675_);
                v___x_3677_ = lean_unsigned_to_nat(4);
                v___x_3678_ = lean_nat_mul(v_size_x27_3674_, v___x_3677_);
                v___x_3679_ = lean_unsigned_to_nat(3);
                v___x_3680_ = lean_nat_div(v___x_3678_, v___x_3679_);
                lean_dec(v___x_3678_);
                v___x_3681_ = lean_array_get_size(v_buckets_x27_3676_);
                v___x_3682_ = lean_nat_dec_le(v___x_3680_, v___x_3681_);
                lean_dec(v___x_3680_);
                if v___x_3682_ == 0 {
                    v_val_3683_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Try_Collector_OrdSet_insert___at___00Lean_Meta_Try_Collector_saveLibSearchCandidates_spec__0_spec__1_spec__3___redArg(v_buckets_x27_3676_);
                    if v_isShared_3672_ == 0 {
                        lean_ctor_set(v___x_3671_, 1, v_val_3683_);
                        lean_ctor_set(v___x_3671_, 0, v_size_x27_3674_);
                        v___x_3685_ = v___x_3671_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_3686_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_3686_, 0, v_size_x27_3674_);
                        lean_ctor_set(v_reuseFailAlloc_3686_, 1, v_val_3683_);
                        v___x_3685_ = v_reuseFailAlloc_3686_;
                        state = 3;
                        continue;
                    }
                } else {
                    if v_isShared_3672_ == 0 {
                        lean_ctor_set(v___x_3671_, 1, v_buckets_x27_3676_);
                        lean_ctor_set(v___x_3671_, 0, v_size_x27_3674_);
                        v___x_3688_ = v___x_3671_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_3689_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_3689_, 0, v_size_x27_3674_);
                        lean_ctor_set(v_reuseFailAlloc_3689_, 1, v_buckets_x27_3676_);
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
    mut v_s_3695_: *mut LeanObject,
    mut v_a_3696_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_elems_3697_: *mut LeanObject = core::ptr::null_mut();
    let mut v_set_3698_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3699_: u8 = 0;
    let mut v___x_3701_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3702_: u8 = 0;
    let mut v___x_3703_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3704_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3705_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3707_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3708_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3709_: u8 = 0;
    let mut v_unused_3710_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_3711_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_elems_3697_ = lean_ctor_get(v_s_3695_, 0);
                v_set_3698_ = lean_ctor_get(v_s_3695_, 1);
                v___x_3699_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Try_Collector_OrdSet_insert___at___00Lean_Meta_Try_Collector_saveLibSearchCandidates_spec__0_spec__0___redArg(v_set_3698_, v_a_3696_);
                if v___x_3699_ == 0 {
                    lean_inc_ref(v_set_3698_);
                    lean_inc_ref(v_elems_3697_);
                    v_isSharedCheck_3709_ = (!lean_is_exclusive(v_s_3695_)) as u8;
                    if v_isSharedCheck_3709_ == 0 {
                        v_unused_3710_ = lean_ctor_get(v_s_3695_, 1);
                        lean_dec(v_unused_3710_);
                        v_unused_3711_ = lean_ctor_get(v_s_3695_, 0);
                        lean_dec(v_unused_3711_);
                        v___x_3701_ = v_s_3695_;
                        v_isShared_3702_ = v_isSharedCheck_3709_;
                        state = 1;
                        continue;
                    } else {
                        lean_dec(v_s_3695_);
                        v___x_3701_ = lean_box(0);
                        v_isShared_3702_ = v_isSharedCheck_3709_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec_ref(v_a_3696_);
                    return v_s_3695_;
                }
            }
            1 => {
                lean_inc_ref(v_a_3696_);
                v___x_3703_ = lean_array_push(v_elems_3697_, v_a_3696_);
                v___x_3704_ = lean_box(0);
                v___x_3705_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Try_Collector_OrdSet_insert___at___00Lean_Meta_Try_Collector_saveLibSearchCandidates_spec__0_spec__1___redArg(v_set_3698_, v_a_3696_, v___x_3704_);
                if v_isShared_3702_ == 0 {
                    lean_ctor_set(v___x_3701_, 1, v___x_3705_);
                    lean_ctor_set(v___x_3701_, 0, v___x_3703_);
                    v___x_3707_ = v___x_3701_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3708_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3708_, 0, v___x_3703_);
                    lean_ctor_set(v_reuseFailAlloc_3708_, 1, v___x_3705_);
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
    mut v_as_3712_: *mut LeanObject,
    mut v_sz_3713_: usize,
    mut v_i_3714_: usize,
    mut v_b_3715_: *mut LeanObject,
    mut v___y_3716_: *mut LeanObject,
    mut v___y_3717_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_3720_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3721_: usize = 0;
    let mut v___x_3722_: usize = 0;
    let mut v___x_3724_: u8 = 0;
    let mut v___x_3725_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3726_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_3727_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_3728_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3730_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3731_: u8 = 0;
    let mut v___x_3732_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3733_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3734_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3735_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3737_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3738_: *mut LeanObject = core::ptr::null_mut();
    let mut v_allConsts_3739_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unfoldCandidates_3740_: *mut LeanObject = core::ptr::null_mut();
    let mut v_eqnCandidates_3741_: *mut LeanObject = core::ptr::null_mut();
    let mut v_funIndCandidates_3742_: *mut LeanObject = core::ptr::null_mut();
    let mut v_indCandidates_3743_: *mut LeanObject = core::ptr::null_mut();
    let mut v_libSearchResults_3744_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3746_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3747_: u8 = 0;
    let mut v___x_3749_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3750_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3752_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3753_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3754_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3755_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3756_: u8 = 0;
    let mut v___x_3757_: u8 = 0;
    let mut v___x_3758_: u8 = 0;
    let mut v___x_3759_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3760_: u8 = 0;
    let mut v___x_3761_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3762_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3763_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3765_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3766_: u8 = 0;
    let mut v___x_3768_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3769_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3770_: u8 = 0;
    let mut v_isSharedCheck_3771_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3724_ = lean_usize_dec_lt(v_i_3714_, v_sz_3713_);
                if v___x_3724_ == 0 {
                    v___x_3725_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_3725_, 0, v_b_3715_);
                    return v___x_3725_;
                } else {
                    v_a_3726_ = lean_array_uget(v_as_3712_, v_i_3714_);
                    v_fst_3727_ = lean_ctor_get(v_a_3726_, 0);
                    v_snd_3728_ = lean_ctor_get(v_a_3726_, 1);
                    v_isSharedCheck_3771_ = (!lean_is_exclusive(v_a_3726_)) as u8;
                    if v_isSharedCheck_3771_ == 0 {
                        v___x_3730_ = v_a_3726_;
                        v_isShared_3731_ = v_isSharedCheck_3771_;
                        state = 2;
                        continue;
                    } else {
                        lean_inc(v_snd_3728_);
                        lean_inc(v_fst_3727_);
                        lean_dec(v_a_3726_);
                        v___x_3730_ = lean_box(0);
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
                lean_inc(v_fst_3727_);
                v___x_3733_ = l_Lean_Meta_Grind_Extension_isEMatchTheorem___redArg(
                    v___x_3732_,
                    v_fst_3727_,
                    v___y_3717_,
                );
                if lean_obj_tag(v___x_3733_) == 0 {
                    v_a_3734_ = lean_ctor_get(v___x_3733_, 0);
                    lean_inc(v_a_3734_);
                    lean_dec_ref_known(v___x_3733_, 1);
                    v___x_3735_ = lean_box(0);
                    v___x_3757_ = (lean_unbox(v_a_3734_) as u8);
                    if v___x_3757_ == 0 {
                        v___x_3758_ = (lean_unbox(v_snd_3728_) as u8);
                        lean_dec(v_snd_3728_);
                        match v___x_3758_ {
                            0 => {
                                v___x_3759_ = lean_alloc_ctor(8, 0, (1) as u32);
                                v___x_3760_ = (lean_unbox(v_a_3734_) as u8);
                                lean_dec(v_a_3734_);
                                lean_ctor_set_uint8(v___x_3759_, 0 as u32, v___x_3760_);
                                v___y_3737_ = v___x_3759_;
                                state = 3;
                                continue;
                            }
                            1 => {
                                lean_dec(v_a_3734_);
                                v___x_3761_ = lean_box(6);
                                v___y_3737_ = v___x_3761_;
                                state = 3;
                                continue;
                            }
                            _ => {
                                lean_dec(v_a_3734_);
                                v___x_3762_ = lean_box(7);
                                v___y_3737_ = v___x_3762_;
                                state = 3;
                                continue;
                            }
                        }
                    } else {
                        lean_dec(v_a_3734_);
                        lean_del_object(v___x_3730_);
                        lean_dec(v_snd_3728_);
                        lean_dec(v_fst_3727_);
                        v_a_3720_ = v___x_3735_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_3730_);
                    lean_dec(v_snd_3728_);
                    lean_dec(v_fst_3727_);
                    v_a_3763_ = lean_ctor_get(v___x_3733_, 0);
                    v_isSharedCheck_3770_ = (!lean_is_exclusive(v___x_3733_)) as u8;
                    if v_isSharedCheck_3770_ == 0 {
                        v___x_3765_ = v___x_3733_;
                        v_isShared_3766_ = v_isSharedCheck_3770_;
                        state = 7;
                        continue;
                    } else {
                        lean_inc(v_a_3763_);
                        lean_dec(v___x_3733_);
                        v___x_3765_ = lean_box(0);
                        v_isShared_3766_ = v_isSharedCheck_3770_;
                        state = 7;
                        continue;
                    }
                }
            }
            3 => {
                v___x_3738_ = lean_st_ref_take(v___y_3716_);
                v_allConsts_3739_ = lean_ctor_get(v___x_3738_, 0);
                v_unfoldCandidates_3740_ = lean_ctor_get(v___x_3738_, 1);
                v_eqnCandidates_3741_ = lean_ctor_get(v___x_3738_, 2);
                v_funIndCandidates_3742_ = lean_ctor_get(v___x_3738_, 3);
                v_indCandidates_3743_ = lean_ctor_get(v___x_3738_, 4);
                v_libSearchResults_3744_ = lean_ctor_get(v___x_3738_, 5);
                v_isSharedCheck_3756_ = (!lean_is_exclusive(v___x_3738_)) as u8;
                if v_isSharedCheck_3756_ == 0 {
                    v___x_3746_ = v___x_3738_;
                    v_isShared_3747_ = v_isSharedCheck_3756_;
                    state = 4;
                    continue;
                } else {
                    lean_inc(v_libSearchResults_3744_);
                    lean_inc(v_indCandidates_3743_);
                    lean_inc(v_funIndCandidates_3742_);
                    lean_inc(v_eqnCandidates_3741_);
                    lean_inc(v_unfoldCandidates_3740_);
                    lean_inc(v_allConsts_3739_);
                    lean_dec(v___x_3738_);
                    v___x_3746_ = lean_box(0);
                    v_isShared_3747_ = v_isSharedCheck_3756_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                if v_isShared_3731_ == 0 {
                    lean_ctor_set(v___x_3730_, 1, v___y_3737_);
                    v___x_3749_ = v___x_3730_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_3755_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3755_, 0, v_fst_3727_);
                    lean_ctor_set(v_reuseFailAlloc_3755_, 1, v___y_3737_);
                    v___x_3749_ = v_reuseFailAlloc_3755_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v___x_3750_ = l_Lean_Meta_Try_Collector_OrdSet_insert___at___00Lean_Meta_Try_Collector_saveLibSearchCandidates_spec__0(v_libSearchResults_3744_, v___x_3749_);
                if v_isShared_3747_ == 0 {
                    lean_ctor_set(v___x_3746_, 5, v___x_3750_);
                    v___x_3752_ = v___x_3746_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_3754_ = lean_alloc_ctor(0, 6, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3754_, 0, v_allConsts_3739_);
                    lean_ctor_set(v_reuseFailAlloc_3754_, 1, v_unfoldCandidates_3740_);
                    lean_ctor_set(v_reuseFailAlloc_3754_, 2, v_eqnCandidates_3741_);
                    lean_ctor_set(v_reuseFailAlloc_3754_, 3, v_funIndCandidates_3742_);
                    lean_ctor_set(v_reuseFailAlloc_3754_, 4, v_indCandidates_3743_);
                    lean_ctor_set(v_reuseFailAlloc_3754_, 5, v___x_3750_);
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
                    v_reuseFailAlloc_3769_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3769_, 0, v_a_3763_);
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
    mut v_as_3772_: *mut LeanObject,
    mut v_sz_3773_: *mut LeanObject,
    mut v_i_3774_: *mut LeanObject,
    mut v_b_3775_: *mut LeanObject,
    mut v___y_3776_: *mut LeanObject,
    mut v___y_3777_: *mut LeanObject,
    mut v___y_3778_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_boxed_3779_: usize = 0;
    let mut v_i_boxed_3780_: usize = 0;
    let mut v_res_3781_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_3779_ = lean_unbox_usize(v_sz_3773_);
    lean_dec(v_sz_3773_);
    v_i_boxed_3780_ = lean_unbox_usize(v_i_3774_);
    lean_dec(v_i_3774_);
    v_res_3781_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Try_Collector_saveLibSearchCandidates_spec__1___redArg(v_as_3772_, v_sz_boxed_3779_, v_i_boxed_3780_, v_b_3775_, v___y_3776_, v___y_3777_);
    lean_dec(v___y_3777_);
    lean_dec(v___y_3776_);
    lean_dec_ref(v_as_3772_);
    return v_res_3781_;
}
pub unsafe fn l_Lean_Meta_Try_Collector_saveLibSearchCandidates(
    mut v_e_3782_: *mut LeanObject,
    mut v_a_3783_: *mut LeanObject,
    mut v_a_3784_: *mut LeanObject,
    mut v_a_3785_: *mut LeanObject,
    mut v_a_3786_: *mut LeanObject,
    mut v_a_3787_: *mut LeanObject,
    mut v_a_3788_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_harder_3790_: u8 = 0;
    let mut v___x_3791_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3792_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3793_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3794_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3795_: *mut LeanObject = core::ptr::null_mut();
    let mut v_sz_3796_: usize = 0;
    let mut v___x_3797_: usize = 0;
    let mut v___x_3798_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3800_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3801_: u8 = 0;
    let mut v___x_3803_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3804_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3805_: u8 = 0;
    let mut v_unused_3806_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3807_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3809_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3810_: u8 = 0;
    let mut v___x_3812_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3813_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3814_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_harder_3790_ = lean_ctor_get_uint8(
                    v_a_3783_,
                    (core::mem::size_of::<*mut LeanObject>() * 1 + 5) as u32,
                );
                if v_harder_3790_ == 0 {
                    lean_dec_ref(v_e_3782_);
                    v___x_3791_ = lean_box(0);
                    v___x_3792_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_3792_, 0, v___x_3791_);
                    return v___x_3792_;
                } else {
                    v___x_3793_ = l_Lean_Meta_LibrarySearch_libSearchFindDecls(
                        v_e_3782_, v_a_3785_, v_a_3786_, v_a_3787_, v_a_3788_,
                    );
                    if lean_obj_tag(v___x_3793_) == 0 {
                        v_a_3794_ = lean_ctor_get(v___x_3793_, 0);
                        lean_inc(v_a_3794_);
                        lean_dec_ref_known(v___x_3793_, 1);
                        v___x_3795_ = lean_box(0);
                        v_sz_3796_ = lean_array_size(v_a_3794_);
                        v___x_3797_ = 0usize;
                        v___x_3798_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Try_Collector_saveLibSearchCandidates_spec__1___redArg(v_a_3794_, v_sz_3796_, v___x_3797_, v___x_3795_, v_a_3784_, v_a_3788_);
                        lean_dec(v_a_3794_);
                        if lean_obj_tag(v___x_3798_) == 0 {
                            v_isSharedCheck_3805_ = (!lean_is_exclusive(v___x_3798_)) as u8;
                            if v_isSharedCheck_3805_ == 0 {
                                v_unused_3806_ = lean_ctor_get(v___x_3798_, 0);
                                lean_dec(v_unused_3806_);
                                v___x_3800_ = v___x_3798_;
                                v_isShared_3801_ = v_isSharedCheck_3805_;
                                state = 1;
                                continue;
                            } else {
                                lean_dec(v___x_3798_);
                                v___x_3800_ = lean_box(0);
                                v_isShared_3801_ = v_isSharedCheck_3805_;
                                state = 1;
                                continue;
                            }
                        } else {
                            return v___x_3798_;
                        }
                    } else {
                        v_a_3807_ = lean_ctor_get(v___x_3793_, 0);
                        v_isSharedCheck_3814_ = (!lean_is_exclusive(v___x_3793_)) as u8;
                        if v_isSharedCheck_3814_ == 0 {
                            v___x_3809_ = v___x_3793_;
                            v_isShared_3810_ = v_isSharedCheck_3814_;
                            state = 3;
                            continue;
                        } else {
                            lean_inc(v_a_3807_);
                            lean_dec(v___x_3793_);
                            v___x_3809_ = lean_box(0);
                            v_isShared_3810_ = v_isSharedCheck_3814_;
                            state = 3;
                            continue;
                        }
                    }
                }
            }
            1 => {
                if v_isShared_3801_ == 0 {
                    lean_ctor_set(v___x_3800_, 0, v___x_3795_);
                    v___x_3803_ = v___x_3800_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3804_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3804_, 0, v___x_3795_);
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
                    v_reuseFailAlloc_3813_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3813_, 0, v_a_3807_);
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
    mut v_e_3815_: *mut LeanObject,
    mut v_a_3816_: *mut LeanObject,
    mut v_a_3817_: *mut LeanObject,
    mut v_a_3818_: *mut LeanObject,
    mut v_a_3819_: *mut LeanObject,
    mut v_a_3820_: *mut LeanObject,
    mut v_a_3821_: *mut LeanObject,
    mut v_a_3822_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3823_: *mut LeanObject = core::ptr::null_mut();
    v_res_3823_ = l_Lean_Meta_Try_Collector_saveLibSearchCandidates(
        v_e_3815_, v_a_3816_, v_a_3817_, v_a_3818_, v_a_3819_, v_a_3820_, v_a_3821_,
    );
    lean_dec(v_a_3821_);
    lean_dec_ref(v_a_3820_);
    lean_dec(v_a_3819_);
    lean_dec_ref(v_a_3818_);
    lean_dec(v_a_3817_);
    lean_dec_ref(v_a_3816_);
    return v_res_3823_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Try_Collector_saveLibSearchCandidates_spec__1(
    mut v_as_3824_: *mut LeanObject,
    mut v_sz_3825_: usize,
    mut v_i_3826_: usize,
    mut v_b_3827_: *mut LeanObject,
    mut v___y_3828_: *mut LeanObject,
    mut v___y_3829_: *mut LeanObject,
    mut v___y_3830_: *mut LeanObject,
    mut v___y_3831_: *mut LeanObject,
    mut v___y_3832_: *mut LeanObject,
    mut v___y_3833_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3835_: *mut LeanObject = core::ptr::null_mut();
    v___x_3835_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Try_Collector_saveLibSearchCandidates_spec__1___redArg(v_as_3824_, v_sz_3825_, v_i_3826_, v_b_3827_, v___y_3829_, v___y_3833_);
    return v___x_3835_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Try_Collector_saveLibSearchCandidates_spec__1___boxed(
    mut v_as_3836_: *mut LeanObject,
    mut v_sz_3837_: *mut LeanObject,
    mut v_i_3838_: *mut LeanObject,
    mut v_b_3839_: *mut LeanObject,
    mut v___y_3840_: *mut LeanObject,
    mut v___y_3841_: *mut LeanObject,
    mut v___y_3842_: *mut LeanObject,
    mut v___y_3843_: *mut LeanObject,
    mut v___y_3844_: *mut LeanObject,
    mut v___y_3845_: *mut LeanObject,
    mut v___y_3846_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_boxed_3847_: usize = 0;
    let mut v_i_boxed_3848_: usize = 0;
    let mut v_res_3849_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_3847_ = lean_unbox_usize(v_sz_3837_);
    lean_dec(v_sz_3837_);
    v_i_boxed_3848_ = lean_unbox_usize(v_i_3838_);
    lean_dec(v_i_3838_);
    v_res_3849_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Try_Collector_saveLibSearchCandidates_spec__1(v_as_3836_, v_sz_boxed_3847_, v_i_boxed_3848_, v_b_3839_, v___y_3840_, v___y_3841_, v___y_3842_, v___y_3843_, v___y_3844_, v___y_3845_);
    lean_dec(v___y_3845_);
    lean_dec_ref(v___y_3844_);
    lean_dec(v___y_3843_);
    lean_dec_ref(v___y_3842_);
    lean_dec(v___y_3841_);
    lean_dec_ref(v___y_3840_);
    lean_dec_ref(v_as_3836_);
    return v_res_3849_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Try_Collector_OrdSet_insert___at___00Lean_Meta_Try_Collector_saveLibSearchCandidates_spec__0_spec__0(
    mut v_00_u03b2_3850_: *mut LeanObject,
    mut v_m_3851_: *mut LeanObject,
    mut v_a_3852_: *mut LeanObject,
) -> u8 {
    let mut v___x_3853_: u8 = 0;
    v___x_3853_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Try_Collector_OrdSet_insert___at___00Lean_Meta_Try_Collector_saveLibSearchCandidates_spec__0_spec__0___redArg(v_m_3851_, v_a_3852_);
    return v___x_3853_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Try_Collector_OrdSet_insert___at___00Lean_Meta_Try_Collector_saveLibSearchCandidates_spec__0_spec__0___boxed(
    mut v_00_u03b2_3854_: *mut LeanObject,
    mut v_m_3855_: *mut LeanObject,
    mut v_a_3856_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3857_: u8 = 0;
    let mut v_r_3858_: *mut LeanObject = core::ptr::null_mut();
    v_res_3857_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Try_Collector_OrdSet_insert___at___00Lean_Meta_Try_Collector_saveLibSearchCandidates_spec__0_spec__0(v_00_u03b2_3854_, v_m_3855_, v_a_3856_);
    lean_dec_ref(v_a_3856_);
    lean_dec_ref(v_m_3855_);
    v_r_3858_ = lean_box((v_res_3857_) as usize);
    return v_r_3858_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Try_Collector_OrdSet_insert___at___00Lean_Meta_Try_Collector_saveLibSearchCandidates_spec__0_spec__1(
    mut v_00_u03b2_3859_: *mut LeanObject,
    mut v_m_3860_: *mut LeanObject,
    mut v_a_3861_: *mut LeanObject,
    mut v_b_3862_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3863_: *mut LeanObject = core::ptr::null_mut();
    v___x_3863_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Try_Collector_OrdSet_insert___at___00Lean_Meta_Try_Collector_saveLibSearchCandidates_spec__0_spec__1___redArg(v_m_3860_, v_a_3861_, v_b_3862_);
    return v___x_3863_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Try_Collector_OrdSet_insert___at___00Lean_Meta_Try_Collector_saveLibSearchCandidates_spec__0_spec__0_spec__1(
    mut v_00_u03b2_3864_: *mut LeanObject,
    mut v_a_3865_: *mut LeanObject,
    mut v_x_3866_: *mut LeanObject,
) -> u8 {
    let mut v___x_3867_: u8 = 0;
    v___x_3867_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Try_Collector_OrdSet_insert___at___00Lean_Meta_Try_Collector_saveLibSearchCandidates_spec__0_spec__0_spec__1___redArg(v_a_3865_, v_x_3866_);
    return v___x_3867_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Try_Collector_OrdSet_insert___at___00Lean_Meta_Try_Collector_saveLibSearchCandidates_spec__0_spec__0_spec__1___boxed(
    mut v_00_u03b2_3868_: *mut LeanObject,
    mut v_a_3869_: *mut LeanObject,
    mut v_x_3870_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3871_: u8 = 0;
    let mut v_r_3872_: *mut LeanObject = core::ptr::null_mut();
    v_res_3871_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Try_Collector_OrdSet_insert___at___00Lean_Meta_Try_Collector_saveLibSearchCandidates_spec__0_spec__0_spec__1(v_00_u03b2_3868_, v_a_3869_, v_x_3870_);
    lean_dec(v_x_3870_);
    lean_dec_ref(v_a_3869_);
    v_r_3872_ = lean_box((v_res_3871_) as usize);
    return v_r_3872_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Try_Collector_OrdSet_insert___at___00Lean_Meta_Try_Collector_saveLibSearchCandidates_spec__0_spec__1_spec__3(
    mut v_00_u03b2_3873_: *mut LeanObject,
    mut v_data_3874_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3875_: *mut LeanObject = core::ptr::null_mut();
    v___x_3875_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Try_Collector_OrdSet_insert___at___00Lean_Meta_Try_Collector_saveLibSearchCandidates_spec__0_spec__1_spec__3___redArg(v_data_3874_);
    return v___x_3875_;
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Try_Collector_OrdSet_insert___at___00Lean_Meta_Try_Collector_saveLibSearchCandidates_spec__0_spec__1_spec__3_spec__5(
    mut v_00_u03b2_3876_: *mut LeanObject,
    mut v_i_3877_: *mut LeanObject,
    mut v_source_3878_: *mut LeanObject,
    mut v_target_3879_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3880_: *mut LeanObject = core::ptr::null_mut();
    v___x_3880_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Try_Collector_OrdSet_insert___at___00Lean_Meta_Try_Collector_saveLibSearchCandidates_spec__0_spec__1_spec__3_spec__5___redArg(v_i_3877_, v_source_3878_, v_target_3879_);
    return v___x_3880_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Try_Collector_OrdSet_insert___at___00Lean_Meta_Try_Collector_saveLibSearchCandidates_spec__0_spec__1_spec__3_spec__5_spec__6(
    mut v_00_u03b2_3881_: *mut LeanObject,
    mut v_x_3882_: *mut LeanObject,
    mut v_x_3883_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3884_: *mut LeanObject = core::ptr::null_mut();
    v___x_3884_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Try_Collector_OrdSet_insert___at___00Lean_Meta_Try_Collector_saveLibSearchCandidates_spec__0_spec__1_spec__3_spec__5_spec__6___redArg(v_x_3882_, v_x_3883_);
    return v___x_3884_;
}
pub unsafe fn l_Lean_Meta_Try_Collector_visitApp(
    mut v_e_3885_: *mut LeanObject,
    mut v_declName_3886_: *mut LeanObject,
    mut v_args_3887_: *mut LeanObject,
    mut v_a_3888_: *mut LeanObject,
    mut v_a_3889_: *mut LeanObject,
    mut v_a_3890_: *mut LeanObject,
    mut v_a_3891_: *mut LeanObject,
    mut v_a_3892_: *mut LeanObject,
    mut v_a_3893_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3895_: *mut LeanObject = core::ptr::null_mut();
    lean_inc(v_declName_3886_);
    v___x_3895_ = l_Lean_Meta_Try_Collector_saveEqnCandidate(
        v_declName_3886_,
        v_a_3888_,
        v_a_3889_,
        v_a_3890_,
        v_a_3891_,
        v_a_3892_,
        v_a_3893_,
    );
    if lean_obj_tag(v___x_3895_) == 0 {
        let mut v___x_3896_: *mut LeanObject = core::ptr::null_mut();
        lean_dec_ref_known(v___x_3895_, 1);
        lean_inc(v_declName_3886_);
        lean_inc_ref(v_e_3885_);
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
        if lean_obj_tag(v___x_3896_) == 0 {
            let mut v___x_3897_: *mut LeanObject = core::ptr::null_mut();
            lean_dec_ref_known(v___x_3896_, 1);
            v___x_3897_ = l_Lean_Meta_Try_Collector_saveUnfoldCandidate___redArg(
                v_declName_3886_,
                v_a_3888_,
                v_a_3889_,
                v_a_3892_,
                v_a_3893_,
            );
            if lean_obj_tag(v___x_3897_) == 0 {
                let mut v___x_3898_: *mut LeanObject = core::ptr::null_mut();
                lean_dec_ref_known(v___x_3897_, 1);
                v___x_3898_ = l_Lean_Meta_Try_Collector_saveLibSearchCandidates(
                    v_e_3885_, v_a_3888_, v_a_3889_, v_a_3890_, v_a_3891_, v_a_3892_, v_a_3893_,
                );
                return v___x_3898_;
            } else {
                lean_dec_ref(v_e_3885_);
                return v___x_3897_;
            }
        } else {
            lean_dec(v_declName_3886_);
            lean_dec_ref(v_e_3885_);
            return v___x_3896_;
        }
    } else {
        lean_dec(v_declName_3886_);
        lean_dec_ref(v_e_3885_);
        return v___x_3895_;
    }
}
pub unsafe fn l_Lean_Meta_Try_Collector_visitApp___boxed(
    mut v_e_3899_: *mut LeanObject,
    mut v_declName_3900_: *mut LeanObject,
    mut v_args_3901_: *mut LeanObject,
    mut v_a_3902_: *mut LeanObject,
    mut v_a_3903_: *mut LeanObject,
    mut v_a_3904_: *mut LeanObject,
    mut v_a_3905_: *mut LeanObject,
    mut v_a_3906_: *mut LeanObject,
    mut v_a_3907_: *mut LeanObject,
    mut v_a_3908_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3909_: *mut LeanObject = core::ptr::null_mut();
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
    lean_dec(v_a_3907_);
    lean_dec_ref(v_a_3906_);
    lean_dec(v_a_3905_);
    lean_dec_ref(v_a_3904_);
    lean_dec(v_a_3903_);
    lean_dec_ref(v_a_3902_);
    lean_dec_ref(v_args_3901_);
    return v_res_3909_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Try_Collector_checkInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__0()
-> *mut LeanObject {
    let mut v___x_3910_: *mut LeanObject = core::ptr::null_mut();
    v___x_3910_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
    return v___x_3910_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Try_Collector_checkInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__1()
-> *mut LeanObject {
    let mut v___x_3911_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3912_: *mut LeanObject = core::ptr::null_mut();
    v___x_3911_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Try_Collector_checkInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Try_Collector_checkInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__0_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Try_Collector_checkInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__0);
    v___x_3912_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_3912_, 0, v___x_3911_);
    return v___x_3912_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Try_Collector_checkInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__2()
-> *mut LeanObject {
    let mut v___x_3913_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3914_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3915_: *mut LeanObject = core::ptr::null_mut();
    v___x_3913_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Try_Collector_checkInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Try_Collector_checkInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__1_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Try_Collector_checkInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__1);
    v___x_3914_ = lean_unsigned_to_nat(0);
    v___x_3915_ = lean_alloc_ctor(0, 10, (0) as u32);
    lean_ctor_set(v___x_3915_, 0, v___x_3914_);
    lean_ctor_set(v___x_3915_, 1, v___x_3914_);
    lean_ctor_set(v___x_3915_, 2, v___x_3914_);
    lean_ctor_set(v___x_3915_, 3, v___x_3914_);
    lean_ctor_set(v___x_3915_, 4, v___x_3913_);
    lean_ctor_set(v___x_3915_, 5, v___x_3913_);
    lean_ctor_set(v___x_3915_, 6, v___x_3913_);
    lean_ctor_set(v___x_3915_, 7, v___x_3913_);
    lean_ctor_set(v___x_3915_, 8, v___x_3913_);
    lean_ctor_set(v___x_3915_, 9, v___x_3913_);
    return v___x_3915_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Try_Collector_checkInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__3()
-> *mut LeanObject {
    let mut v___x_3916_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3917_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3918_: *mut LeanObject = core::ptr::null_mut();
    v___x_3916_ = lean_unsigned_to_nat(32);
    v___x_3917_ = lean_mk_empty_array_with_capacity(v___x_3916_);
    v___x_3918_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_3918_, 0, v___x_3917_);
    return v___x_3918_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Try_Collector_checkInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__4()
-> *mut LeanObject {
    let mut v___x_3919_: usize = 0;
    let mut v___x_3920_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3921_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3922_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3923_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3924_: *mut LeanObject = core::ptr::null_mut();
    v___x_3919_ = 5usize;
    v___x_3920_ = lean_unsigned_to_nat(0);
    v___x_3921_ = lean_unsigned_to_nat(32);
    v___x_3922_ = lean_mk_empty_array_with_capacity(v___x_3921_);
    v___x_3923_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Try_Collector_checkInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__3), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Try_Collector_checkInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__3_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Try_Collector_checkInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__3);
    v___x_3924_ = lean_alloc_ctor(0, 4, (core::mem::size_of::<usize>() * 1) as u32);
    lean_ctor_set(v___x_3924_, 0, v___x_3923_);
    lean_ctor_set(v___x_3924_, 1, v___x_3922_);
    lean_ctor_set(v___x_3924_, 2, v___x_3920_);
    lean_ctor_set(v___x_3924_, 3, v___x_3920_);
    lean_ctor_set_usize(v___x_3924_, 4, v___x_3919_);
    return v___x_3924_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Try_Collector_checkInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__5()
-> *mut LeanObject {
    let mut v___x_3925_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3926_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3927_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3928_: *mut LeanObject = core::ptr::null_mut();
    v___x_3925_ = lean_box(1);
    v___x_3926_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Try_Collector_checkInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__4), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Try_Collector_checkInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__4_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Try_Collector_checkInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__4);
    v___x_3927_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Try_Collector_checkInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Try_Collector_checkInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__1_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Try_Collector_checkInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__1);
    v___x_3928_ = lean_alloc_ctor(0, 3, (0) as u32);
    lean_ctor_set(v___x_3928_, 0, v___x_3927_);
    lean_ctor_set(v___x_3928_, 1, v___x_3926_);
    lean_ctor_set(v___x_3928_, 2, v___x_3925_);
    return v___x_3928_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Try_Collector_checkInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__7()
-> *mut LeanObject {
    let mut v___x_3930_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3931_: *mut LeanObject = core::ptr::null_mut();
    v___x_3930_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Try_Collector_checkInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__6;
    v___x_3931_ = l_Lean_stringToMessageData(v___x_3930_);
    return v___x_3931_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Try_Collector_checkInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__9()
-> *mut LeanObject {
    let mut v___x_3933_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3934_: *mut LeanObject = core::ptr::null_mut();
    v___x_3933_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Try_Collector_checkInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__8;
    v___x_3934_ = l_Lean_stringToMessageData(v___x_3933_);
    return v___x_3934_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Try_Collector_checkInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__11()
-> *mut LeanObject {
    let mut v___x_3936_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3937_: *mut LeanObject = core::ptr::null_mut();
    v___x_3936_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Try_Collector_checkInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__10;
    v___x_3937_ = l_Lean_stringToMessageData(v___x_3936_);
    return v___x_3937_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Try_Collector_checkInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__13()
-> *mut LeanObject {
    let mut v___x_3939_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3940_: *mut LeanObject = core::ptr::null_mut();
    v___x_3939_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Try_Collector_checkInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__12;
    v___x_3940_ = l_Lean_stringToMessageData(v___x_3939_);
    return v___x_3940_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Try_Collector_checkInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__15()
-> *mut LeanObject {
    let mut v___x_3942_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3943_: *mut LeanObject = core::ptr::null_mut();
    v___x_3942_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Try_Collector_checkInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__14;
    v___x_3943_ = l_Lean_stringToMessageData(v___x_3942_);
    return v___x_3943_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Try_Collector_checkInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__17()
-> *mut LeanObject {
    let mut v___x_3945_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3946_: *mut LeanObject = core::ptr::null_mut();
    v___x_3945_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Try_Collector_checkInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__16;
    v___x_3946_ = l_Lean_stringToMessageData(v___x_3945_);
    return v___x_3946_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Try_Collector_checkInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__19()
-> *mut LeanObject {
    let mut v___x_3948_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3949_: *mut LeanObject = core::ptr::null_mut();
    v___x_3948_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Try_Collector_checkInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__18;
    v___x_3949_ = l_Lean_stringToMessageData(v___x_3948_);
    return v___x_3949_;
}
pub unsafe fn l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Try_Collector_checkInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg(
    mut v_msg_3950_: *mut LeanObject,
    mut v_declHint_3951_: *mut LeanObject,
    mut v___y_3952_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3954_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_3955_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3956_: u8 = 0;
    let mut v_isExporting_3957_: u8 = 0;
    let mut v___x_3958_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3959_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3960_: u8 = 0;
    let mut v___x_3961_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3962_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3963_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3964_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3965_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3966_: *mut LeanObject = core::ptr::null_mut();
    let mut v_c_3967_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3968_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3969_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3970_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3971_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3972_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3973_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3974_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3975_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_3976_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3978_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3979_: u8 = 0;
    let mut v___x_3980_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3981_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3982_: *mut LeanObject = core::ptr::null_mut();
    let mut v_mod_3983_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3984_: u8 = 0;
    let mut v___x_3985_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3986_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3987_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3988_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3989_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3990_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3991_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3992_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3993_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3994_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3996_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3997_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3998_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3999_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4000_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4001_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4002_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4003_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4004_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4005_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4006_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4007_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4009_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4010_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4011_: u8 = 0;
    let mut v___x_4012_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3954_ = lean_st_ref_get(v___y_3952_);
                v_env_3955_ = lean_ctor_get(v___x_3954_, 0);
                lean_inc_ref(v_env_3955_);
                lean_dec(v___x_3954_);
                v___x_3956_ = l_Lean_Name_isAnonymous(v_declHint_3951_);
                if v___x_3956_ == 0 {
                    v_isExporting_3957_ = lean_ctor_get_uint8(
                        v_env_3955_,
                        (core::mem::size_of::<*mut LeanObject>() * 8) as u32,
                    );
                    if v_isExporting_3957_ == 0 {
                        lean_dec_ref(v_env_3955_);
                        lean_dec(v_declHint_3951_);
                        v___x_3958_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v___x_3958_, 0, v_msg_3950_);
                        return v___x_3958_;
                    } else {
                        lean_inc_ref(v_env_3955_);
                        v___x_3959_ = l_Lean_Environment_setExporting(v_env_3955_, v___x_3956_);
                        lean_inc(v_declHint_3951_);
                        lean_inc_ref(v___x_3959_);
                        v___x_3960_ = l_Lean_Environment_contains(
                            v___x_3959_,
                            v_declHint_3951_,
                            v_isExporting_3957_,
                        );
                        if v___x_3960_ == 0 {
                            lean_dec_ref(v___x_3959_);
                            lean_dec_ref(v_env_3955_);
                            lean_dec(v_declHint_3951_);
                            v___x_3961_ = lean_alloc_ctor(0, 1, (0) as u32);
                            lean_ctor_set(v___x_3961_, 0, v_msg_3950_);
                            return v___x_3961_;
                        } else {
                            v___x_3962_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Try_Collector_checkInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__2), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Try_Collector_checkInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__2_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Try_Collector_checkInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__2);
                            v___x_3963_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Try_Collector_checkInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__5), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Try_Collector_checkInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__5_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Try_Collector_checkInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__5);
                            v___x_3964_ = l_Lean_Options_empty;
                            v___x_3965_ = lean_alloc_ctor(0, 4, (0) as u32);
                            lean_ctor_set(v___x_3965_, 0, v___x_3959_);
                            lean_ctor_set(v___x_3965_, 1, v___x_3962_);
                            lean_ctor_set(v___x_3965_, 2, v___x_3963_);
                            lean_ctor_set(v___x_3965_, 3, v___x_3964_);
                            lean_inc(v_declHint_3951_);
                            v___x_3966_ =
                                l_Lean_MessageData_ofConstName(v_declHint_3951_, v___x_3956_);
                            v_c_3967_ = lean_alloc_ctor(3, 2, (0) as u32);
                            lean_ctor_set(v_c_3967_, 0, v___x_3965_);
                            lean_ctor_set(v_c_3967_, 1, v___x_3966_);
                            v___x_3968_ = l_Lean_Environment_getModuleIdxFor_x3f(
                                v_env_3955_,
                                v_declHint_3951_,
                            );
                            if lean_obj_tag(v___x_3968_) == 0 {
                                lean_dec_ref(v_env_3955_);
                                lean_dec(v_declHint_3951_);
                                v___x_3969_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Try_Collector_checkInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__7), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Try_Collector_checkInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__7_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Try_Collector_checkInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__7);
                                v___x_3970_ = lean_alloc_ctor(7, 2, (0) as u32);
                                lean_ctor_set(v___x_3970_, 0, v___x_3969_);
                                lean_ctor_set(v___x_3970_, 1, v_c_3967_);
                                v___x_3971_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Try_Collector_checkInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__9), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Try_Collector_checkInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__9_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Try_Collector_checkInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__9);
                                v___x_3972_ = lean_alloc_ctor(7, 2, (0) as u32);
                                lean_ctor_set(v___x_3972_, 0, v___x_3970_);
                                lean_ctor_set(v___x_3972_, 1, v___x_3971_);
                                v___x_3973_ = l_Lean_MessageData_note(v___x_3972_);
                                v___x_3974_ = lean_alloc_ctor(7, 2, (0) as u32);
                                lean_ctor_set(v___x_3974_, 0, v_msg_3950_);
                                lean_ctor_set(v___x_3974_, 1, v___x_3973_);
                                v___x_3975_ = lean_alloc_ctor(0, 1, (0) as u32);
                                lean_ctor_set(v___x_3975_, 0, v___x_3974_);
                                return v___x_3975_;
                            } else {
                                v_val_3976_ = lean_ctor_get(v___x_3968_, 0);
                                v_isSharedCheck_4011_ = (!lean_is_exclusive(v___x_3968_)) as u8;
                                if v_isSharedCheck_4011_ == 0 {
                                    v___x_3978_ = v___x_3968_;
                                    v_isShared_3979_ = v_isSharedCheck_4011_;
                                    state = 1;
                                    continue;
                                } else {
                                    lean_inc(v_val_3976_);
                                    lean_dec(v___x_3968_);
                                    v___x_3978_ = lean_box(0);
                                    v_isShared_3979_ = v_isSharedCheck_4011_;
                                    state = 1;
                                    continue;
                                }
                            }
                        }
                    }
                } else {
                    lean_dec_ref(v_env_3955_);
                    lean_dec(v_declHint_3951_);
                    v___x_4012_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_4012_, 0, v_msg_3950_);
                    return v___x_4012_;
                }
            }
            1 => {
                v___x_3980_ = lean_box(0);
                v___x_3981_ = l_Lean_Environment_header(v_env_3955_);
                lean_dec_ref(v_env_3955_);
                v___x_3982_ = l_Lean_EnvironmentHeader_moduleNames(v___x_3981_);
                v_mod_3983_ = lean_array_get(v___x_3980_, v___x_3982_, v_val_3976_);
                lean_dec(v_val_3976_);
                lean_dec_ref(v___x_3982_);
                v___x_3984_ = l_Lean_isPrivateName(v_declHint_3951_);
                lean_dec(v_declHint_3951_);
                if v___x_3984_ == 0 {
                    v___x_3985_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Try_Collector_checkInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__11), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Try_Collector_checkInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__11_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Try_Collector_checkInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__11);
                    v___x_3986_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_3986_, 0, v___x_3985_);
                    lean_ctor_set(v___x_3986_, 1, v_c_3967_);
                    v___x_3987_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Try_Collector_checkInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__13), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Try_Collector_checkInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__13_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Try_Collector_checkInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__13);
                    v___x_3988_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_3988_, 0, v___x_3986_);
                    lean_ctor_set(v___x_3988_, 1, v___x_3987_);
                    v___x_3989_ = l_Lean_MessageData_ofName(v_mod_3983_);
                    v___x_3990_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_3990_, 0, v___x_3988_);
                    lean_ctor_set(v___x_3990_, 1, v___x_3989_);
                    v___x_3991_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Try_Collector_checkInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__15), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Try_Collector_checkInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__15_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Try_Collector_checkInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__15);
                    v___x_3992_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_3992_, 0, v___x_3990_);
                    lean_ctor_set(v___x_3992_, 1, v___x_3991_);
                    v___x_3993_ = l_Lean_MessageData_note(v___x_3992_);
                    v___x_3994_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_3994_, 0, v_msg_3950_);
                    lean_ctor_set(v___x_3994_, 1, v___x_3993_);
                    if v_isShared_3979_ == 0 {
                        lean_ctor_set_tag(v___x_3978_, 0);
                        lean_ctor_set(v___x_3978_, 0, v___x_3994_);
                        v___x_3996_ = v___x_3978_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_3997_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_3997_, 0, v___x_3994_);
                        v___x_3996_ = v_reuseFailAlloc_3997_;
                        state = 2;
                        continue;
                    }
                } else {
                    v___x_3998_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Try_Collector_checkInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__7), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Try_Collector_checkInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__7_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Try_Collector_checkInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__7);
                    v___x_3999_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_3999_, 0, v___x_3998_);
                    lean_ctor_set(v___x_3999_, 1, v_c_3967_);
                    v___x_4000_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Try_Collector_checkInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__17), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Try_Collector_checkInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__17_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Try_Collector_checkInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__17);
                    v___x_4001_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_4001_, 0, v___x_3999_);
                    lean_ctor_set(v___x_4001_, 1, v___x_4000_);
                    v___x_4002_ = l_Lean_MessageData_ofName(v_mod_3983_);
                    v___x_4003_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_4003_, 0, v___x_4001_);
                    lean_ctor_set(v___x_4003_, 1, v___x_4002_);
                    v___x_4004_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Try_Collector_checkInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__19), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Try_Collector_checkInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__19_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Try_Collector_checkInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__19);
                    v___x_4005_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_4005_, 0, v___x_4003_);
                    lean_ctor_set(v___x_4005_, 1, v___x_4004_);
                    v___x_4006_ = l_Lean_MessageData_note(v___x_4005_);
                    v___x_4007_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_4007_, 0, v_msg_3950_);
                    lean_ctor_set(v___x_4007_, 1, v___x_4006_);
                    if v_isShared_3979_ == 0 {
                        lean_ctor_set_tag(v___x_3978_, 0);
                        lean_ctor_set(v___x_3978_, 0, v___x_4007_);
                        v___x_4009_ = v___x_3978_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_4010_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_4010_, 0, v___x_4007_);
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
    mut v_msg_4013_: *mut LeanObject,
    mut v_declHint_4014_: *mut LeanObject,
    mut v___y_4015_: *mut LeanObject,
    mut v___y_4016_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4017_: *mut LeanObject = core::ptr::null_mut();
    v_res_4017_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Try_Collector_checkInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg(v_msg_4013_, v_declHint_4014_, v___y_4015_);
    lean_dec(v___y_4015_);
    return v_res_4017_;
}
pub unsafe fn l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Try_Collector_checkInductive_spec__0_spec__0_spec__1_spec__2_spec__3(
    mut v_msg_4018_: *mut LeanObject,
    mut v_declHint_4019_: *mut LeanObject,
    mut v___y_4020_: *mut LeanObject,
    mut v___y_4021_: *mut LeanObject,
    mut v___y_4022_: *mut LeanObject,
    mut v___y_4023_: *mut LeanObject,
    mut v___y_4024_: *mut LeanObject,
    mut v___y_4025_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4027_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4028_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4030_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4031_: u8 = 0;
    let mut v___x_4032_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4033_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4035_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4036_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4037_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4027_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Try_Collector_checkInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg(v_msg_4018_, v_declHint_4019_, v___y_4025_);
                v_a_4028_ = lean_ctor_get(v___x_4027_, 0);
                v_isSharedCheck_4037_ = (!lean_is_exclusive(v___x_4027_)) as u8;
                if v_isSharedCheck_4037_ == 0 {
                    v___x_4030_ = v___x_4027_;
                    v_isShared_4031_ = v_isSharedCheck_4037_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_a_4028_);
                    lean_dec(v___x_4027_);
                    v___x_4030_ = lean_box(0);
                    v_isShared_4031_ = v_isSharedCheck_4037_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_4032_ = l_Lean_unknownIdentifierMessageTag;
                v___x_4033_ = lean_alloc_ctor(8, 2, (0) as u32);
                lean_ctor_set(v___x_4033_, 0, v___x_4032_);
                lean_ctor_set(v___x_4033_, 1, v_a_4028_);
                if v_isShared_4031_ == 0 {
                    lean_ctor_set(v___x_4030_, 0, v___x_4033_);
                    v___x_4035_ = v___x_4030_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4036_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4036_, 0, v___x_4033_);
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
    mut v_msg_4038_: *mut LeanObject,
    mut v_declHint_4039_: *mut LeanObject,
    mut v___y_4040_: *mut LeanObject,
    mut v___y_4041_: *mut LeanObject,
    mut v___y_4042_: *mut LeanObject,
    mut v___y_4043_: *mut LeanObject,
    mut v___y_4044_: *mut LeanObject,
    mut v___y_4045_: *mut LeanObject,
    mut v___y_4046_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4047_: *mut LeanObject = core::ptr::null_mut();
    v_res_4047_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Try_Collector_checkInductive_spec__0_spec__0_spec__1_spec__2_spec__3(v_msg_4038_, v_declHint_4039_, v___y_4040_, v___y_4041_, v___y_4042_, v___y_4043_, v___y_4044_, v___y_4045_);
    lean_dec(v___y_4045_);
    lean_dec_ref(v___y_4044_);
    lean_dec(v___y_4043_);
    lean_dec_ref(v___y_4042_);
    lean_dec(v___y_4041_);
    lean_dec_ref(v___y_4040_);
    return v_res_4047_;
}
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Try_Collector_checkInductive_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6_spec__7(
    mut v_msgData_4048_: *mut LeanObject,
    mut v___y_4049_: *mut LeanObject,
    mut v___y_4050_: *mut LeanObject,
    mut v___y_4051_: *mut LeanObject,
    mut v___y_4052_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4054_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_4055_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4056_: *mut LeanObject = core::ptr::null_mut();
    let mut v_mctx_4057_: *mut LeanObject = core::ptr::null_mut();
    let mut v_lctx_4058_: *mut LeanObject = core::ptr::null_mut();
    let mut v_options_4059_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4060_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4061_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4062_: *mut LeanObject = core::ptr::null_mut();
    v___x_4054_ = lean_st_ref_get(v___y_4052_);
    v_env_4055_ = lean_ctor_get(v___x_4054_, 0);
    lean_inc_ref(v_env_4055_);
    lean_dec(v___x_4054_);
    v___x_4056_ = lean_st_ref_get(v___y_4050_);
    v_mctx_4057_ = lean_ctor_get(v___x_4056_, 0);
    lean_inc_ref(v_mctx_4057_);
    lean_dec(v___x_4056_);
    v_lctx_4058_ = lean_ctor_get(v___y_4049_, 2);
    v_options_4059_ = lean_ctor_get(v___y_4051_, 2);
    lean_inc_ref(v_options_4059_);
    lean_inc_ref(v_lctx_4058_);
    v___x_4060_ = lean_alloc_ctor(0, 4, (0) as u32);
    lean_ctor_set(v___x_4060_, 0, v_env_4055_);
    lean_ctor_set(v___x_4060_, 1, v_mctx_4057_);
    lean_ctor_set(v___x_4060_, 2, v_lctx_4058_);
    lean_ctor_set(v___x_4060_, 3, v_options_4059_);
    v___x_4061_ = lean_alloc_ctor(3, 2, (0) as u32);
    lean_ctor_set(v___x_4061_, 0, v___x_4060_);
    lean_ctor_set(v___x_4061_, 1, v_msgData_4048_);
    v___x_4062_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_4062_, 0, v___x_4061_);
    return v___x_4062_;
}
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Try_Collector_checkInductive_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6_spec__7___boxed(
    mut v_msgData_4063_: *mut LeanObject,
    mut v___y_4064_: *mut LeanObject,
    mut v___y_4065_: *mut LeanObject,
    mut v___y_4066_: *mut LeanObject,
    mut v___y_4067_: *mut LeanObject,
    mut v___y_4068_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4069_: *mut LeanObject = core::ptr::null_mut();
    v_res_4069_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Try_Collector_checkInductive_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6_spec__7(v_msgData_4063_, v___y_4064_, v___y_4065_, v___y_4066_, v___y_4067_);
    lean_dec(v___y_4067_);
    lean_dec_ref(v___y_4066_);
    lean_dec(v___y_4065_);
    lean_dec_ref(v___y_4064_);
    return v_res_4069_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Try_Collector_checkInductive_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6___redArg(
    mut v_msg_4070_: *mut LeanObject,
    mut v___y_4071_: *mut LeanObject,
    mut v___y_4072_: *mut LeanObject,
    mut v___y_4073_: *mut LeanObject,
    mut v___y_4074_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_ref_4076_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4077_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4078_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4080_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4081_: u8 = 0;
    let mut v___x_4082_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4084_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4085_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4086_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ref_4076_ = lean_ctor_get(v___y_4073_, 5);
                v___x_4077_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Try_Collector_checkInductive_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6_spec__7(v_msg_4070_, v___y_4071_, v___y_4072_, v___y_4073_, v___y_4074_);
                v_a_4078_ = lean_ctor_get(v___x_4077_, 0);
                v_isSharedCheck_4086_ = (!lean_is_exclusive(v___x_4077_)) as u8;
                if v_isSharedCheck_4086_ == 0 {
                    v___x_4080_ = v___x_4077_;
                    v_isShared_4081_ = v_isSharedCheck_4086_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_a_4078_);
                    lean_dec(v___x_4077_);
                    v___x_4080_ = lean_box(0);
                    v_isShared_4081_ = v_isSharedCheck_4086_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                lean_inc(v_ref_4076_);
                v___x_4082_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_4082_, 0, v_ref_4076_);
                lean_ctor_set(v___x_4082_, 1, v_a_4078_);
                if v_isShared_4081_ == 0 {
                    lean_ctor_set_tag(v___x_4080_, 1);
                    lean_ctor_set(v___x_4080_, 0, v___x_4082_);
                    v___x_4084_ = v___x_4080_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4085_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4085_, 0, v___x_4082_);
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
    mut v_msg_4087_: *mut LeanObject,
    mut v___y_4088_: *mut LeanObject,
    mut v___y_4089_: *mut LeanObject,
    mut v___y_4090_: *mut LeanObject,
    mut v___y_4091_: *mut LeanObject,
    mut v___y_4092_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4093_: *mut LeanObject = core::ptr::null_mut();
    v_res_4093_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Try_Collector_checkInductive_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6___redArg(v_msg_4087_, v___y_4088_, v___y_4089_, v___y_4090_, v___y_4091_);
    lean_dec(v___y_4091_);
    lean_dec_ref(v___y_4090_);
    lean_dec(v___y_4089_);
    lean_dec_ref(v___y_4088_);
    return v_res_4093_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Try_Collector_checkInductive_spec__0_spec__0_spec__1_spec__2_spec__4___redArg(
    mut v_ref_4094_: *mut LeanObject,
    mut v_msg_4095_: *mut LeanObject,
    mut v___y_4096_: *mut LeanObject,
    mut v___y_4097_: *mut LeanObject,
    mut v___y_4098_: *mut LeanObject,
    mut v___y_4099_: *mut LeanObject,
    mut v___y_4100_: *mut LeanObject,
    mut v___y_4101_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_fileName_4103_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fileMap_4104_: *mut LeanObject = core::ptr::null_mut();
    let mut v_options_4105_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currRecDepth_4106_: *mut LeanObject = core::ptr::null_mut();
    let mut v_maxRecDepth_4107_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ref_4108_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currNamespace_4109_: *mut LeanObject = core::ptr::null_mut();
    let mut v_openDecls_4110_: *mut LeanObject = core::ptr::null_mut();
    let mut v_initHeartbeats_4111_: *mut LeanObject = core::ptr::null_mut();
    let mut v_maxHeartbeats_4112_: *mut LeanObject = core::ptr::null_mut();
    let mut v_quotContext_4113_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currMacroScope_4114_: *mut LeanObject = core::ptr::null_mut();
    let mut v_diag_4115_: u8 = 0;
    let mut v_cancelTk_x3f_4116_: *mut LeanObject = core::ptr::null_mut();
    let mut v_suppressElabErrors_4117_: u8 = 0;
    let mut v_inheritedTraceOptions_4118_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ref_4119_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4120_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4121_: *mut LeanObject = core::ptr::null_mut();
    v_fileName_4103_ = lean_ctor_get(v___y_4100_, 0);
    v_fileMap_4104_ = lean_ctor_get(v___y_4100_, 1);
    v_options_4105_ = lean_ctor_get(v___y_4100_, 2);
    v_currRecDepth_4106_ = lean_ctor_get(v___y_4100_, 3);
    v_maxRecDepth_4107_ = lean_ctor_get(v___y_4100_, 4);
    v_ref_4108_ = lean_ctor_get(v___y_4100_, 5);
    v_currNamespace_4109_ = lean_ctor_get(v___y_4100_, 6);
    v_openDecls_4110_ = lean_ctor_get(v___y_4100_, 7);
    v_initHeartbeats_4111_ = lean_ctor_get(v___y_4100_, 8);
    v_maxHeartbeats_4112_ = lean_ctor_get(v___y_4100_, 9);
    v_quotContext_4113_ = lean_ctor_get(v___y_4100_, 10);
    v_currMacroScope_4114_ = lean_ctor_get(v___y_4100_, 11);
    v_diag_4115_ = lean_ctor_get_uint8(
        v___y_4100_,
        (core::mem::size_of::<*mut LeanObject>() * 14) as u32,
    );
    v_cancelTk_x3f_4116_ = lean_ctor_get(v___y_4100_, 12);
    v_suppressElabErrors_4117_ = lean_ctor_get_uint8(
        v___y_4100_,
        (core::mem::size_of::<*mut LeanObject>() * 14 + 1) as u32,
    );
    v_inheritedTraceOptions_4118_ = lean_ctor_get(v___y_4100_, 13);
    v_ref_4119_ = l_Lean_replaceRef(v_ref_4094_, v_ref_4108_);
    lean_inc_ref(v_inheritedTraceOptions_4118_);
    lean_inc(v_cancelTk_x3f_4116_);
    lean_inc(v_currMacroScope_4114_);
    lean_inc(v_quotContext_4113_);
    lean_inc(v_maxHeartbeats_4112_);
    lean_inc(v_initHeartbeats_4111_);
    lean_inc(v_openDecls_4110_);
    lean_inc(v_currNamespace_4109_);
    lean_inc(v_maxRecDepth_4107_);
    lean_inc(v_currRecDepth_4106_);
    lean_inc_ref(v_options_4105_);
    lean_inc_ref(v_fileMap_4104_);
    lean_inc_ref(v_fileName_4103_);
    v___x_4120_ = lean_alloc_ctor(0, 14, (2) as u32);
    lean_ctor_set(v___x_4120_, 0, v_fileName_4103_);
    lean_ctor_set(v___x_4120_, 1, v_fileMap_4104_);
    lean_ctor_set(v___x_4120_, 2, v_options_4105_);
    lean_ctor_set(v___x_4120_, 3, v_currRecDepth_4106_);
    lean_ctor_set(v___x_4120_, 4, v_maxRecDepth_4107_);
    lean_ctor_set(v___x_4120_, 5, v_ref_4119_);
    lean_ctor_set(v___x_4120_, 6, v_currNamespace_4109_);
    lean_ctor_set(v___x_4120_, 7, v_openDecls_4110_);
    lean_ctor_set(v___x_4120_, 8, v_initHeartbeats_4111_);
    lean_ctor_set(v___x_4120_, 9, v_maxHeartbeats_4112_);
    lean_ctor_set(v___x_4120_, 10, v_quotContext_4113_);
    lean_ctor_set(v___x_4120_, 11, v_currMacroScope_4114_);
    lean_ctor_set(v___x_4120_, 12, v_cancelTk_x3f_4116_);
    lean_ctor_set(v___x_4120_, 13, v_inheritedTraceOptions_4118_);
    lean_ctor_set_uint8(
        v___x_4120_,
        (core::mem::size_of::<*mut LeanObject>() * 14) as u32,
        v_diag_4115_,
    );
    lean_ctor_set_uint8(
        v___x_4120_,
        (core::mem::size_of::<*mut LeanObject>() * 14 + 1) as u32,
        v_suppressElabErrors_4117_,
    );
    v___x_4121_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Try_Collector_checkInductive_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6___redArg(v_msg_4095_, v___y_4098_, v___y_4099_, v___x_4120_, v___y_4101_);
    lean_dec_ref_known(v___x_4120_, 14);
    return v___x_4121_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Try_Collector_checkInductive_spec__0_spec__0_spec__1_spec__2_spec__4___redArg___boxed(
    mut v_ref_4122_: *mut LeanObject,
    mut v_msg_4123_: *mut LeanObject,
    mut v___y_4124_: *mut LeanObject,
    mut v___y_4125_: *mut LeanObject,
    mut v___y_4126_: *mut LeanObject,
    mut v___y_4127_: *mut LeanObject,
    mut v___y_4128_: *mut LeanObject,
    mut v___y_4129_: *mut LeanObject,
    mut v___y_4130_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4131_: *mut LeanObject = core::ptr::null_mut();
    v_res_4131_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Try_Collector_checkInductive_spec__0_spec__0_spec__1_spec__2_spec__4___redArg(v_ref_4122_, v_msg_4123_, v___y_4124_, v___y_4125_, v___y_4126_, v___y_4127_, v___y_4128_, v___y_4129_);
    lean_dec(v___y_4129_);
    lean_dec_ref(v___y_4128_);
    lean_dec(v___y_4127_);
    lean_dec_ref(v___y_4126_);
    lean_dec(v___y_4125_);
    lean_dec_ref(v___y_4124_);
    lean_dec(v_ref_4122_);
    return v_res_4131_;
}
pub unsafe fn l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Try_Collector_checkInductive_spec__0_spec__0_spec__1_spec__2___redArg(
    mut v_ref_4132_: *mut LeanObject,
    mut v_msg_4133_: *mut LeanObject,
    mut v_declHint_4134_: *mut LeanObject,
    mut v___y_4135_: *mut LeanObject,
    mut v___y_4136_: *mut LeanObject,
    mut v___y_4137_: *mut LeanObject,
    mut v___y_4138_: *mut LeanObject,
    mut v___y_4139_: *mut LeanObject,
    mut v___y_4140_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4142_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4143_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4144_: *mut LeanObject = core::ptr::null_mut();
    v___x_4142_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Try_Collector_checkInductive_spec__0_spec__0_spec__1_spec__2_spec__3(v_msg_4133_, v_declHint_4134_, v___y_4135_, v___y_4136_, v___y_4137_, v___y_4138_, v___y_4139_, v___y_4140_);
    v_a_4143_ = lean_ctor_get(v___x_4142_, 0);
    lean_inc(v_a_4143_);
    lean_dec_ref(v___x_4142_);
    v___x_4144_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Try_Collector_checkInductive_spec__0_spec__0_spec__1_spec__2_spec__4___redArg(v_ref_4132_, v_a_4143_, v___y_4135_, v___y_4136_, v___y_4137_, v___y_4138_, v___y_4139_, v___y_4140_);
    return v___x_4144_;
}
pub unsafe fn l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Try_Collector_checkInductive_spec__0_spec__0_spec__1_spec__2___redArg___boxed(
    mut v_ref_4145_: *mut LeanObject,
    mut v_msg_4146_: *mut LeanObject,
    mut v_declHint_4147_: *mut LeanObject,
    mut v___y_4148_: *mut LeanObject,
    mut v___y_4149_: *mut LeanObject,
    mut v___y_4150_: *mut LeanObject,
    mut v___y_4151_: *mut LeanObject,
    mut v___y_4152_: *mut LeanObject,
    mut v___y_4153_: *mut LeanObject,
    mut v___y_4154_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4155_: *mut LeanObject = core::ptr::null_mut();
    v_res_4155_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Try_Collector_checkInductive_spec__0_spec__0_spec__1_spec__2___redArg(v_ref_4145_, v_msg_4146_, v_declHint_4147_, v___y_4148_, v___y_4149_, v___y_4150_, v___y_4151_, v___y_4152_, v___y_4153_);
    lean_dec(v___y_4153_);
    lean_dec_ref(v___y_4152_);
    lean_dec(v___y_4151_);
    lean_dec_ref(v___y_4150_);
    lean_dec(v___y_4149_);
    lean_dec_ref(v___y_4148_);
    lean_dec(v_ref_4145_);
    return v_res_4155_;
}
pub unsafe fn _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Try_Collector_checkInductive_spec__0_spec__0_spec__1___redArg___closed__1()
-> *mut LeanObject {
    let mut v___x_4157_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4158_: *mut LeanObject = core::ptr::null_mut();
    v___x_4157_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Try_Collector_checkInductive_spec__0_spec__0_spec__1___redArg___closed__0;
    v___x_4158_ = l_Lean_stringToMessageData(v___x_4157_);
    return v___x_4158_;
}
pub unsafe fn _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Try_Collector_checkInductive_spec__0_spec__0_spec__1___redArg___closed__3()
-> *mut LeanObject {
    let mut v___x_4160_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4161_: *mut LeanObject = core::ptr::null_mut();
    v___x_4160_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Try_Collector_checkInductive_spec__0_spec__0_spec__1___redArg___closed__2;
    v___x_4161_ = l_Lean_stringToMessageData(v___x_4160_);
    return v___x_4161_;
}
pub unsafe fn l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Try_Collector_checkInductive_spec__0_spec__0_spec__1___redArg(
    mut v_ref_4162_: *mut LeanObject,
    mut v_constName_4163_: *mut LeanObject,
    mut v___y_4164_: *mut LeanObject,
    mut v___y_4165_: *mut LeanObject,
    mut v___y_4166_: *mut LeanObject,
    mut v___y_4167_: *mut LeanObject,
    mut v___y_4168_: *mut LeanObject,
    mut v___y_4169_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4171_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4172_: u8 = 0;
    let mut v___x_4173_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4174_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4175_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4176_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4177_: *mut LeanObject = core::ptr::null_mut();
    v___x_4171_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Try_Collector_checkInductive_spec__0_spec__0_spec__1___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Try_Collector_checkInductive_spec__0_spec__0_spec__1___redArg___closed__1_once), _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Try_Collector_checkInductive_spec__0_spec__0_spec__1___redArg___closed__1);
    v___x_4172_ = 0;
    lean_inc(v_constName_4163_);
    v___x_4173_ = l_Lean_MessageData_ofConstName(v_constName_4163_, v___x_4172_);
    v___x_4174_ = lean_alloc_ctor(7, 2, (0) as u32);
    lean_ctor_set(v___x_4174_, 0, v___x_4171_);
    lean_ctor_set(v___x_4174_, 1, v___x_4173_);
    v___x_4175_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Try_Collector_checkInductive_spec__0_spec__0_spec__1___redArg___closed__3), core::ptr::addr_of_mut!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Try_Collector_checkInductive_spec__0_spec__0_spec__1___redArg___closed__3_once), _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Try_Collector_checkInductive_spec__0_spec__0_spec__1___redArg___closed__3);
    v___x_4176_ = lean_alloc_ctor(7, 2, (0) as u32);
    lean_ctor_set(v___x_4176_, 0, v___x_4174_);
    lean_ctor_set(v___x_4176_, 1, v___x_4175_);
    v___x_4177_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Try_Collector_checkInductive_spec__0_spec__0_spec__1_spec__2___redArg(v_ref_4162_, v___x_4176_, v_constName_4163_, v___y_4164_, v___y_4165_, v___y_4166_, v___y_4167_, v___y_4168_, v___y_4169_);
    return v___x_4177_;
}
pub unsafe fn l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Try_Collector_checkInductive_spec__0_spec__0_spec__1___redArg___boxed(
    mut v_ref_4178_: *mut LeanObject,
    mut v_constName_4179_: *mut LeanObject,
    mut v___y_4180_: *mut LeanObject,
    mut v___y_4181_: *mut LeanObject,
    mut v___y_4182_: *mut LeanObject,
    mut v___y_4183_: *mut LeanObject,
    mut v___y_4184_: *mut LeanObject,
    mut v___y_4185_: *mut LeanObject,
    mut v___y_4186_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4187_: *mut LeanObject = core::ptr::null_mut();
    v_res_4187_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Try_Collector_checkInductive_spec__0_spec__0_spec__1___redArg(v_ref_4178_, v_constName_4179_, v___y_4180_, v___y_4181_, v___y_4182_, v___y_4183_, v___y_4184_, v___y_4185_);
    lean_dec(v___y_4185_);
    lean_dec_ref(v___y_4184_);
    lean_dec(v___y_4183_);
    lean_dec_ref(v___y_4182_);
    lean_dec(v___y_4181_);
    lean_dec_ref(v___y_4180_);
    lean_dec(v_ref_4178_);
    return v_res_4187_;
}
pub unsafe fn l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Try_Collector_checkInductive_spec__0_spec__0___redArg(
    mut v_constName_4188_: *mut LeanObject,
    mut v___y_4189_: *mut LeanObject,
    mut v___y_4190_: *mut LeanObject,
    mut v___y_4191_: *mut LeanObject,
    mut v___y_4192_: *mut LeanObject,
    mut v___y_4193_: *mut LeanObject,
    mut v___y_4194_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_ref_4196_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4197_: *mut LeanObject = core::ptr::null_mut();
    v_ref_4196_ = lean_ctor_get(v___y_4193_, 5);
    v___x_4197_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Try_Collector_checkInductive_spec__0_spec__0_spec__1___redArg(v_ref_4196_, v_constName_4188_, v___y_4189_, v___y_4190_, v___y_4191_, v___y_4192_, v___y_4193_, v___y_4194_);
    return v___x_4197_;
}
pub unsafe fn l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Try_Collector_checkInductive_spec__0_spec__0___redArg___boxed(
    mut v_constName_4198_: *mut LeanObject,
    mut v___y_4199_: *mut LeanObject,
    mut v___y_4200_: *mut LeanObject,
    mut v___y_4201_: *mut LeanObject,
    mut v___y_4202_: *mut LeanObject,
    mut v___y_4203_: *mut LeanObject,
    mut v___y_4204_: *mut LeanObject,
    mut v___y_4205_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4206_: *mut LeanObject = core::ptr::null_mut();
    v_res_4206_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Try_Collector_checkInductive_spec__0_spec__0___redArg(v_constName_4198_, v___y_4199_, v___y_4200_, v___y_4201_, v___y_4202_, v___y_4203_, v___y_4204_);
    lean_dec(v___y_4204_);
    lean_dec_ref(v___y_4203_);
    lean_dec(v___y_4202_);
    lean_dec_ref(v___y_4201_);
    lean_dec(v___y_4200_);
    lean_dec_ref(v___y_4199_);
    return v_res_4206_;
}
pub unsafe fn l_Lean_getConstInfo___at___00Lean_Meta_Try_Collector_checkInductive_spec__0(
    mut v_constName_4207_: *mut LeanObject,
    mut v___y_4208_: *mut LeanObject,
    mut v___y_4209_: *mut LeanObject,
    mut v___y_4210_: *mut LeanObject,
    mut v___y_4211_: *mut LeanObject,
    mut v___y_4212_: *mut LeanObject,
    mut v___y_4213_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4215_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_4216_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4217_: u8 = 0;
    let mut v___x_4218_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4219_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_4220_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4222_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4223_: u8 = 0;
    let mut v___x_4225_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4226_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4227_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4215_ = lean_st_ref_get(v___y_4213_);
                v_env_4216_ = lean_ctor_get(v___x_4215_, 0);
                lean_inc_ref(v_env_4216_);
                lean_dec(v___x_4215_);
                v___x_4217_ = 0;
                lean_inc(v_constName_4207_);
                v___x_4218_ =
                    l_Lean_Environment_find_x3f(v_env_4216_, v_constName_4207_, v___x_4217_);
                if lean_obj_tag(v___x_4218_) == 0 {
                    v___x_4219_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Try_Collector_checkInductive_spec__0_spec__0___redArg(v_constName_4207_, v___y_4208_, v___y_4209_, v___y_4210_, v___y_4211_, v___y_4212_, v___y_4213_);
                    return v___x_4219_;
                } else {
                    lean_dec(v_constName_4207_);
                    v_val_4220_ = lean_ctor_get(v___x_4218_, 0);
                    v_isSharedCheck_4227_ = (!lean_is_exclusive(v___x_4218_)) as u8;
                    if v_isSharedCheck_4227_ == 0 {
                        v___x_4222_ = v___x_4218_;
                        v_isShared_4223_ = v_isSharedCheck_4227_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_val_4220_);
                        lean_dec(v___x_4218_);
                        v___x_4222_ = lean_box(0);
                        v_isShared_4223_ = v_isSharedCheck_4227_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_4223_ == 0 {
                    lean_ctor_set_tag(v___x_4222_, 0);
                    v___x_4225_ = v___x_4222_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4226_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4226_, 0, v_val_4220_);
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
    mut v_constName_4228_: *mut LeanObject,
    mut v___y_4229_: *mut LeanObject,
    mut v___y_4230_: *mut LeanObject,
    mut v___y_4231_: *mut LeanObject,
    mut v___y_4232_: *mut LeanObject,
    mut v___y_4233_: *mut LeanObject,
    mut v___y_4234_: *mut LeanObject,
    mut v___y_4235_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4236_: *mut LeanObject = core::ptr::null_mut();
    v_res_4236_ = l_Lean_getConstInfo___at___00Lean_Meta_Try_Collector_checkInductive_spec__0(
        v_constName_4228_,
        v___y_4229_,
        v___y_4230_,
        v___y_4231_,
        v___y_4232_,
        v___y_4233_,
        v___y_4234_,
    );
    lean_dec(v___y_4234_);
    lean_dec_ref(v___y_4233_);
    lean_dec(v___y_4232_);
    lean_dec_ref(v___y_4231_);
    lean_dec(v___y_4230_);
    lean_dec_ref(v___y_4229_);
    return v_res_4236_;
}
pub unsafe fn l_Lean_Meta_Try_Collector_checkInductive(
    mut v_localDecl_4237_: *mut LeanObject,
    mut v_a_4238_: *mut LeanObject,
    mut v_a_4239_: *mut LeanObject,
    mut v_a_4240_: *mut LeanObject,
    mut v_a_4241_: *mut LeanObject,
    mut v_a_4242_: *mut LeanObject,
    mut v_a_4243_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4245_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4246_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4247_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4249_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4250_: u8 = 0;
    let mut v___x_4251_: *mut LeanObject = core::ptr::null_mut();
    let mut v_declName_4252_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4253_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4254_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4256_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4257_: u8 = 0;
    let mut v_val_4258_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4259_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4260_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4262_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4263_: u8 = 0;
    let mut v___x_4264_: u8 = 0;
    let mut v___x_4265_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4267_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4268_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4269_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4270_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4272_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4273_: u8 = 0;
    let mut v___x_4274_: u8 = 0;
    let mut v___x_4275_: *mut LeanObject = core::ptr::null_mut();
    let mut v_allConsts_4276_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unfoldCandidates_4277_: *mut LeanObject = core::ptr::null_mut();
    let mut v_eqnCandidates_4278_: *mut LeanObject = core::ptr::null_mut();
    let mut v_funIndCandidates_4279_: *mut LeanObject = core::ptr::null_mut();
    let mut v_indCandidates_4280_: *mut LeanObject = core::ptr::null_mut();
    let mut v_libSearchResults_4281_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4283_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4284_: u8 = 0;
    let mut v___x_4285_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4286_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4287_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4289_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4290_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4291_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4293_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4294_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4295_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4296_: u8 = 0;
    let mut v___x_4297_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4299_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4300_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4301_: u8 = 0;
    let mut v_a_4302_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4304_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4305_: u8 = 0;
    let mut v___x_4307_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4308_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4309_: u8 = 0;
    let mut v_isSharedCheck_4310_: u8 = 0;
    let mut v___x_4311_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4313_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4314_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4315_: u8 = 0;
    let mut v_a_4316_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4318_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4319_: u8 = 0;
    let mut v___x_4321_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4322_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4323_: u8 = 0;
    let mut v___x_4324_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4326_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4327_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4328_: u8 = 0;
    let mut v_a_4329_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4331_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4332_: u8 = 0;
    let mut v___x_4334_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4335_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4336_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4245_ = l_Lean_LocalDecl_type(v_localDecl_4237_);
                v___x_4246_ =
                    l_Lean_Meta_whnfD(v___x_4245_, v_a_4240_, v_a_4241_, v_a_4242_, v_a_4243_);
                if lean_obj_tag(v___x_4246_) == 0 {
                    v_a_4247_ = lean_ctor_get(v___x_4246_, 0);
                    v_isSharedCheck_4328_ = (!lean_is_exclusive(v___x_4246_)) as u8;
                    if v_isSharedCheck_4328_ == 0 {
                        v___x_4249_ = v___x_4246_;
                        v_isShared_4250_ = v_isSharedCheck_4328_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_4247_);
                        lean_dec(v___x_4246_);
                        v___x_4249_ = lean_box(0);
                        v_isShared_4250_ = v_isSharedCheck_4328_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_4329_ = lean_ctor_get(v___x_4246_, 0);
                    v_isSharedCheck_4336_ = (!lean_is_exclusive(v___x_4246_)) as u8;
                    if v_isSharedCheck_4336_ == 0 {
                        v___x_4331_ = v___x_4246_;
                        v_isShared_4332_ = v_isSharedCheck_4336_;
                        state = 16;
                        continue;
                    } else {
                        lean_inc(v_a_4329_);
                        lean_dec(v___x_4246_);
                        v___x_4331_ = lean_box(0);
                        v_isShared_4332_ = v_isSharedCheck_4336_;
                        state = 16;
                        continue;
                    }
                }
            }
            1 => {
                v___x_4251_ = l_Lean_Expr_getAppFn(v_a_4247_);
                lean_dec(v_a_4247_);
                if lean_obj_tag(v___x_4251_) == 4 {
                    lean_del_object(v___x_4249_);
                    v_declName_4252_ = lean_ctor_get(v___x_4251_, 0);
                    lean_inc_n(v_declName_4252_, 2);
                    lean_dec_ref_known(v___x_4251_, 2);
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
                    if lean_obj_tag(v___x_4253_) == 0 {
                        v_a_4254_ = lean_ctor_get(v___x_4253_, 0);
                        v_isSharedCheck_4315_ = (!lean_is_exclusive(v___x_4253_)) as u8;
                        if v_isSharedCheck_4315_ == 0 {
                            v___x_4256_ = v___x_4253_;
                            v_isShared_4257_ = v_isSharedCheck_4315_;
                            state = 2;
                            continue;
                        } else {
                            lean_inc(v_a_4254_);
                            lean_dec(v___x_4253_);
                            v___x_4256_ = lean_box(0);
                            v_isShared_4257_ = v_isSharedCheck_4315_;
                            state = 2;
                            continue;
                        }
                    } else {
                        lean_dec(v_declName_4252_);
                        v_a_4316_ = lean_ctor_get(v___x_4253_, 0);
                        v_isSharedCheck_4323_ = (!lean_is_exclusive(v___x_4253_)) as u8;
                        if v_isSharedCheck_4323_ == 0 {
                            v___x_4318_ = v___x_4253_;
                            v_isShared_4319_ = v_isSharedCheck_4323_;
                            state = 13;
                            continue;
                        } else {
                            lean_inc(v_a_4316_);
                            lean_dec(v___x_4253_);
                            v___x_4318_ = lean_box(0);
                            v_isShared_4319_ = v_isSharedCheck_4323_;
                            state = 13;
                            continue;
                        }
                    }
                } else {
                    lean_dec_ref(v___x_4251_);
                    v___x_4324_ = lean_box(0);
                    if v_isShared_4250_ == 0 {
                        lean_ctor_set(v___x_4249_, 0, v___x_4324_);
                        v___x_4326_ = v___x_4249_;
                        state = 15;
                        continue;
                    } else {
                        v_reuseFailAlloc_4327_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_4327_, 0, v___x_4324_);
                        v___x_4326_ = v_reuseFailAlloc_4327_;
                        state = 15;
                        continue;
                    }
                }
            }
            2 => {
                if lean_obj_tag(v_a_4254_) == 5 {
                    lean_del_object(v___x_4256_);
                    v_val_4258_ = lean_ctor_get(v_a_4254_, 0);
                    lean_inc_ref(v_val_4258_);
                    lean_dec_ref_known(v_a_4254_, 1);
                    v___x_4259_ = l_Lean_Meta_Try_Collector_isEligible___redArg(
                        v_declName_4252_,
                        v_a_4238_,
                        v_a_4242_,
                        v_a_4243_,
                    );
                    v_a_4260_ = lean_ctor_get(v___x_4259_, 0);
                    v_isSharedCheck_4310_ = (!lean_is_exclusive(v___x_4259_)) as u8;
                    if v_isSharedCheck_4310_ == 0 {
                        v___x_4262_ = v___x_4259_;
                        v_isShared_4263_ = v_isSharedCheck_4310_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_4260_);
                        lean_dec(v___x_4259_);
                        v___x_4262_ = lean_box(0);
                        v_isShared_4263_ = v_isSharedCheck_4310_;
                        state = 3;
                        continue;
                    }
                } else {
                    lean_dec(v_a_4254_);
                    lean_dec(v_declName_4252_);
                    v___x_4311_ = lean_box(0);
                    if v_isShared_4257_ == 0 {
                        lean_ctor_set(v___x_4256_, 0, v___x_4311_);
                        v___x_4313_ = v___x_4256_;
                        state = 12;
                        continue;
                    } else {
                        v_reuseFailAlloc_4314_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_4314_, 0, v___x_4311_);
                        v___x_4313_ = v_reuseFailAlloc_4314_;
                        state = 12;
                        continue;
                    }
                }
            }
            3 => {
                v___x_4264_ = (lean_unbox(v_a_4260_) as u8);
                lean_dec(v_a_4260_);
                if v___x_4264_ == 0 {
                    lean_dec_ref(v_val_4258_);
                    lean_dec(v_declName_4252_);
                    v___x_4265_ = lean_box(0);
                    if v_isShared_4263_ == 0 {
                        lean_ctor_set(v___x_4262_, 0, v___x_4265_);
                        v___x_4267_ = v___x_4262_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_4268_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_4268_, 0, v___x_4265_);
                        v___x_4267_ = v_reuseFailAlloc_4268_;
                        state = 4;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_4262_);
                    v___x_4269_ =
                        l_Lean_Meta_Grind_isGlobalSplit___redArg(v_declName_4252_, v_a_4243_);
                    lean_dec(v_declName_4252_);
                    if lean_obj_tag(v___x_4269_) == 0 {
                        v_a_4270_ = lean_ctor_get(v___x_4269_, 0);
                        v_isSharedCheck_4301_ = (!lean_is_exclusive(v___x_4269_)) as u8;
                        if v_isSharedCheck_4301_ == 0 {
                            v___x_4272_ = v___x_4269_;
                            v_isShared_4273_ = v_isSharedCheck_4301_;
                            state = 5;
                            continue;
                        } else {
                            lean_inc(v_a_4270_);
                            lean_dec(v___x_4269_);
                            v___x_4272_ = lean_box(0);
                            v_isShared_4273_ = v_isSharedCheck_4301_;
                            state = 5;
                            continue;
                        }
                    } else {
                        lean_dec_ref(v_val_4258_);
                        v_a_4302_ = lean_ctor_get(v___x_4269_, 0);
                        v_isSharedCheck_4309_ = (!lean_is_exclusive(v___x_4269_)) as u8;
                        if v_isSharedCheck_4309_ == 0 {
                            v___x_4304_ = v___x_4269_;
                            v_isShared_4305_ = v_isSharedCheck_4309_;
                            state = 10;
                            continue;
                        } else {
                            lean_inc(v_a_4302_);
                            lean_dec(v___x_4269_);
                            v___x_4304_ = lean_box(0);
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
                v___x_4274_ = (lean_unbox(v_a_4270_) as u8);
                lean_dec(v_a_4270_);
                if v___x_4274_ == 0 {
                    v___x_4275_ = lean_st_ref_take(v_a_4239_);
                    v_allConsts_4276_ = lean_ctor_get(v___x_4275_, 0);
                    v_unfoldCandidates_4277_ = lean_ctor_get(v___x_4275_, 1);
                    v_eqnCandidates_4278_ = lean_ctor_get(v___x_4275_, 2);
                    v_funIndCandidates_4279_ = lean_ctor_get(v___x_4275_, 3);
                    v_indCandidates_4280_ = lean_ctor_get(v___x_4275_, 4);
                    v_libSearchResults_4281_ = lean_ctor_get(v___x_4275_, 5);
                    v_isSharedCheck_4296_ = (!lean_is_exclusive(v___x_4275_)) as u8;
                    if v_isSharedCheck_4296_ == 0 {
                        v___x_4283_ = v___x_4275_;
                        v_isShared_4284_ = v_isSharedCheck_4296_;
                        state = 6;
                        continue;
                    } else {
                        lean_inc(v_libSearchResults_4281_);
                        lean_inc(v_indCandidates_4280_);
                        lean_inc(v_funIndCandidates_4279_);
                        lean_inc(v_eqnCandidates_4278_);
                        lean_inc(v_unfoldCandidates_4277_);
                        lean_inc(v_allConsts_4276_);
                        lean_dec(v___x_4275_);
                        v___x_4283_ = lean_box(0);
                        v_isShared_4284_ = v_isSharedCheck_4296_;
                        state = 6;
                        continue;
                    }
                } else {
                    lean_dec_ref(v_val_4258_);
                    v___x_4297_ = lean_box(0);
                    if v_isShared_4273_ == 0 {
                        lean_ctor_set(v___x_4272_, 0, v___x_4297_);
                        v___x_4299_ = v___x_4272_;
                        state = 9;
                        continue;
                    } else {
                        v_reuseFailAlloc_4300_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_4300_, 0, v___x_4297_);
                        v___x_4299_ = v_reuseFailAlloc_4300_;
                        state = 9;
                        continue;
                    }
                }
            }
            6 => {
                v___x_4285_ = l_Lean_LocalDecl_fvarId(v_localDecl_4237_);
                v___x_4286_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_4286_, 0, v___x_4285_);
                lean_ctor_set(v___x_4286_, 1, v_val_4258_);
                v___x_4287_ = lean_array_push(v_indCandidates_4280_, v___x_4286_);
                if v_isShared_4284_ == 0 {
                    lean_ctor_set(v___x_4283_, 4, v___x_4287_);
                    v___x_4289_ = v___x_4283_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_4295_ = lean_alloc_ctor(0, 6, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4295_, 0, v_allConsts_4276_);
                    lean_ctor_set(v_reuseFailAlloc_4295_, 1, v_unfoldCandidates_4277_);
                    lean_ctor_set(v_reuseFailAlloc_4295_, 2, v_eqnCandidates_4278_);
                    lean_ctor_set(v_reuseFailAlloc_4295_, 3, v_funIndCandidates_4279_);
                    lean_ctor_set(v_reuseFailAlloc_4295_, 4, v___x_4287_);
                    lean_ctor_set(v_reuseFailAlloc_4295_, 5, v_libSearchResults_4281_);
                    v___x_4289_ = v_reuseFailAlloc_4295_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                v___x_4290_ = lean_st_ref_set(v_a_4239_, v___x_4289_);
                v___x_4291_ = lean_box(0);
                if v_isShared_4273_ == 0 {
                    lean_ctor_set(v___x_4272_, 0, v___x_4291_);
                    v___x_4293_ = v___x_4272_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_4294_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4294_, 0, v___x_4291_);
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
                    v_reuseFailAlloc_4308_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4308_, 0, v_a_4302_);
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
                    v_reuseFailAlloc_4322_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4322_, 0, v_a_4316_);
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
                    v_reuseFailAlloc_4335_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4335_, 0, v_a_4329_);
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
    mut v_localDecl_4337_: *mut LeanObject,
    mut v_a_4338_: *mut LeanObject,
    mut v_a_4339_: *mut LeanObject,
    mut v_a_4340_: *mut LeanObject,
    mut v_a_4341_: *mut LeanObject,
    mut v_a_4342_: *mut LeanObject,
    mut v_a_4343_: *mut LeanObject,
    mut v_a_4344_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4345_: *mut LeanObject = core::ptr::null_mut();
    v_res_4345_ = l_Lean_Meta_Try_Collector_checkInductive(
        v_localDecl_4337_,
        v_a_4338_,
        v_a_4339_,
        v_a_4340_,
        v_a_4341_,
        v_a_4342_,
        v_a_4343_,
    );
    lean_dec(v_a_4343_);
    lean_dec_ref(v_a_4342_);
    lean_dec(v_a_4341_);
    lean_dec_ref(v_a_4340_);
    lean_dec(v_a_4339_);
    lean_dec_ref(v_a_4338_);
    lean_dec_ref(v_localDecl_4337_);
    return v_res_4345_;
}
pub unsafe fn l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Try_Collector_checkInductive_spec__0_spec__0(
    mut v_00_u03b1_4346_: *mut LeanObject,
    mut v_constName_4347_: *mut LeanObject,
    mut v___y_4348_: *mut LeanObject,
    mut v___y_4349_: *mut LeanObject,
    mut v___y_4350_: *mut LeanObject,
    mut v___y_4351_: *mut LeanObject,
    mut v___y_4352_: *mut LeanObject,
    mut v___y_4353_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4355_: *mut LeanObject = core::ptr::null_mut();
    v___x_4355_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Try_Collector_checkInductive_spec__0_spec__0___redArg(v_constName_4347_, v___y_4348_, v___y_4349_, v___y_4350_, v___y_4351_, v___y_4352_, v___y_4353_);
    return v___x_4355_;
}
pub unsafe fn l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Try_Collector_checkInductive_spec__0_spec__0___boxed(
    mut v_00_u03b1_4356_: *mut LeanObject,
    mut v_constName_4357_: *mut LeanObject,
    mut v___y_4358_: *mut LeanObject,
    mut v___y_4359_: *mut LeanObject,
    mut v___y_4360_: *mut LeanObject,
    mut v___y_4361_: *mut LeanObject,
    mut v___y_4362_: *mut LeanObject,
    mut v___y_4363_: *mut LeanObject,
    mut v___y_4364_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4365_: *mut LeanObject = core::ptr::null_mut();
    v_res_4365_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Try_Collector_checkInductive_spec__0_spec__0(v_00_u03b1_4356_, v_constName_4357_, v___y_4358_, v___y_4359_, v___y_4360_, v___y_4361_, v___y_4362_, v___y_4363_);
    lean_dec(v___y_4363_);
    lean_dec_ref(v___y_4362_);
    lean_dec(v___y_4361_);
    lean_dec_ref(v___y_4360_);
    lean_dec(v___y_4359_);
    lean_dec_ref(v___y_4358_);
    return v_res_4365_;
}
pub unsafe fn l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Try_Collector_checkInductive_spec__0_spec__0_spec__1(
    mut v_00_u03b1_4366_: *mut LeanObject,
    mut v_ref_4367_: *mut LeanObject,
    mut v_constName_4368_: *mut LeanObject,
    mut v___y_4369_: *mut LeanObject,
    mut v___y_4370_: *mut LeanObject,
    mut v___y_4371_: *mut LeanObject,
    mut v___y_4372_: *mut LeanObject,
    mut v___y_4373_: *mut LeanObject,
    mut v___y_4374_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4376_: *mut LeanObject = core::ptr::null_mut();
    v___x_4376_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Try_Collector_checkInductive_spec__0_spec__0_spec__1___redArg(v_ref_4367_, v_constName_4368_, v___y_4369_, v___y_4370_, v___y_4371_, v___y_4372_, v___y_4373_, v___y_4374_);
    return v___x_4376_;
}
pub unsafe fn l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Try_Collector_checkInductive_spec__0_spec__0_spec__1___boxed(
    mut v_00_u03b1_4377_: *mut LeanObject,
    mut v_ref_4378_: *mut LeanObject,
    mut v_constName_4379_: *mut LeanObject,
    mut v___y_4380_: *mut LeanObject,
    mut v___y_4381_: *mut LeanObject,
    mut v___y_4382_: *mut LeanObject,
    mut v___y_4383_: *mut LeanObject,
    mut v___y_4384_: *mut LeanObject,
    mut v___y_4385_: *mut LeanObject,
    mut v___y_4386_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4387_: *mut LeanObject = core::ptr::null_mut();
    v_res_4387_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Try_Collector_checkInductive_spec__0_spec__0_spec__1(v_00_u03b1_4377_, v_ref_4378_, v_constName_4379_, v___y_4380_, v___y_4381_, v___y_4382_, v___y_4383_, v___y_4384_, v___y_4385_);
    lean_dec(v___y_4385_);
    lean_dec_ref(v___y_4384_);
    lean_dec(v___y_4383_);
    lean_dec_ref(v___y_4382_);
    lean_dec(v___y_4381_);
    lean_dec_ref(v___y_4380_);
    lean_dec(v_ref_4378_);
    return v_res_4387_;
}
pub unsafe fn l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Try_Collector_checkInductive_spec__0_spec__0_spec__1_spec__2(
    mut v_00_u03b1_4388_: *mut LeanObject,
    mut v_ref_4389_: *mut LeanObject,
    mut v_msg_4390_: *mut LeanObject,
    mut v_declHint_4391_: *mut LeanObject,
    mut v___y_4392_: *mut LeanObject,
    mut v___y_4393_: *mut LeanObject,
    mut v___y_4394_: *mut LeanObject,
    mut v___y_4395_: *mut LeanObject,
    mut v___y_4396_: *mut LeanObject,
    mut v___y_4397_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4399_: *mut LeanObject = core::ptr::null_mut();
    v___x_4399_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Try_Collector_checkInductive_spec__0_spec__0_spec__1_spec__2___redArg(v_ref_4389_, v_msg_4390_, v_declHint_4391_, v___y_4392_, v___y_4393_, v___y_4394_, v___y_4395_, v___y_4396_, v___y_4397_);
    return v___x_4399_;
}
pub unsafe fn l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Try_Collector_checkInductive_spec__0_spec__0_spec__1_spec__2___boxed(
    mut v_00_u03b1_4400_: *mut LeanObject,
    mut v_ref_4401_: *mut LeanObject,
    mut v_msg_4402_: *mut LeanObject,
    mut v_declHint_4403_: *mut LeanObject,
    mut v___y_4404_: *mut LeanObject,
    mut v___y_4405_: *mut LeanObject,
    mut v___y_4406_: *mut LeanObject,
    mut v___y_4407_: *mut LeanObject,
    mut v___y_4408_: *mut LeanObject,
    mut v___y_4409_: *mut LeanObject,
    mut v___y_4410_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4411_: *mut LeanObject = core::ptr::null_mut();
    v_res_4411_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Try_Collector_checkInductive_spec__0_spec__0_spec__1_spec__2(v_00_u03b1_4400_, v_ref_4401_, v_msg_4402_, v_declHint_4403_, v___y_4404_, v___y_4405_, v___y_4406_, v___y_4407_, v___y_4408_, v___y_4409_);
    lean_dec(v___y_4409_);
    lean_dec_ref(v___y_4408_);
    lean_dec(v___y_4407_);
    lean_dec_ref(v___y_4406_);
    lean_dec(v___y_4405_);
    lean_dec_ref(v___y_4404_);
    lean_dec(v_ref_4401_);
    return v_res_4411_;
}
pub unsafe fn l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Try_Collector_checkInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4(
    mut v_msg_4412_: *mut LeanObject,
    mut v_declHint_4413_: *mut LeanObject,
    mut v___y_4414_: *mut LeanObject,
    mut v___y_4415_: *mut LeanObject,
    mut v___y_4416_: *mut LeanObject,
    mut v___y_4417_: *mut LeanObject,
    mut v___y_4418_: *mut LeanObject,
    mut v___y_4419_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4421_: *mut LeanObject = core::ptr::null_mut();
    v___x_4421_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Try_Collector_checkInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg(v_msg_4412_, v_declHint_4413_, v___y_4419_);
    return v___x_4421_;
}
pub unsafe fn l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Try_Collector_checkInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___boxed(
    mut v_msg_4422_: *mut LeanObject,
    mut v_declHint_4423_: *mut LeanObject,
    mut v___y_4424_: *mut LeanObject,
    mut v___y_4425_: *mut LeanObject,
    mut v___y_4426_: *mut LeanObject,
    mut v___y_4427_: *mut LeanObject,
    mut v___y_4428_: *mut LeanObject,
    mut v___y_4429_: *mut LeanObject,
    mut v___y_4430_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4431_: *mut LeanObject = core::ptr::null_mut();
    v_res_4431_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Try_Collector_checkInductive_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4(v_msg_4422_, v_declHint_4423_, v___y_4424_, v___y_4425_, v___y_4426_, v___y_4427_, v___y_4428_, v___y_4429_);
    lean_dec(v___y_4429_);
    lean_dec_ref(v___y_4428_);
    lean_dec(v___y_4427_);
    lean_dec_ref(v___y_4426_);
    lean_dec(v___y_4425_);
    lean_dec_ref(v___y_4424_);
    return v_res_4431_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Try_Collector_checkInductive_spec__0_spec__0_spec__1_spec__2_spec__4(
    mut v_00_u03b1_4432_: *mut LeanObject,
    mut v_ref_4433_: *mut LeanObject,
    mut v_msg_4434_: *mut LeanObject,
    mut v___y_4435_: *mut LeanObject,
    mut v___y_4436_: *mut LeanObject,
    mut v___y_4437_: *mut LeanObject,
    mut v___y_4438_: *mut LeanObject,
    mut v___y_4439_: *mut LeanObject,
    mut v___y_4440_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4442_: *mut LeanObject = core::ptr::null_mut();
    v___x_4442_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Try_Collector_checkInductive_spec__0_spec__0_spec__1_spec__2_spec__4___redArg(v_ref_4433_, v_msg_4434_, v___y_4435_, v___y_4436_, v___y_4437_, v___y_4438_, v___y_4439_, v___y_4440_);
    return v___x_4442_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Try_Collector_checkInductive_spec__0_spec__0_spec__1_spec__2_spec__4___boxed(
    mut v_00_u03b1_4443_: *mut LeanObject,
    mut v_ref_4444_: *mut LeanObject,
    mut v_msg_4445_: *mut LeanObject,
    mut v___y_4446_: *mut LeanObject,
    mut v___y_4447_: *mut LeanObject,
    mut v___y_4448_: *mut LeanObject,
    mut v___y_4449_: *mut LeanObject,
    mut v___y_4450_: *mut LeanObject,
    mut v___y_4451_: *mut LeanObject,
    mut v___y_4452_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4453_: *mut LeanObject = core::ptr::null_mut();
    v_res_4453_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Try_Collector_checkInductive_spec__0_spec__0_spec__1_spec__2_spec__4(v_00_u03b1_4443_, v_ref_4444_, v_msg_4445_, v___y_4446_, v___y_4447_, v___y_4448_, v___y_4449_, v___y_4450_, v___y_4451_);
    lean_dec(v___y_4451_);
    lean_dec_ref(v___y_4450_);
    lean_dec(v___y_4449_);
    lean_dec_ref(v___y_4448_);
    lean_dec(v___y_4447_);
    lean_dec_ref(v___y_4446_);
    lean_dec(v_ref_4444_);
    return v_res_4453_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Try_Collector_checkInductive_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6(
    mut v_00_u03b1_4454_: *mut LeanObject,
    mut v_msg_4455_: *mut LeanObject,
    mut v___y_4456_: *mut LeanObject,
    mut v___y_4457_: *mut LeanObject,
    mut v___y_4458_: *mut LeanObject,
    mut v___y_4459_: *mut LeanObject,
    mut v___y_4460_: *mut LeanObject,
    mut v___y_4461_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4463_: *mut LeanObject = core::ptr::null_mut();
    v___x_4463_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Try_Collector_checkInductive_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6___redArg(v_msg_4455_, v___y_4458_, v___y_4459_, v___y_4460_, v___y_4461_);
    return v___x_4463_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Try_Collector_checkInductive_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6___boxed(
    mut v_00_u03b1_4464_: *mut LeanObject,
    mut v_msg_4465_: *mut LeanObject,
    mut v___y_4466_: *mut LeanObject,
    mut v___y_4467_: *mut LeanObject,
    mut v___y_4468_: *mut LeanObject,
    mut v___y_4469_: *mut LeanObject,
    mut v___y_4470_: *mut LeanObject,
    mut v___y_4471_: *mut LeanObject,
    mut v___y_4472_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4473_: *mut LeanObject = core::ptr::null_mut();
    v_res_4473_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_Try_Collector_checkInductive_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6(v_00_u03b1_4464_, v_msg_4465_, v___y_4466_, v___y_4467_, v___y_4468_, v___y_4469_, v___y_4470_, v___y_4471_);
    lean_dec(v___y_4471_);
    lean_dec_ref(v___y_4470_);
    lean_dec(v___y_4469_);
    lean_dec_ref(v___y_4468_);
    lean_dec(v___y_4467_);
    lean_dec_ref(v___y_4466_);
    return v_res_4473_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Try_Collector_visit_spec__1_spec__1___redArg(
    mut v_a_4474_: *mut LeanObject,
    mut v_x_4475_: *mut LeanObject,
) -> u8 {
    let mut v___x_4476_: u8 = 0;
    let mut v_key_4477_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_4478_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4479_: usize = 0;
    let mut v___x_4480_: usize = 0;
    let mut v___x_4481_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_4475_) == 0 {
                    v___x_4476_ = 0;
                    return v___x_4476_;
                } else {
                    v_key_4477_ = lean_ctor_get(v_x_4475_, 0);
                    v_tail_4478_ = lean_ctor_get(v_x_4475_, 2);
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
    mut v_a_4483_: *mut LeanObject,
    mut v_x_4484_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4485_: u8 = 0;
    let mut v_r_4486_: *mut LeanObject = core::ptr::null_mut();
    v_res_4485_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Try_Collector_visit_spec__1_spec__1___redArg(v_a_4483_, v_x_4484_);
    lean_dec(v_x_4484_);
    lean_dec_ref(v_a_4483_);
    v_r_4486_ = lean_box((v_res_4485_) as usize);
    return v_r_4486_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Try_Collector_visit_spec__1___redArg(
    mut v_m_4487_: *mut LeanObject,
    mut v_a_4488_: *mut LeanObject,
) -> u8 {
    let mut v_buckets_4489_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4490_: *mut LeanObject = core::ptr::null_mut();
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
    let mut v___x_4506_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4507_: u8 = 0;
    v_buckets_4489_ = lean_ctor_get(v_m_4487_, 1);
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
    mut v_m_4508_: *mut LeanObject,
    mut v_a_4509_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4510_: u8 = 0;
    let mut v_r_4511_: *mut LeanObject = core::ptr::null_mut();
    v_res_4510_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Try_Collector_visit_spec__1___redArg(v_m_4508_, v_a_4509_);
    lean_dec_ref(v_a_4509_);
    lean_dec_ref(v_m_4508_);
    v_r_4511_ = lean_box((v_res_4510_) as usize);
    return v_r_4511_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Try_Collector_visit_spec__2_spec__3_spec__4_spec__6___redArg(
    mut v_x_4512_: *mut LeanObject,
    mut v_x_4513_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_key_4514_: *mut LeanObject = core::ptr::null_mut();
    let mut v_value_4515_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_4516_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4518_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4519_: u8 = 0;
    let mut v___x_4520_: *mut LeanObject = core::ptr::null_mut();
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
    let mut v___x_4536_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4538_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4539_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4541_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4542_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_4513_) == 0 {
                    return v_x_4512_;
                } else {
                    v_key_4514_ = lean_ctor_get(v_x_4513_, 0);
                    v_value_4515_ = lean_ctor_get(v_x_4513_, 1);
                    v_tail_4516_ = lean_ctor_get(v_x_4513_, 2);
                    v_isSharedCheck_4542_ = (!lean_is_exclusive(v_x_4513_)) as u8;
                    if v_isSharedCheck_4542_ == 0 {
                        v___x_4518_ = v_x_4513_;
                        v_isShared_4519_ = v_isSharedCheck_4542_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_tail_4516_);
                        lean_inc(v_value_4515_);
                        lean_inc(v_key_4514_);
                        lean_dec(v_x_4513_);
                        v___x_4518_ = lean_box(0);
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
                lean_inc(v___x_4536_);
                if v_isShared_4519_ == 0 {
                    lean_ctor_set(v___x_4518_, 2, v___x_4536_);
                    v___x_4538_ = v___x_4518_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4541_ = lean_alloc_ctor(1, 3, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4541_, 0, v_key_4514_);
                    lean_ctor_set(v_reuseFailAlloc_4541_, 1, v_value_4515_);
                    lean_ctor_set(v_reuseFailAlloc_4541_, 2, v___x_4536_);
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
    mut v_i_4543_: *mut LeanObject,
    mut v_source_4544_: *mut LeanObject,
    mut v_target_4545_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4546_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4547_: u8 = 0;
    let mut v_es_4548_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4549_: *mut LeanObject = core::ptr::null_mut();
    let mut v_source_4550_: *mut LeanObject = core::ptr::null_mut();
    let mut v_target_4551_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4552_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4553_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4546_ = lean_array_get_size(v_source_4544_);
                v___x_4547_ = lean_nat_dec_lt(v_i_4543_, v___x_4546_);
                if v___x_4547_ == 0 {
                    lean_dec_ref(v_source_4544_);
                    lean_dec(v_i_4543_);
                    return v_target_4545_;
                } else {
                    v_es_4548_ = lean_array_fget(v_source_4544_, v_i_4543_);
                    v___x_4549_ = lean_box(0);
                    v_source_4550_ = lean_array_fset(v_source_4544_, v_i_4543_, v___x_4549_);
                    v_target_4551_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Try_Collector_visit_spec__2_spec__3_spec__4_spec__6___redArg(v_target_4545_, v_es_4548_);
                    v___x_4552_ = lean_unsigned_to_nat(1);
                    v___x_4553_ = lean_nat_add(v_i_4543_, v___x_4552_);
                    lean_dec(v_i_4543_);
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
    mut v_data_4555_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4556_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4557_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nbuckets_4558_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4559_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4560_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4561_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4562_: *mut LeanObject = core::ptr::null_mut();
    v___x_4556_ = lean_array_get_size(v_data_4555_);
    v___x_4557_ = lean_unsigned_to_nat(2);
    v_nbuckets_4558_ = lean_nat_mul(v___x_4556_, v___x_4557_);
    v___x_4559_ = lean_unsigned_to_nat(0);
    v___x_4560_ = lean_box(0);
    v___x_4561_ = lean_mk_array(v_nbuckets_4558_, v___x_4560_);
    v___x_4562_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Try_Collector_visit_spec__2_spec__3_spec__4___redArg(v___x_4559_, v_data_4555_, v___x_4561_);
    return v___x_4562_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Try_Collector_visit_spec__2___redArg(
    mut v_m_4563_: *mut LeanObject,
    mut v_a_4564_: *mut LeanObject,
    mut v_b_4565_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_size_4566_: *mut LeanObject = core::ptr::null_mut();
    let mut v_buckets_4567_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4568_: *mut LeanObject = core::ptr::null_mut();
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
    let mut v_bkt_4584_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4585_: u8 = 0;
    let mut v___x_4587_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4588_: u8 = 0;
    let mut v___x_4589_: *mut LeanObject = core::ptr::null_mut();
    let mut v_size_x27_4590_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4591_: *mut LeanObject = core::ptr::null_mut();
    let mut v_buckets_x27_4592_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4593_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4594_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4595_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4596_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4597_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4598_: u8 = 0;
    let mut v_val_4599_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4601_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4602_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4604_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4605_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4606_: u8 = 0;
    let mut v_unused_4607_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_4608_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_size_4566_ = lean_ctor_get(v_m_4563_, 0);
                v_buckets_4567_ = lean_ctor_get(v_m_4563_, 1);
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
                    lean_inc_ref(v_buckets_4567_);
                    lean_inc(v_size_4566_);
                    v_isSharedCheck_4606_ = (!lean_is_exclusive(v_m_4563_)) as u8;
                    if v_isSharedCheck_4606_ == 0 {
                        v_unused_4607_ = lean_ctor_get(v_m_4563_, 1);
                        lean_dec(v_unused_4607_);
                        v_unused_4608_ = lean_ctor_get(v_m_4563_, 0);
                        lean_dec(v_unused_4608_);
                        v___x_4587_ = v_m_4563_;
                        v_isShared_4588_ = v_isSharedCheck_4606_;
                        state = 1;
                        continue;
                    } else {
                        lean_dec(v_m_4563_);
                        v___x_4587_ = lean_box(0);
                        v_isShared_4588_ = v_isSharedCheck_4606_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec(v_b_4565_);
                    lean_dec_ref(v_a_4564_);
                    return v_m_4563_;
                }
            }
            1 => {
                v___x_4589_ = lean_unsigned_to_nat(1);
                v_size_x27_4590_ = lean_nat_add(v_size_4566_, v___x_4589_);
                lean_dec(v_size_4566_);
                lean_inc(v_bkt_4584_);
                v___x_4591_ = lean_alloc_ctor(1, 3, (0) as u32);
                lean_ctor_set(v___x_4591_, 0, v_a_4564_);
                lean_ctor_set(v___x_4591_, 1, v_b_4565_);
                lean_ctor_set(v___x_4591_, 2, v_bkt_4584_);
                v_buckets_x27_4592_ = lean_array_uset(v_buckets_4567_, v___x_4583_, v___x_4591_);
                v___x_4593_ = lean_unsigned_to_nat(4);
                v___x_4594_ = lean_nat_mul(v_size_x27_4590_, v___x_4593_);
                v___x_4595_ = lean_unsigned_to_nat(3);
                v___x_4596_ = lean_nat_div(v___x_4594_, v___x_4595_);
                lean_dec(v___x_4594_);
                v___x_4597_ = lean_array_get_size(v_buckets_x27_4592_);
                v___x_4598_ = lean_nat_dec_le(v___x_4596_, v___x_4597_);
                lean_dec(v___x_4596_);
                if v___x_4598_ == 0 {
                    v_val_4599_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Try_Collector_visit_spec__2_spec__3___redArg(v_buckets_x27_4592_);
                    if v_isShared_4588_ == 0 {
                        lean_ctor_set(v___x_4587_, 1, v_val_4599_);
                        lean_ctor_set(v___x_4587_, 0, v_size_x27_4590_);
                        v___x_4601_ = v___x_4587_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_4602_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_4602_, 0, v_size_x27_4590_);
                        lean_ctor_set(v_reuseFailAlloc_4602_, 1, v_val_4599_);
                        v___x_4601_ = v_reuseFailAlloc_4602_;
                        state = 2;
                        continue;
                    }
                } else {
                    if v_isShared_4588_ == 0 {
                        lean_ctor_set(v___x_4587_, 1, v_buckets_x27_4592_);
                        lean_ctor_set(v___x_4587_, 0, v_size_x27_4590_);
                        v___x_4604_ = v___x_4587_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_4605_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_4605_, 0, v_size_x27_4590_);
                        lean_ctor_set(v_reuseFailAlloc_4605_, 1, v_buckets_x27_4592_);
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
pub unsafe fn _init_l_Lean_Meta_Try_Collector_visit___closed__0() -> *mut LeanObject {
    let mut v___x_4609_: *mut LeanObject = core::ptr::null_mut();
    let mut v_dummy_4610_: *mut LeanObject = core::ptr::null_mut();
    v___x_4609_ = lean_box(0);
    v_dummy_4610_ = l_Lean_Expr_sort___override(v___x_4609_);
    return v_dummy_4610_;
}
pub unsafe fn l_Lean_Expr_withAppAux___at___00Lean_Meta_Try_Collector_visit_spec__3(
    mut v_e_4611_: *mut LeanObject,
    mut v_x_4612_: *mut LeanObject,
    mut v_x_4613_: *mut LeanObject,
    mut v_x_4614_: *mut LeanObject,
    mut v___y_4615_: *mut LeanObject,
    mut v___y_4616_: *mut LeanObject,
    mut v___y_4617_: *mut LeanObject,
    mut v___y_4618_: *mut LeanObject,
    mut v___y_4619_: *mut LeanObject,
    mut v___y_4620_: *mut LeanObject,
    mut v___y_4621_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___y_4624_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4625_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4626_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4627_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4628_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4629_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4630_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4631_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4632_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4633_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4634_: u8 = 0;
    let mut v___x_4635_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4636_: u8 = 0;
    let mut v___x_4637_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4638_: usize = 0;
    let mut v___x_4639_: usize = 0;
    let mut v___x_4640_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4641_: usize = 0;
    let mut v___x_4642_: usize = 0;
    let mut v___x_4643_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fn_4644_: *mut LeanObject = core::ptr::null_mut();
    let mut v_arg_4645_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4646_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4647_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4648_: *mut LeanObject = core::ptr::null_mut();
    let mut v_declName_4650_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4651_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4652_: u8 = 0;
    let mut v___x_4653_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4654_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_4612_) == 5 {
                    v_fn_4644_ = lean_ctor_get(v_x_4612_, 0);
                    lean_inc_ref(v_fn_4644_);
                    v_arg_4645_ = lean_ctor_get(v_x_4612_, 1);
                    lean_inc_ref(v_arg_4645_);
                    lean_dec_ref_known(v_x_4612_, 2);
                    v___x_4646_ = lean_array_set(v_x_4613_, v_x_4614_, v_arg_4645_);
                    v___x_4647_ = lean_unsigned_to_nat(1);
                    v___x_4648_ = lean_nat_sub(v_x_4614_, v___x_4647_);
                    lean_dec(v_x_4614_);
                    v_x_4612_ = v_fn_4644_;
                    v_x_4613_ = v___x_4646_;
                    v_x_4614_ = v___x_4648_;
                    state = 0;
                    continue;
                } else {
                    lean_dec(v_x_4614_);
                    if lean_obj_tag(v_x_4612_) == 4 {
                        v_declName_4650_ = lean_ctor_get(v_x_4612_, 0);
                        lean_inc_n(v_declName_4650_, 2);
                        lean_dec_ref_known(v_x_4612_, 2);
                        v___x_4651_ = l_Lean_Meta_Try_Collector_saveConst___redArg(
                            v_declName_4650_,
                            v___y_4617_,
                        );
                        lean_dec_ref(v___x_4651_);
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
                            if lean_obj_tag(v___x_4653_) == 0 {
                                lean_dec_ref_known(v___x_4653_, 1);
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
                                lean_dec_ref(v_x_4613_);
                                return v___x_4653_;
                            }
                        } else {
                            lean_dec(v_declName_4650_);
                            lean_dec_ref(v_e_4611_);
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
                        lean_dec_ref(v_e_4611_);
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
                        if lean_obj_tag(v___x_4654_) == 0 {
                            lean_dec_ref_known(v___x_4654_, 1);
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
                            lean_dec_ref(v_x_4613_);
                            return v___x_4654_;
                        }
                    }
                }
            }
            1 => {
                v___x_4631_ = lean_unsigned_to_nat(0);
                v___x_4632_ = lean_array_get_size(v_x_4613_);
                v___x_4633_ = lean_box(0);
                v___x_4634_ = lean_nat_dec_lt(v___x_4631_, v___x_4632_);
                if v___x_4634_ == 0 {
                    lean_dec_ref(v_x_4613_);
                    v___x_4635_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_4635_, 0, v___x_4633_);
                    return v___x_4635_;
                } else {
                    v___x_4636_ = lean_nat_dec_le(v___x_4632_, v___x_4632_);
                    if v___x_4636_ == 0 {
                        if v___x_4634_ == 0 {
                            lean_dec_ref(v_x_4613_);
                            v___x_4637_ = lean_alloc_ctor(0, 1, (0) as u32);
                            lean_ctor_set(v___x_4637_, 0, v___x_4633_);
                            return v___x_4637_;
                        } else {
                            v___x_4638_ = 0usize;
                            v___x_4639_ = lean_usize_of_nat(v___x_4632_);
                            v___x_4640_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Try_Collector_visit_spec__0(v_x_4613_, v___x_4638_, v___x_4639_, v___x_4633_, v___y_4624_, v___y_4625_, v___y_4626_, v___y_4627_, v___y_4628_, v___y_4629_, v___y_4630_);
                            lean_dec_ref(v_x_4613_);
                            return v___x_4640_;
                        }
                    } else {
                        v___x_4641_ = 0usize;
                        v___x_4642_ = lean_usize_of_nat(v___x_4632_);
                        v___x_4643_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Try_Collector_visit_spec__0(v_x_4613_, v___x_4641_, v___x_4642_, v___x_4633_, v___y_4624_, v___y_4625_, v___y_4626_, v___y_4627_, v___y_4628_, v___y_4629_, v___y_4630_);
                        lean_dec_ref(v_x_4613_);
                        return v___x_4643_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Try_Collector_visit(
    mut v_e_4655_: *mut LeanObject,
    mut v_a_4656_: *mut LeanObject,
    mut v_a_4657_: *mut LeanObject,
    mut v_a_4658_: *mut LeanObject,
    mut v_a_4659_: *mut LeanObject,
    mut v_a_4660_: *mut LeanObject,
    mut v_a_4661_: *mut LeanObject,
    mut v_a_4662_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4664_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4665_: u8 = 0;
    let mut v___x_4666_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4667_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4668_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4669_: *mut LeanObject = core::ptr::null_mut();
    let mut v_d_4671_: *mut LeanObject = core::ptr::null_mut();
    let mut v_b_4672_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4673_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4674_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4675_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4676_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4677_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4678_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4679_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4680_: *mut LeanObject = core::ptr::null_mut();
    let mut v_declName_4682_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4683_: *mut LeanObject = core::ptr::null_mut();
    let mut v_binderType_4684_: *mut LeanObject = core::ptr::null_mut();
    let mut v_body_4685_: *mut LeanObject = core::ptr::null_mut();
    let mut v_binderType_4686_: *mut LeanObject = core::ptr::null_mut();
    let mut v_body_4687_: *mut LeanObject = core::ptr::null_mut();
    let mut v_expr_4688_: *mut LeanObject = core::ptr::null_mut();
    let mut v_type_4690_: *mut LeanObject = core::ptr::null_mut();
    let mut v_value_4691_: *mut LeanObject = core::ptr::null_mut();
    let mut v_body_4692_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4693_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4694_: *mut LeanObject = core::ptr::null_mut();
    let mut v_dummy_4696_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nargs_4697_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4698_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4699_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4700_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4701_: *mut LeanObject = core::ptr::null_mut();
    let mut v_struct_4702_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4704_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4705_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4706_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4664_ = lean_st_ref_get(v_a_4656_);
                v___x_4665_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Try_Collector_visit_spec__1___redArg(v___x_4664_, v_e_4655_);
                lean_dec(v___x_4664_);
                if v___x_4665_ == 0 {
                    v___x_4666_ = lean_st_ref_take(v_a_4656_);
                    v___x_4667_ = lean_box(0);
                    lean_inc_ref(v_e_4655_);
                    v___x_4668_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Try_Collector_visit_spec__2___redArg(v___x_4666_, v_e_4655_, v___x_4667_);
                    v___x_4669_ = lean_st_ref_set(v_a_4656_, v___x_4668_);
                    match lean_obj_tag(v_e_4655_) {
                        4 => {
                            v_declName_4682_ = lean_ctor_get(v_e_4655_, 0);
                            lean_inc(v_declName_4682_);
                            lean_dec_ref_known(v_e_4655_, 2);
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
                            v_binderType_4684_ = lean_ctor_get(v_e_4655_, 1);
                            lean_inc_ref(v_binderType_4684_);
                            v_body_4685_ = lean_ctor_get(v_e_4655_, 2);
                            lean_inc_ref(v_body_4685_);
                            lean_dec_ref_known(v_e_4655_, 3);
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
                            v_binderType_4686_ = lean_ctor_get(v_e_4655_, 1);
                            lean_inc_ref(v_binderType_4686_);
                            v_body_4687_ = lean_ctor_get(v_e_4655_, 2);
                            lean_inc_ref(v_body_4687_);
                            lean_dec_ref_known(v_e_4655_, 3);
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
                            v_expr_4688_ = lean_ctor_get(v_e_4655_, 1);
                            lean_inc_ref(v_expr_4688_);
                            lean_dec_ref_known(v_e_4655_, 2);
                            v_e_4655_ = v_expr_4688_;
                            state = 0;
                            continue;
                        }
                        8 => {
                            v_type_4690_ = lean_ctor_get(v_e_4655_, 1);
                            lean_inc_ref(v_type_4690_);
                            v_value_4691_ = lean_ctor_get(v_e_4655_, 2);
                            lean_inc_ref(v_value_4691_);
                            v_body_4692_ = lean_ctor_get(v_e_4655_, 3);
                            lean_inc_ref(v_body_4692_);
                            lean_dec_ref_known(v_e_4655_, 4);
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
                            if lean_obj_tag(v___x_4693_) == 0 {
                                lean_dec_ref_known(v___x_4693_, 1);
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
                                if lean_obj_tag(v___x_4694_) == 0 {
                                    lean_dec_ref_known(v___x_4694_, 1);
                                    v_e_4655_ = v_body_4692_;
                                    state = 0;
                                    continue;
                                } else {
                                    lean_dec_ref(v_body_4692_);
                                    return v___x_4694_;
                                }
                            } else {
                                lean_dec_ref(v_body_4692_);
                                lean_dec_ref(v_value_4691_);
                                return v___x_4693_;
                            }
                        }
                        5 => {
                            v_dummy_4696_ = lean_obj_once(
                                core::ptr::addr_of_mut!(
                                    l_Lean_Meta_Try_Collector_visit___closed__0
                                ),
                                core::ptr::addr_of_mut!(
                                    l_Lean_Meta_Try_Collector_visit___closed__0_once
                                ),
                                _init_l_Lean_Meta_Try_Collector_visit___closed__0,
                            );
                            v_nargs_4697_ = l_Lean_Expr_getAppNumArgs(v_e_4655_);
                            lean_inc(v_nargs_4697_);
                            v___x_4698_ = lean_mk_array(v_nargs_4697_, v_dummy_4696_);
                            v___x_4699_ = lean_unsigned_to_nat(1);
                            v___x_4700_ = lean_nat_sub(v_nargs_4697_, v___x_4699_);
                            lean_dec(v_nargs_4697_);
                            lean_inc_ref(v_e_4655_);
                            v___x_4701_ = l_Lean_Expr_withAppAux___at___00Lean_Meta_Try_Collector_visit_spec__3(v_e_4655_, v_e_4655_, v___x_4698_, v___x_4700_, v_a_4656_, v_a_4657_, v_a_4658_, v_a_4659_, v_a_4660_, v_a_4661_, v_a_4662_);
                            return v___x_4701_;
                        }
                        11 => {
                            v_struct_4702_ = lean_ctor_get(v_e_4655_, 2);
                            lean_inc_ref(v_struct_4702_);
                            lean_dec_ref_known(v_e_4655_, 3);
                            v_e_4655_ = v_struct_4702_;
                            state = 0;
                            continue;
                        }
                        _ => {
                            lean_dec_ref(v_e_4655_);
                            v___x_4704_ = lean_alloc_ctor(0, 1, (0) as u32);
                            lean_ctor_set(v___x_4704_, 0, v___x_4667_);
                            return v___x_4704_;
                        }
                    }
                } else {
                    lean_dec_ref(v_e_4655_);
                    v___x_4705_ = lean_box(0);
                    v___x_4706_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_4706_, 0, v___x_4705_);
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
                if lean_obj_tag(v___x_4680_) == 0 {
                    lean_dec_ref_known(v___x_4680_, 1);
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
                    lean_dec_ref(v_b_4672_);
                    return v___x_4680_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Try_Collector_visit_spec__0(
    mut v_as_4707_: *mut LeanObject,
    mut v_i_4708_: usize,
    mut v_stop_4709_: usize,
    mut v_b_4710_: *mut LeanObject,
    mut v___y_4711_: *mut LeanObject,
    mut v___y_4712_: *mut LeanObject,
    mut v___y_4713_: *mut LeanObject,
    mut v___y_4714_: *mut LeanObject,
    mut v___y_4715_: *mut LeanObject,
    mut v___y_4716_: *mut LeanObject,
    mut v___y_4717_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4719_: u8 = 0;
    let mut v___x_4720_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4721_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4722_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4723_: usize = 0;
    let mut v___x_4724_: usize = 0;
    let mut v___x_4726_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4719_ = lean_usize_dec_eq(v_i_4708_, v_stop_4709_);
                if v___x_4719_ == 0 {
                    v___x_4720_ = lean_array_uget_borrowed(v_as_4707_, v_i_4708_);
                    lean_inc(v___x_4720_);
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
                    if lean_obj_tag(v___x_4721_) == 0 {
                        v_a_4722_ = lean_ctor_get(v___x_4721_, 0);
                        lean_inc(v_a_4722_);
                        lean_dec_ref_known(v___x_4721_, 1);
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
                    v___x_4726_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_4726_, 0, v_b_4710_);
                    return v___x_4726_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Try_Collector_visit_spec__0___boxed(
    mut v_as_4727_: *mut LeanObject,
    mut v_i_4728_: *mut LeanObject,
    mut v_stop_4729_: *mut LeanObject,
    mut v_b_4730_: *mut LeanObject,
    mut v___y_4731_: *mut LeanObject,
    mut v___y_4732_: *mut LeanObject,
    mut v___y_4733_: *mut LeanObject,
    mut v___y_4734_: *mut LeanObject,
    mut v___y_4735_: *mut LeanObject,
    mut v___y_4736_: *mut LeanObject,
    mut v___y_4737_: *mut LeanObject,
    mut v___y_4738_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_i_boxed_4739_: usize = 0;
    let mut v_stop_boxed_4740_: usize = 0;
    let mut v_res_4741_: *mut LeanObject = core::ptr::null_mut();
    v_i_boxed_4739_ = lean_unbox_usize(v_i_4728_);
    lean_dec(v_i_4728_);
    v_stop_boxed_4740_ = lean_unbox_usize(v_stop_4729_);
    lean_dec(v_stop_4729_);
    v_res_4741_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Try_Collector_visit_spec__0(v_as_4727_, v_i_boxed_4739_, v_stop_boxed_4740_, v_b_4730_, v___y_4731_, v___y_4732_, v___y_4733_, v___y_4734_, v___y_4735_, v___y_4736_, v___y_4737_);
    lean_dec(v___y_4737_);
    lean_dec_ref(v___y_4736_);
    lean_dec(v___y_4735_);
    lean_dec_ref(v___y_4734_);
    lean_dec(v___y_4733_);
    lean_dec_ref(v___y_4732_);
    lean_dec(v___y_4731_);
    lean_dec_ref(v_as_4727_);
    return v_res_4741_;
}
pub unsafe fn l_Lean_Expr_withAppAux___at___00Lean_Meta_Try_Collector_visit_spec__3___boxed(
    mut v_e_4742_: *mut LeanObject,
    mut v_x_4743_: *mut LeanObject,
    mut v_x_4744_: *mut LeanObject,
    mut v_x_4745_: *mut LeanObject,
    mut v___y_4746_: *mut LeanObject,
    mut v___y_4747_: *mut LeanObject,
    mut v___y_4748_: *mut LeanObject,
    mut v___y_4749_: *mut LeanObject,
    mut v___y_4750_: *mut LeanObject,
    mut v___y_4751_: *mut LeanObject,
    mut v___y_4752_: *mut LeanObject,
    mut v___y_4753_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4754_: *mut LeanObject = core::ptr::null_mut();
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
    lean_dec(v___y_4752_);
    lean_dec_ref(v___y_4751_);
    lean_dec(v___y_4750_);
    lean_dec_ref(v___y_4749_);
    lean_dec(v___y_4748_);
    lean_dec_ref(v___y_4747_);
    lean_dec(v___y_4746_);
    return v_res_4754_;
}
pub unsafe fn l_Lean_Meta_Try_Collector_visit___boxed(
    mut v_e_4755_: *mut LeanObject,
    mut v_a_4756_: *mut LeanObject,
    mut v_a_4757_: *mut LeanObject,
    mut v_a_4758_: *mut LeanObject,
    mut v_a_4759_: *mut LeanObject,
    mut v_a_4760_: *mut LeanObject,
    mut v_a_4761_: *mut LeanObject,
    mut v_a_4762_: *mut LeanObject,
    mut v_a_4763_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4764_: *mut LeanObject = core::ptr::null_mut();
    v_res_4764_ = l_Lean_Meta_Try_Collector_visit(
        v_e_4755_, v_a_4756_, v_a_4757_, v_a_4758_, v_a_4759_, v_a_4760_, v_a_4761_, v_a_4762_,
    );
    lean_dec(v_a_4762_);
    lean_dec_ref(v_a_4761_);
    lean_dec(v_a_4760_);
    lean_dec_ref(v_a_4759_);
    lean_dec(v_a_4758_);
    lean_dec_ref(v_a_4757_);
    lean_dec(v_a_4756_);
    return v_res_4764_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Try_Collector_visit_spec__1(
    mut v_00_u03b2_4765_: *mut LeanObject,
    mut v_m_4766_: *mut LeanObject,
    mut v_a_4767_: *mut LeanObject,
) -> u8 {
    let mut v___x_4768_: u8 = 0;
    v___x_4768_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Try_Collector_visit_spec__1___redArg(v_m_4766_, v_a_4767_);
    return v___x_4768_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Try_Collector_visit_spec__1___boxed(
    mut v_00_u03b2_4769_: *mut LeanObject,
    mut v_m_4770_: *mut LeanObject,
    mut v_a_4771_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4772_: u8 = 0;
    let mut v_r_4773_: *mut LeanObject = core::ptr::null_mut();
    v_res_4772_ =
        l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Try_Collector_visit_spec__1(
            v_00_u03b2_4769_,
            v_m_4770_,
            v_a_4771_,
        );
    lean_dec_ref(v_a_4771_);
    lean_dec_ref(v_m_4770_);
    v_r_4773_ = lean_box((v_res_4772_) as usize);
    return v_r_4773_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Try_Collector_visit_spec__2(
    mut v_00_u03b2_4774_: *mut LeanObject,
    mut v_m_4775_: *mut LeanObject,
    mut v_a_4776_: *mut LeanObject,
    mut v_b_4777_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4778_: *mut LeanObject = core::ptr::null_mut();
    v___x_4778_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Try_Collector_visit_spec__2___redArg(v_m_4775_, v_a_4776_, v_b_4777_);
    return v___x_4778_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Try_Collector_visit_spec__1_spec__1(
    mut v_00_u03b2_4779_: *mut LeanObject,
    mut v_a_4780_: *mut LeanObject,
    mut v_x_4781_: *mut LeanObject,
) -> u8 {
    let mut v___x_4782_: u8 = 0;
    v___x_4782_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Try_Collector_visit_spec__1_spec__1___redArg(v_a_4780_, v_x_4781_);
    return v___x_4782_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Try_Collector_visit_spec__1_spec__1___boxed(
    mut v_00_u03b2_4783_: *mut LeanObject,
    mut v_a_4784_: *mut LeanObject,
    mut v_x_4785_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4786_: u8 = 0;
    let mut v_r_4787_: *mut LeanObject = core::ptr::null_mut();
    v_res_4786_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Try_Collector_visit_spec__1_spec__1(v_00_u03b2_4783_, v_a_4784_, v_x_4785_);
    lean_dec(v_x_4785_);
    lean_dec_ref(v_a_4784_);
    v_r_4787_ = lean_box((v_res_4786_) as usize);
    return v_r_4787_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Try_Collector_visit_spec__2_spec__3(
    mut v_00_u03b2_4788_: *mut LeanObject,
    mut v_data_4789_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4790_: *mut LeanObject = core::ptr::null_mut();
    v___x_4790_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Try_Collector_visit_spec__2_spec__3___redArg(v_data_4789_);
    return v___x_4790_;
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Try_Collector_visit_spec__2_spec__3_spec__4(
    mut v_00_u03b2_4791_: *mut LeanObject,
    mut v_i_4792_: *mut LeanObject,
    mut v_source_4793_: *mut LeanObject,
    mut v_target_4794_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4795_: *mut LeanObject = core::ptr::null_mut();
    v___x_4795_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Try_Collector_visit_spec__2_spec__3_spec__4___redArg(v_i_4792_, v_source_4793_, v_target_4794_);
    return v___x_4795_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Try_Collector_visit_spec__2_spec__3_spec__4_spec__6(
    mut v_00_u03b2_4796_: *mut LeanObject,
    mut v_x_4797_: *mut LeanObject,
    mut v_x_4798_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4799_: *mut LeanObject = core::ptr::null_mut();
    v___x_4799_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Meta_Try_Collector_visit_spec__2_spec__3_spec__4_spec__6___redArg(v_x_4797_, v_x_4798_);
    return v___x_4799_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Try_Collect_0__Lean_Meta_Try_Collector_main_go_spec__0_spec__1_spec__4(
    mut v_as_4800_: *mut LeanObject,
    mut v_sz_4801_: usize,
    mut v_i_4802_: usize,
    mut v_b_4803_: *mut LeanObject,
    mut v___y_4804_: *mut LeanObject,
    mut v___y_4805_: *mut LeanObject,
    mut v___y_4806_: *mut LeanObject,
    mut v___y_4807_: *mut LeanObject,
    mut v___y_4808_: *mut LeanObject,
    mut v___y_4809_: *mut LeanObject,
    mut v___y_4810_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4812_: u8 = 0;
    let mut v___x_4813_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_4814_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4816_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4817_: u8 = 0;
    let mut v___x_4818_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4820_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4822_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4823_: usize = 0;
    let mut v___x_4824_: usize = 0;
    let mut v_reuseFailAlloc_4826_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4827_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_4828_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4829_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4830_: u8 = 0;
    let mut v___x_4831_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_4832_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4833_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4834_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4836_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4837_: u8 = 0;
    let mut v___x_4839_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4840_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4841_: u8 = 0;
    let mut v___x_4842_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4843_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4844_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4845_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4847_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4848_: u8 = 0;
    let mut v___x_4850_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4851_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4852_: u8 = 0;
    let mut v_a_4853_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4855_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4856_: u8 = 0;
    let mut v___x_4858_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4859_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4860_: u8 = 0;
    let mut v_isSharedCheck_4861_: u8 = 0;
    let mut v_unused_4862_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4812_ = lean_usize_dec_lt(v_i_4802_, v_sz_4801_);
                if v___x_4812_ == 0 {
                    v___x_4813_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_4813_, 0, v_b_4803_);
                    return v___x_4813_;
                } else {
                    v_snd_4814_ = lean_ctor_get(v_b_4803_, 1);
                    v_isSharedCheck_4861_ = (!lean_is_exclusive(v_b_4803_)) as u8;
                    if v_isSharedCheck_4861_ == 0 {
                        v_unused_4862_ = lean_ctor_get(v_b_4803_, 0);
                        lean_dec(v_unused_4862_);
                        v___x_4816_ = v_b_4803_;
                        v_isShared_4817_ = v_isSharedCheck_4861_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_snd_4814_);
                        lean_dec(v_b_4803_);
                        v___x_4816_ = lean_box(0);
                        v_isShared_4817_ = v_isSharedCheck_4861_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_4818_ = lean_box(0);
                v_a_4827_ = lean_array_uget_borrowed(v_as_4800_, v_i_4802_);
                if lean_obj_tag(v_a_4827_) == 0 {
                    v_a_4820_ = v_snd_4814_;
                    state = 2;
                    continue;
                } else {
                    lean_dec(v_snd_4814_);
                    v_val_4828_ = lean_ctor_get(v_a_4827_, 0);
                    v___x_4829_ = lean_box(0);
                    v___x_4830_ = l_Lean_LocalDecl_isAuxDecl(v_val_4828_);
                    if v___x_4830_ == 0 {
                        v___x_4831_ = l_Lean_LocalDecl_value_x3f(v_val_4828_, v___x_4830_);
                        if lean_obj_tag(v___x_4831_) == 1 {
                            v_val_4832_ = lean_ctor_get(v___x_4831_, 0);
                            lean_inc(v_val_4832_);
                            lean_dec_ref_known(v___x_4831_, 1);
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
                            if lean_obj_tag(v___x_4833_) == 0 {
                                lean_dec_ref_known(v___x_4833_, 1);
                                v_a_4820_ = v___x_4829_;
                                state = 2;
                                continue;
                            } else {
                                lean_del_object(v___x_4816_);
                                v_a_4834_ = lean_ctor_get(v___x_4833_, 0);
                                v_isSharedCheck_4841_ = (!lean_is_exclusive(v___x_4833_)) as u8;
                                if v_isSharedCheck_4841_ == 0 {
                                    v___x_4836_ = v___x_4833_;
                                    v_isShared_4837_ = v_isSharedCheck_4841_;
                                    state = 4;
                                    continue;
                                } else {
                                    lean_inc(v_a_4834_);
                                    lean_dec(v___x_4833_);
                                    v___x_4836_ = lean_box(0);
                                    v_isShared_4837_ = v_isSharedCheck_4841_;
                                    state = 4;
                                    continue;
                                }
                            }
                        } else {
                            lean_dec(v___x_4831_);
                            v___x_4842_ = l_Lean_Meta_Try_Collector_checkInductive(
                                v_val_4828_,
                                v___y_4805_,
                                v___y_4806_,
                                v___y_4807_,
                                v___y_4808_,
                                v___y_4809_,
                                v___y_4810_,
                            );
                            if lean_obj_tag(v___x_4842_) == 0 {
                                lean_dec_ref_known(v___x_4842_, 1);
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
                                if lean_obj_tag(v___x_4844_) == 0 {
                                    lean_dec_ref_known(v___x_4844_, 1);
                                    v_a_4820_ = v___x_4829_;
                                    state = 2;
                                    continue;
                                } else {
                                    lean_del_object(v___x_4816_);
                                    v_a_4845_ = lean_ctor_get(v___x_4844_, 0);
                                    v_isSharedCheck_4852_ = (!lean_is_exclusive(v___x_4844_)) as u8;
                                    if v_isSharedCheck_4852_ == 0 {
                                        v___x_4847_ = v___x_4844_;
                                        v_isShared_4848_ = v_isSharedCheck_4852_;
                                        state = 6;
                                        continue;
                                    } else {
                                        lean_inc(v_a_4845_);
                                        lean_dec(v___x_4844_);
                                        v___x_4847_ = lean_box(0);
                                        v_isShared_4848_ = v_isSharedCheck_4852_;
                                        state = 6;
                                        continue;
                                    }
                                }
                            } else {
                                lean_del_object(v___x_4816_);
                                v_a_4853_ = lean_ctor_get(v___x_4842_, 0);
                                v_isSharedCheck_4860_ = (!lean_is_exclusive(v___x_4842_)) as u8;
                                if v_isSharedCheck_4860_ == 0 {
                                    v___x_4855_ = v___x_4842_;
                                    v_isShared_4856_ = v_isSharedCheck_4860_;
                                    state = 8;
                                    continue;
                                } else {
                                    lean_inc(v_a_4853_);
                                    lean_dec(v___x_4842_);
                                    v___x_4855_ = lean_box(0);
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
                    lean_ctor_set(v___x_4816_, 1, v_a_4820_);
                    lean_ctor_set(v___x_4816_, 0, v___x_4818_);
                    v___x_4822_ = v___x_4816_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_4826_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4826_, 0, v___x_4818_);
                    lean_ctor_set(v_reuseFailAlloc_4826_, 1, v_a_4820_);
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
                    v_reuseFailAlloc_4840_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4840_, 0, v_a_4834_);
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
                    v_reuseFailAlloc_4851_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4851_, 0, v_a_4845_);
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
                    v_reuseFailAlloc_4859_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4859_, 0, v_a_4853_);
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
    mut v_as_4863_: *mut LeanObject,
    mut v_sz_4864_: *mut LeanObject,
    mut v_i_4865_: *mut LeanObject,
    mut v_b_4866_: *mut LeanObject,
    mut v___y_4867_: *mut LeanObject,
    mut v___y_4868_: *mut LeanObject,
    mut v___y_4869_: *mut LeanObject,
    mut v___y_4870_: *mut LeanObject,
    mut v___y_4871_: *mut LeanObject,
    mut v___y_4872_: *mut LeanObject,
    mut v___y_4873_: *mut LeanObject,
    mut v___y_4874_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_boxed_4875_: usize = 0;
    let mut v_i_boxed_4876_: usize = 0;
    let mut v_res_4877_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_4875_ = lean_unbox_usize(v_sz_4864_);
    lean_dec(v_sz_4864_);
    v_i_boxed_4876_ = lean_unbox_usize(v_i_4865_);
    lean_dec(v_i_4865_);
    v_res_4877_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Try_Collect_0__Lean_Meta_Try_Collector_main_go_spec__0_spec__1_spec__4(v_as_4863_, v_sz_boxed_4875_, v_i_boxed_4876_, v_b_4866_, v___y_4867_, v___y_4868_, v___y_4869_, v___y_4870_, v___y_4871_, v___y_4872_, v___y_4873_);
    lean_dec(v___y_4873_);
    lean_dec_ref(v___y_4872_);
    lean_dec(v___y_4871_);
    lean_dec_ref(v___y_4870_);
    lean_dec(v___y_4869_);
    lean_dec_ref(v___y_4868_);
    lean_dec(v___y_4867_);
    lean_dec_ref(v_as_4863_);
    return v_res_4877_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Try_Collect_0__Lean_Meta_Try_Collector_main_go_spec__0_spec__1(
    mut v_as_4878_: *mut LeanObject,
    mut v_sz_4879_: usize,
    mut v_i_4880_: usize,
    mut v_b_4881_: *mut LeanObject,
    mut v___y_4882_: *mut LeanObject,
    mut v___y_4883_: *mut LeanObject,
    mut v___y_4884_: *mut LeanObject,
    mut v___y_4885_: *mut LeanObject,
    mut v___y_4886_: *mut LeanObject,
    mut v___y_4887_: *mut LeanObject,
    mut v___y_4888_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4890_: u8 = 0;
    let mut v___x_4891_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_4892_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4894_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4895_: u8 = 0;
    let mut v___x_4896_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4898_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4900_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4901_: usize = 0;
    let mut v___x_4902_: usize = 0;
    let mut v___x_4903_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4904_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4905_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_4906_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4907_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4908_: u8 = 0;
    let mut v___x_4909_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_4910_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4911_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4912_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4914_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4915_: u8 = 0;
    let mut v___x_4917_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4918_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4919_: u8 = 0;
    let mut v___x_4920_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4921_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4922_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4923_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4925_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4926_: u8 = 0;
    let mut v___x_4928_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4929_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4930_: u8 = 0;
    let mut v_a_4931_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4933_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4934_: u8 = 0;
    let mut v___x_4936_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4937_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4938_: u8 = 0;
    let mut v_isSharedCheck_4939_: u8 = 0;
    let mut v_unused_4940_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4890_ = lean_usize_dec_lt(v_i_4880_, v_sz_4879_);
                if v___x_4890_ == 0 {
                    v___x_4891_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_4891_, 0, v_b_4881_);
                    return v___x_4891_;
                } else {
                    v_snd_4892_ = lean_ctor_get(v_b_4881_, 1);
                    v_isSharedCheck_4939_ = (!lean_is_exclusive(v_b_4881_)) as u8;
                    if v_isSharedCheck_4939_ == 0 {
                        v_unused_4940_ = lean_ctor_get(v_b_4881_, 0);
                        lean_dec(v_unused_4940_);
                        v___x_4894_ = v_b_4881_;
                        v_isShared_4895_ = v_isSharedCheck_4939_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_snd_4892_);
                        lean_dec(v_b_4881_);
                        v___x_4894_ = lean_box(0);
                        v_isShared_4895_ = v_isSharedCheck_4939_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_4896_ = lean_box(0);
                v_a_4905_ = lean_array_uget_borrowed(v_as_4878_, v_i_4880_);
                if lean_obj_tag(v_a_4905_) == 0 {
                    v_a_4898_ = v_snd_4892_;
                    state = 2;
                    continue;
                } else {
                    lean_dec(v_snd_4892_);
                    v_val_4906_ = lean_ctor_get(v_a_4905_, 0);
                    v___x_4907_ = lean_box(0);
                    v___x_4908_ = l_Lean_LocalDecl_isAuxDecl(v_val_4906_);
                    if v___x_4908_ == 0 {
                        v___x_4909_ = l_Lean_LocalDecl_value_x3f(v_val_4906_, v___x_4908_);
                        if lean_obj_tag(v___x_4909_) == 1 {
                            v_val_4910_ = lean_ctor_get(v___x_4909_, 0);
                            lean_inc(v_val_4910_);
                            lean_dec_ref_known(v___x_4909_, 1);
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
                            if lean_obj_tag(v___x_4911_) == 0 {
                                lean_dec_ref_known(v___x_4911_, 1);
                                v_a_4898_ = v___x_4907_;
                                state = 2;
                                continue;
                            } else {
                                lean_del_object(v___x_4894_);
                                v_a_4912_ = lean_ctor_get(v___x_4911_, 0);
                                v_isSharedCheck_4919_ = (!lean_is_exclusive(v___x_4911_)) as u8;
                                if v_isSharedCheck_4919_ == 0 {
                                    v___x_4914_ = v___x_4911_;
                                    v_isShared_4915_ = v_isSharedCheck_4919_;
                                    state = 4;
                                    continue;
                                } else {
                                    lean_inc(v_a_4912_);
                                    lean_dec(v___x_4911_);
                                    v___x_4914_ = lean_box(0);
                                    v_isShared_4915_ = v_isSharedCheck_4919_;
                                    state = 4;
                                    continue;
                                }
                            }
                        } else {
                            lean_dec(v___x_4909_);
                            v___x_4920_ = l_Lean_Meta_Try_Collector_checkInductive(
                                v_val_4906_,
                                v___y_4883_,
                                v___y_4884_,
                                v___y_4885_,
                                v___y_4886_,
                                v___y_4887_,
                                v___y_4888_,
                            );
                            if lean_obj_tag(v___x_4920_) == 0 {
                                lean_dec_ref_known(v___x_4920_, 1);
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
                                if lean_obj_tag(v___x_4922_) == 0 {
                                    lean_dec_ref_known(v___x_4922_, 1);
                                    v_a_4898_ = v___x_4907_;
                                    state = 2;
                                    continue;
                                } else {
                                    lean_del_object(v___x_4894_);
                                    v_a_4923_ = lean_ctor_get(v___x_4922_, 0);
                                    v_isSharedCheck_4930_ = (!lean_is_exclusive(v___x_4922_)) as u8;
                                    if v_isSharedCheck_4930_ == 0 {
                                        v___x_4925_ = v___x_4922_;
                                        v_isShared_4926_ = v_isSharedCheck_4930_;
                                        state = 6;
                                        continue;
                                    } else {
                                        lean_inc(v_a_4923_);
                                        lean_dec(v___x_4922_);
                                        v___x_4925_ = lean_box(0);
                                        v_isShared_4926_ = v_isSharedCheck_4930_;
                                        state = 6;
                                        continue;
                                    }
                                }
                            } else {
                                lean_del_object(v___x_4894_);
                                v_a_4931_ = lean_ctor_get(v___x_4920_, 0);
                                v_isSharedCheck_4938_ = (!lean_is_exclusive(v___x_4920_)) as u8;
                                if v_isSharedCheck_4938_ == 0 {
                                    v___x_4933_ = v___x_4920_;
                                    v_isShared_4934_ = v_isSharedCheck_4938_;
                                    state = 8;
                                    continue;
                                } else {
                                    lean_inc(v_a_4931_);
                                    lean_dec(v___x_4920_);
                                    v___x_4933_ = lean_box(0);
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
                    lean_ctor_set(v___x_4894_, 1, v_a_4898_);
                    lean_ctor_set(v___x_4894_, 0, v___x_4896_);
                    v___x_4900_ = v___x_4894_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_4904_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4904_, 0, v___x_4896_);
                    lean_ctor_set(v_reuseFailAlloc_4904_, 1, v_a_4898_);
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
                    v_reuseFailAlloc_4918_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4918_, 0, v_a_4912_);
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
                    v_reuseFailAlloc_4929_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4929_, 0, v_a_4923_);
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
                    v_reuseFailAlloc_4937_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4937_, 0, v_a_4931_);
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
    mut v_as_4941_: *mut LeanObject,
    mut v_sz_4942_: *mut LeanObject,
    mut v_i_4943_: *mut LeanObject,
    mut v_b_4944_: *mut LeanObject,
    mut v___y_4945_: *mut LeanObject,
    mut v___y_4946_: *mut LeanObject,
    mut v___y_4947_: *mut LeanObject,
    mut v___y_4948_: *mut LeanObject,
    mut v___y_4949_: *mut LeanObject,
    mut v___y_4950_: *mut LeanObject,
    mut v___y_4951_: *mut LeanObject,
    mut v___y_4952_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_boxed_4953_: usize = 0;
    let mut v_i_boxed_4954_: usize = 0;
    let mut v_res_4955_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_4953_ = lean_unbox_usize(v_sz_4942_);
    lean_dec(v_sz_4942_);
    v_i_boxed_4954_ = lean_unbox_usize(v_i_4943_);
    lean_dec(v_i_4943_);
    v_res_4955_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Try_Collect_0__Lean_Meta_Try_Collector_main_go_spec__0_spec__1(v_as_4941_, v_sz_boxed_4953_, v_i_boxed_4954_, v_b_4944_, v___y_4945_, v___y_4946_, v___y_4947_, v___y_4948_, v___y_4949_, v___y_4950_, v___y_4951_);
    lean_dec(v___y_4951_);
    lean_dec_ref(v___y_4950_);
    lean_dec(v___y_4949_);
    lean_dec_ref(v___y_4948_);
    lean_dec(v___y_4947_);
    lean_dec_ref(v___y_4946_);
    lean_dec(v___y_4945_);
    lean_dec_ref(v_as_4941_);
    return v_res_4955_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Try_Collect_0__Lean_Meta_Try_Collector_main_go_spec__0_spec__0_spec__2_spec__3(
    mut v_as_4956_: *mut LeanObject,
    mut v_sz_4957_: usize,
    mut v_i_4958_: usize,
    mut v_b_4959_: *mut LeanObject,
    mut v___y_4960_: *mut LeanObject,
    mut v___y_4961_: *mut LeanObject,
    mut v___y_4962_: *mut LeanObject,
    mut v___y_4963_: *mut LeanObject,
    mut v___y_4964_: *mut LeanObject,
    mut v___y_4965_: *mut LeanObject,
    mut v___y_4966_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4968_: u8 = 0;
    let mut v___x_4969_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_4970_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4972_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4973_: u8 = 0;
    let mut v___x_4974_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4976_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4978_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4979_: usize = 0;
    let mut v___x_4980_: usize = 0;
    let mut v_reuseFailAlloc_4982_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4983_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_4984_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4985_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4986_: u8 = 0;
    let mut v___x_4987_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_4988_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4989_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4990_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4992_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4993_: u8 = 0;
    let mut v___x_4995_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4996_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4997_: u8 = 0;
    let mut v___x_4998_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4999_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5000_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5001_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5003_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5004_: u8 = 0;
    let mut v___x_5006_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5007_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5008_: u8 = 0;
    let mut v_a_5009_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5011_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5012_: u8 = 0;
    let mut v___x_5014_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5015_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5016_: u8 = 0;
    let mut v_isSharedCheck_5017_: u8 = 0;
    let mut v_unused_5018_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4968_ = lean_usize_dec_lt(v_i_4958_, v_sz_4957_);
                if v___x_4968_ == 0 {
                    v___x_4969_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_4969_, 0, v_b_4959_);
                    return v___x_4969_;
                } else {
                    v_snd_4970_ = lean_ctor_get(v_b_4959_, 1);
                    v_isSharedCheck_5017_ = (!lean_is_exclusive(v_b_4959_)) as u8;
                    if v_isSharedCheck_5017_ == 0 {
                        v_unused_5018_ = lean_ctor_get(v_b_4959_, 0);
                        lean_dec(v_unused_5018_);
                        v___x_4972_ = v_b_4959_;
                        v_isShared_4973_ = v_isSharedCheck_5017_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_snd_4970_);
                        lean_dec(v_b_4959_);
                        v___x_4972_ = lean_box(0);
                        v_isShared_4973_ = v_isSharedCheck_5017_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_4974_ = lean_box(0);
                v_a_4983_ = lean_array_uget_borrowed(v_as_4956_, v_i_4958_);
                if lean_obj_tag(v_a_4983_) == 0 {
                    v_a_4976_ = v_snd_4970_;
                    state = 2;
                    continue;
                } else {
                    lean_dec(v_snd_4970_);
                    v_val_4984_ = lean_ctor_get(v_a_4983_, 0);
                    v___x_4985_ = lean_box(0);
                    v___x_4986_ = l_Lean_LocalDecl_isAuxDecl(v_val_4984_);
                    if v___x_4986_ == 0 {
                        v___x_4987_ = l_Lean_LocalDecl_value_x3f(v_val_4984_, v___x_4986_);
                        if lean_obj_tag(v___x_4987_) == 1 {
                            v_val_4988_ = lean_ctor_get(v___x_4987_, 0);
                            lean_inc(v_val_4988_);
                            lean_dec_ref_known(v___x_4987_, 1);
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
                            if lean_obj_tag(v___x_4989_) == 0 {
                                lean_dec_ref_known(v___x_4989_, 1);
                                v_a_4976_ = v___x_4985_;
                                state = 2;
                                continue;
                            } else {
                                lean_del_object(v___x_4972_);
                                v_a_4990_ = lean_ctor_get(v___x_4989_, 0);
                                v_isSharedCheck_4997_ = (!lean_is_exclusive(v___x_4989_)) as u8;
                                if v_isSharedCheck_4997_ == 0 {
                                    v___x_4992_ = v___x_4989_;
                                    v_isShared_4993_ = v_isSharedCheck_4997_;
                                    state = 4;
                                    continue;
                                } else {
                                    lean_inc(v_a_4990_);
                                    lean_dec(v___x_4989_);
                                    v___x_4992_ = lean_box(0);
                                    v_isShared_4993_ = v_isSharedCheck_4997_;
                                    state = 4;
                                    continue;
                                }
                            }
                        } else {
                            lean_dec(v___x_4987_);
                            v___x_4998_ = l_Lean_Meta_Try_Collector_checkInductive(
                                v_val_4984_,
                                v___y_4961_,
                                v___y_4962_,
                                v___y_4963_,
                                v___y_4964_,
                                v___y_4965_,
                                v___y_4966_,
                            );
                            if lean_obj_tag(v___x_4998_) == 0 {
                                lean_dec_ref_known(v___x_4998_, 1);
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
                                if lean_obj_tag(v___x_5000_) == 0 {
                                    lean_dec_ref_known(v___x_5000_, 1);
                                    v_a_4976_ = v___x_4985_;
                                    state = 2;
                                    continue;
                                } else {
                                    lean_del_object(v___x_4972_);
                                    v_a_5001_ = lean_ctor_get(v___x_5000_, 0);
                                    v_isSharedCheck_5008_ = (!lean_is_exclusive(v___x_5000_)) as u8;
                                    if v_isSharedCheck_5008_ == 0 {
                                        v___x_5003_ = v___x_5000_;
                                        v_isShared_5004_ = v_isSharedCheck_5008_;
                                        state = 6;
                                        continue;
                                    } else {
                                        lean_inc(v_a_5001_);
                                        lean_dec(v___x_5000_);
                                        v___x_5003_ = lean_box(0);
                                        v_isShared_5004_ = v_isSharedCheck_5008_;
                                        state = 6;
                                        continue;
                                    }
                                }
                            } else {
                                lean_del_object(v___x_4972_);
                                v_a_5009_ = lean_ctor_get(v___x_4998_, 0);
                                v_isSharedCheck_5016_ = (!lean_is_exclusive(v___x_4998_)) as u8;
                                if v_isSharedCheck_5016_ == 0 {
                                    v___x_5011_ = v___x_4998_;
                                    v_isShared_5012_ = v_isSharedCheck_5016_;
                                    state = 8;
                                    continue;
                                } else {
                                    lean_inc(v_a_5009_);
                                    lean_dec(v___x_4998_);
                                    v___x_5011_ = lean_box(0);
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
                    lean_ctor_set(v___x_4972_, 1, v_a_4976_);
                    lean_ctor_set(v___x_4972_, 0, v___x_4974_);
                    v___x_4978_ = v___x_4972_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_4982_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4982_, 0, v___x_4974_);
                    lean_ctor_set(v_reuseFailAlloc_4982_, 1, v_a_4976_);
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
                    v_reuseFailAlloc_4996_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4996_, 0, v_a_4990_);
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
                    v_reuseFailAlloc_5007_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5007_, 0, v_a_5001_);
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
                    v_reuseFailAlloc_5015_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5015_, 0, v_a_5009_);
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
    mut v_as_5019_: *mut LeanObject,
    mut v_sz_5020_: *mut LeanObject,
    mut v_i_5021_: *mut LeanObject,
    mut v_b_5022_: *mut LeanObject,
    mut v___y_5023_: *mut LeanObject,
    mut v___y_5024_: *mut LeanObject,
    mut v___y_5025_: *mut LeanObject,
    mut v___y_5026_: *mut LeanObject,
    mut v___y_5027_: *mut LeanObject,
    mut v___y_5028_: *mut LeanObject,
    mut v___y_5029_: *mut LeanObject,
    mut v___y_5030_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_boxed_5031_: usize = 0;
    let mut v_i_boxed_5032_: usize = 0;
    let mut v_res_5033_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_5031_ = lean_unbox_usize(v_sz_5020_);
    lean_dec(v_sz_5020_);
    v_i_boxed_5032_ = lean_unbox_usize(v_i_5021_);
    lean_dec(v_i_5021_);
    v_res_5033_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Try_Collect_0__Lean_Meta_Try_Collector_main_go_spec__0_spec__0_spec__2_spec__3(v_as_5019_, v_sz_boxed_5031_, v_i_boxed_5032_, v_b_5022_, v___y_5023_, v___y_5024_, v___y_5025_, v___y_5026_, v___y_5027_, v___y_5028_, v___y_5029_);
    lean_dec(v___y_5029_);
    lean_dec_ref(v___y_5028_);
    lean_dec(v___y_5027_);
    lean_dec_ref(v___y_5026_);
    lean_dec(v___y_5025_);
    lean_dec_ref(v___y_5024_);
    lean_dec(v___y_5023_);
    lean_dec_ref(v_as_5019_);
    return v_res_5033_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Try_Collect_0__Lean_Meta_Try_Collector_main_go_spec__0_spec__0_spec__2(
    mut v_as_5034_: *mut LeanObject,
    mut v_sz_5035_: usize,
    mut v_i_5036_: usize,
    mut v_b_5037_: *mut LeanObject,
    mut v___y_5038_: *mut LeanObject,
    mut v___y_5039_: *mut LeanObject,
    mut v___y_5040_: *mut LeanObject,
    mut v___y_5041_: *mut LeanObject,
    mut v___y_5042_: *mut LeanObject,
    mut v___y_5043_: *mut LeanObject,
    mut v___y_5044_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5046_: u8 = 0;
    let mut v___x_5047_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_5048_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5050_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5051_: u8 = 0;
    let mut v___x_5052_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5054_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5056_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5057_: usize = 0;
    let mut v___x_5058_: usize = 0;
    let mut v___x_5059_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5060_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5061_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_5062_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5063_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5064_: u8 = 0;
    let mut v___x_5065_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_5066_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5067_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5068_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5070_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5071_: u8 = 0;
    let mut v___x_5073_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5074_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5075_: u8 = 0;
    let mut v___x_5076_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5077_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5078_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5079_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5081_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5082_: u8 = 0;
    let mut v___x_5084_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5085_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5086_: u8 = 0;
    let mut v_a_5087_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5089_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5090_: u8 = 0;
    let mut v___x_5092_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5093_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5094_: u8 = 0;
    let mut v_isSharedCheck_5095_: u8 = 0;
    let mut v_unused_5096_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5046_ = lean_usize_dec_lt(v_i_5036_, v_sz_5035_);
                if v___x_5046_ == 0 {
                    v___x_5047_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_5047_, 0, v_b_5037_);
                    return v___x_5047_;
                } else {
                    v_snd_5048_ = lean_ctor_get(v_b_5037_, 1);
                    v_isSharedCheck_5095_ = (!lean_is_exclusive(v_b_5037_)) as u8;
                    if v_isSharedCheck_5095_ == 0 {
                        v_unused_5096_ = lean_ctor_get(v_b_5037_, 0);
                        lean_dec(v_unused_5096_);
                        v___x_5050_ = v_b_5037_;
                        v_isShared_5051_ = v_isSharedCheck_5095_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_snd_5048_);
                        lean_dec(v_b_5037_);
                        v___x_5050_ = lean_box(0);
                        v_isShared_5051_ = v_isSharedCheck_5095_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_5052_ = lean_box(0);
                v_a_5061_ = lean_array_uget_borrowed(v_as_5034_, v_i_5036_);
                if lean_obj_tag(v_a_5061_) == 0 {
                    v_a_5054_ = v_snd_5048_;
                    state = 2;
                    continue;
                } else {
                    lean_dec(v_snd_5048_);
                    v_val_5062_ = lean_ctor_get(v_a_5061_, 0);
                    v___x_5063_ = lean_box(0);
                    v___x_5064_ = l_Lean_LocalDecl_isAuxDecl(v_val_5062_);
                    if v___x_5064_ == 0 {
                        v___x_5065_ = l_Lean_LocalDecl_value_x3f(v_val_5062_, v___x_5064_);
                        if lean_obj_tag(v___x_5065_) == 1 {
                            v_val_5066_ = lean_ctor_get(v___x_5065_, 0);
                            lean_inc(v_val_5066_);
                            lean_dec_ref_known(v___x_5065_, 1);
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
                            if lean_obj_tag(v___x_5067_) == 0 {
                                lean_dec_ref_known(v___x_5067_, 1);
                                v_a_5054_ = v___x_5063_;
                                state = 2;
                                continue;
                            } else {
                                lean_del_object(v___x_5050_);
                                v_a_5068_ = lean_ctor_get(v___x_5067_, 0);
                                v_isSharedCheck_5075_ = (!lean_is_exclusive(v___x_5067_)) as u8;
                                if v_isSharedCheck_5075_ == 0 {
                                    v___x_5070_ = v___x_5067_;
                                    v_isShared_5071_ = v_isSharedCheck_5075_;
                                    state = 4;
                                    continue;
                                } else {
                                    lean_inc(v_a_5068_);
                                    lean_dec(v___x_5067_);
                                    v___x_5070_ = lean_box(0);
                                    v_isShared_5071_ = v_isSharedCheck_5075_;
                                    state = 4;
                                    continue;
                                }
                            }
                        } else {
                            lean_dec(v___x_5065_);
                            v___x_5076_ = l_Lean_Meta_Try_Collector_checkInductive(
                                v_val_5062_,
                                v___y_5039_,
                                v___y_5040_,
                                v___y_5041_,
                                v___y_5042_,
                                v___y_5043_,
                                v___y_5044_,
                            );
                            if lean_obj_tag(v___x_5076_) == 0 {
                                lean_dec_ref_known(v___x_5076_, 1);
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
                                if lean_obj_tag(v___x_5078_) == 0 {
                                    lean_dec_ref_known(v___x_5078_, 1);
                                    v_a_5054_ = v___x_5063_;
                                    state = 2;
                                    continue;
                                } else {
                                    lean_del_object(v___x_5050_);
                                    v_a_5079_ = lean_ctor_get(v___x_5078_, 0);
                                    v_isSharedCheck_5086_ = (!lean_is_exclusive(v___x_5078_)) as u8;
                                    if v_isSharedCheck_5086_ == 0 {
                                        v___x_5081_ = v___x_5078_;
                                        v_isShared_5082_ = v_isSharedCheck_5086_;
                                        state = 6;
                                        continue;
                                    } else {
                                        lean_inc(v_a_5079_);
                                        lean_dec(v___x_5078_);
                                        v___x_5081_ = lean_box(0);
                                        v_isShared_5082_ = v_isSharedCheck_5086_;
                                        state = 6;
                                        continue;
                                    }
                                }
                            } else {
                                lean_del_object(v___x_5050_);
                                v_a_5087_ = lean_ctor_get(v___x_5076_, 0);
                                v_isSharedCheck_5094_ = (!lean_is_exclusive(v___x_5076_)) as u8;
                                if v_isSharedCheck_5094_ == 0 {
                                    v___x_5089_ = v___x_5076_;
                                    v_isShared_5090_ = v_isSharedCheck_5094_;
                                    state = 8;
                                    continue;
                                } else {
                                    lean_inc(v_a_5087_);
                                    lean_dec(v___x_5076_);
                                    v___x_5089_ = lean_box(0);
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
                    lean_ctor_set(v___x_5050_, 1, v_a_5054_);
                    lean_ctor_set(v___x_5050_, 0, v___x_5052_);
                    v___x_5056_ = v___x_5050_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_5060_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5060_, 0, v___x_5052_);
                    lean_ctor_set(v_reuseFailAlloc_5060_, 1, v_a_5054_);
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
                    v_reuseFailAlloc_5074_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5074_, 0, v_a_5068_);
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
                    v_reuseFailAlloc_5085_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5085_, 0, v_a_5079_);
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
                    v_reuseFailAlloc_5093_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5093_, 0, v_a_5087_);
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
    mut v_as_5097_: *mut LeanObject,
    mut v_sz_5098_: *mut LeanObject,
    mut v_i_5099_: *mut LeanObject,
    mut v_b_5100_: *mut LeanObject,
    mut v___y_5101_: *mut LeanObject,
    mut v___y_5102_: *mut LeanObject,
    mut v___y_5103_: *mut LeanObject,
    mut v___y_5104_: *mut LeanObject,
    mut v___y_5105_: *mut LeanObject,
    mut v___y_5106_: *mut LeanObject,
    mut v___y_5107_: *mut LeanObject,
    mut v___y_5108_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_boxed_5109_: usize = 0;
    let mut v_i_boxed_5110_: usize = 0;
    let mut v_res_5111_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_5109_ = lean_unbox_usize(v_sz_5098_);
    lean_dec(v_sz_5098_);
    v_i_boxed_5110_ = lean_unbox_usize(v_i_5099_);
    lean_dec(v_i_5099_);
    v_res_5111_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Try_Collect_0__Lean_Meta_Try_Collector_main_go_spec__0_spec__0_spec__2(v_as_5097_, v_sz_boxed_5109_, v_i_boxed_5110_, v_b_5100_, v___y_5101_, v___y_5102_, v___y_5103_, v___y_5104_, v___y_5105_, v___y_5106_, v___y_5107_);
    lean_dec(v___y_5107_);
    lean_dec_ref(v___y_5106_);
    lean_dec(v___y_5105_);
    lean_dec_ref(v___y_5104_);
    lean_dec(v___y_5103_);
    lean_dec_ref(v___y_5102_);
    lean_dec(v___y_5101_);
    lean_dec_ref(v_as_5097_);
    return v_res_5111_;
}
pub unsafe fn l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Try_Collect_0__Lean_Meta_Try_Collector_main_go_spec__0_spec__0(
    mut v_init_5112_: *mut LeanObject,
    mut v_n_5113_: *mut LeanObject,
    mut v_b_5114_: *mut LeanObject,
    mut v___y_5115_: *mut LeanObject,
    mut v___y_5116_: *mut LeanObject,
    mut v___y_5117_: *mut LeanObject,
    mut v___y_5118_: *mut LeanObject,
    mut v___y_5119_: *mut LeanObject,
    mut v___y_5120_: *mut LeanObject,
    mut v___y_5121_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_cs_5123_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5124_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5125_: *mut LeanObject = core::ptr::null_mut();
    let mut v_sz_5126_: usize = 0;
    let mut v___x_5127_: usize = 0;
    let mut v___x_5128_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5129_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5131_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5132_: u8 = 0;
    let mut v_fst_5133_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_5134_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5135_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5137_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5138_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_5139_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5141_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5142_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5143_: u8 = 0;
    let mut v_a_5144_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5146_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5147_: u8 = 0;
    let mut v___x_5149_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5150_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5151_: u8 = 0;
    let mut v_vs_5152_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5153_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5154_: *mut LeanObject = core::ptr::null_mut();
    let mut v_sz_5155_: usize = 0;
    let mut v___x_5156_: usize = 0;
    let mut v___x_5157_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5158_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5160_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5161_: u8 = 0;
    let mut v_fst_5162_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_5163_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5164_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5166_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5167_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_5168_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5170_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5171_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5172_: u8 = 0;
    let mut v_a_5173_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5175_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5176_: u8 = 0;
    let mut v___x_5178_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5179_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5180_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_n_5113_) == 0 {
                    v_cs_5123_ = lean_ctor_get(v_n_5113_, 0);
                    v___x_5124_ = lean_box(0);
                    v___x_5125_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v___x_5125_, 0, v___x_5124_);
                    lean_ctor_set(v___x_5125_, 1, v_b_5114_);
                    v_sz_5126_ = lean_array_size(v_cs_5123_);
                    v___x_5127_ = 0usize;
                    v___x_5128_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Try_Collect_0__Lean_Meta_Try_Collector_main_go_spec__0_spec__0_spec__1(v_init_5112_, v_cs_5123_, v_sz_5126_, v___x_5127_, v___x_5125_, v___y_5115_, v___y_5116_, v___y_5117_, v___y_5118_, v___y_5119_, v___y_5120_, v___y_5121_);
                    if lean_obj_tag(v___x_5128_) == 0 {
                        v_a_5129_ = lean_ctor_get(v___x_5128_, 0);
                        v_isSharedCheck_5143_ = (!lean_is_exclusive(v___x_5128_)) as u8;
                        if v_isSharedCheck_5143_ == 0 {
                            v___x_5131_ = v___x_5128_;
                            v_isShared_5132_ = v_isSharedCheck_5143_;
                            state = 1;
                            continue;
                        } else {
                            lean_inc(v_a_5129_);
                            lean_dec(v___x_5128_);
                            v___x_5131_ = lean_box(0);
                            v_isShared_5132_ = v_isSharedCheck_5143_;
                            state = 1;
                            continue;
                        }
                    } else {
                        v_a_5144_ = lean_ctor_get(v___x_5128_, 0);
                        v_isSharedCheck_5151_ = (!lean_is_exclusive(v___x_5128_)) as u8;
                        if v_isSharedCheck_5151_ == 0 {
                            v___x_5146_ = v___x_5128_;
                            v_isShared_5147_ = v_isSharedCheck_5151_;
                            state = 4;
                            continue;
                        } else {
                            lean_inc(v_a_5144_);
                            lean_dec(v___x_5128_);
                            v___x_5146_ = lean_box(0);
                            v_isShared_5147_ = v_isSharedCheck_5151_;
                            state = 4;
                            continue;
                        }
                    }
                } else {
                    v_vs_5152_ = lean_ctor_get(v_n_5113_, 0);
                    v___x_5153_ = lean_box(0);
                    v___x_5154_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v___x_5154_, 0, v___x_5153_);
                    lean_ctor_set(v___x_5154_, 1, v_b_5114_);
                    v_sz_5155_ = lean_array_size(v_vs_5152_);
                    v___x_5156_ = 0usize;
                    v___x_5157_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Try_Collect_0__Lean_Meta_Try_Collector_main_go_spec__0_spec__0_spec__2(v_vs_5152_, v_sz_5155_, v___x_5156_, v___x_5154_, v___y_5115_, v___y_5116_, v___y_5117_, v___y_5118_, v___y_5119_, v___y_5120_, v___y_5121_);
                    if lean_obj_tag(v___x_5157_) == 0 {
                        v_a_5158_ = lean_ctor_get(v___x_5157_, 0);
                        v_isSharedCheck_5172_ = (!lean_is_exclusive(v___x_5157_)) as u8;
                        if v_isSharedCheck_5172_ == 0 {
                            v___x_5160_ = v___x_5157_;
                            v_isShared_5161_ = v_isSharedCheck_5172_;
                            state = 6;
                            continue;
                        } else {
                            lean_inc(v_a_5158_);
                            lean_dec(v___x_5157_);
                            v___x_5160_ = lean_box(0);
                            v_isShared_5161_ = v_isSharedCheck_5172_;
                            state = 6;
                            continue;
                        }
                    } else {
                        v_a_5173_ = lean_ctor_get(v___x_5157_, 0);
                        v_isSharedCheck_5180_ = (!lean_is_exclusive(v___x_5157_)) as u8;
                        if v_isSharedCheck_5180_ == 0 {
                            v___x_5175_ = v___x_5157_;
                            v_isShared_5176_ = v_isSharedCheck_5180_;
                            state = 9;
                            continue;
                        } else {
                            lean_inc(v_a_5173_);
                            lean_dec(v___x_5157_);
                            v___x_5175_ = lean_box(0);
                            v_isShared_5176_ = v_isSharedCheck_5180_;
                            state = 9;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v_fst_5133_ = lean_ctor_get(v_a_5129_, 0);
                if lean_obj_tag(v_fst_5133_) == 0 {
                    v_snd_5134_ = lean_ctor_get(v_a_5129_, 1);
                    lean_inc(v_snd_5134_);
                    lean_dec(v_a_5129_);
                    v___x_5135_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v___x_5135_, 0, v_snd_5134_);
                    if v_isShared_5132_ == 0 {
                        lean_ctor_set(v___x_5131_, 0, v___x_5135_);
                        v___x_5137_ = v___x_5131_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_5138_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_5138_, 0, v___x_5135_);
                        v___x_5137_ = v_reuseFailAlloc_5138_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_inc_ref(v_fst_5133_);
                    lean_dec(v_a_5129_);
                    v_val_5139_ = lean_ctor_get(v_fst_5133_, 0);
                    lean_inc(v_val_5139_);
                    lean_dec_ref_known(v_fst_5133_, 1);
                    if v_isShared_5132_ == 0 {
                        lean_ctor_set(v___x_5131_, 0, v_val_5139_);
                        v___x_5141_ = v___x_5131_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_5142_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_5142_, 0, v_val_5139_);
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
                    v_reuseFailAlloc_5150_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5150_, 0, v_a_5144_);
                    v___x_5149_ = v_reuseFailAlloc_5150_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_5149_;
            }
            6 => {
                v_fst_5162_ = lean_ctor_get(v_a_5158_, 0);
                if lean_obj_tag(v_fst_5162_) == 0 {
                    v_snd_5163_ = lean_ctor_get(v_a_5158_, 1);
                    lean_inc(v_snd_5163_);
                    lean_dec(v_a_5158_);
                    v___x_5164_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v___x_5164_, 0, v_snd_5163_);
                    if v_isShared_5161_ == 0 {
                        lean_ctor_set(v___x_5160_, 0, v___x_5164_);
                        v___x_5166_ = v___x_5160_;
                        state = 7;
                        continue;
                    } else {
                        v_reuseFailAlloc_5167_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_5167_, 0, v___x_5164_);
                        v___x_5166_ = v_reuseFailAlloc_5167_;
                        state = 7;
                        continue;
                    }
                } else {
                    lean_inc_ref(v_fst_5162_);
                    lean_dec(v_a_5158_);
                    v_val_5168_ = lean_ctor_get(v_fst_5162_, 0);
                    lean_inc(v_val_5168_);
                    lean_dec_ref_known(v_fst_5162_, 1);
                    if v_isShared_5161_ == 0 {
                        lean_ctor_set(v___x_5160_, 0, v_val_5168_);
                        v___x_5170_ = v___x_5160_;
                        state = 8;
                        continue;
                    } else {
                        v_reuseFailAlloc_5171_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_5171_, 0, v_val_5168_);
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
                    v_reuseFailAlloc_5179_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5179_, 0, v_a_5173_);
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
    mut v_init_5181_: *mut LeanObject,
    mut v_as_5182_: *mut LeanObject,
    mut v_sz_5183_: usize,
    mut v_i_5184_: usize,
    mut v_b_5185_: *mut LeanObject,
    mut v___y_5186_: *mut LeanObject,
    mut v___y_5187_: *mut LeanObject,
    mut v___y_5188_: *mut LeanObject,
    mut v___y_5189_: *mut LeanObject,
    mut v___y_5190_: *mut LeanObject,
    mut v___y_5191_: *mut LeanObject,
    mut v___y_5192_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5194_: u8 = 0;
    let mut v___x_5195_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_5196_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5198_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5199_: u8 = 0;
    let mut v_a_5200_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5201_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5202_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5204_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5205_: u8 = 0;
    let mut v___x_5206_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5208_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5210_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5211_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5212_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5213_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5214_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5216_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5217_: usize = 0;
    let mut v___x_5218_: usize = 0;
    let mut v_reuseFailAlloc_5220_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5221_: u8 = 0;
    let mut v_a_5222_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5224_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5225_: u8 = 0;
    let mut v___x_5227_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5228_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5229_: u8 = 0;
    let mut v_isSharedCheck_5230_: u8 = 0;
    let mut v_unused_5231_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5194_ = lean_usize_dec_lt(v_i_5184_, v_sz_5183_);
                if v___x_5194_ == 0 {
                    v___x_5195_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_5195_, 0, v_b_5185_);
                    return v___x_5195_;
                } else {
                    v_snd_5196_ = lean_ctor_get(v_b_5185_, 1);
                    v_isSharedCheck_5230_ = (!lean_is_exclusive(v_b_5185_)) as u8;
                    if v_isSharedCheck_5230_ == 0 {
                        v_unused_5231_ = lean_ctor_get(v_b_5185_, 0);
                        lean_dec(v_unused_5231_);
                        v___x_5198_ = v_b_5185_;
                        v_isShared_5199_ = v_isSharedCheck_5230_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_snd_5196_);
                        lean_dec(v_b_5185_);
                        v___x_5198_ = lean_box(0);
                        v_isShared_5199_ = v_isSharedCheck_5230_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_a_5200_ = lean_array_uget_borrowed(v_as_5182_, v_i_5184_);
                lean_inc(v_snd_5196_);
                v___x_5201_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Try_Collect_0__Lean_Meta_Try_Collector_main_go_spec__0_spec__0(v_init_5181_, v_a_5200_, v_snd_5196_, v___y_5186_, v___y_5187_, v___y_5188_, v___y_5189_, v___y_5190_, v___y_5191_, v___y_5192_);
                if lean_obj_tag(v___x_5201_) == 0 {
                    v_a_5202_ = lean_ctor_get(v___x_5201_, 0);
                    v_isSharedCheck_5221_ = (!lean_is_exclusive(v___x_5201_)) as u8;
                    if v_isSharedCheck_5221_ == 0 {
                        v___x_5204_ = v___x_5201_;
                        v_isShared_5205_ = v_isSharedCheck_5221_;
                        state = 2;
                        continue;
                    } else {
                        lean_inc(v_a_5202_);
                        lean_dec(v___x_5201_);
                        v___x_5204_ = lean_box(0);
                        v_isShared_5205_ = v_isSharedCheck_5221_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_5198_);
                    lean_dec(v_snd_5196_);
                    v_a_5222_ = lean_ctor_get(v___x_5201_, 0);
                    v_isSharedCheck_5229_ = (!lean_is_exclusive(v___x_5201_)) as u8;
                    if v_isSharedCheck_5229_ == 0 {
                        v___x_5224_ = v___x_5201_;
                        v_isShared_5225_ = v_isSharedCheck_5229_;
                        state = 6;
                        continue;
                    } else {
                        lean_inc(v_a_5222_);
                        lean_dec(v___x_5201_);
                        v___x_5224_ = lean_box(0);
                        v_isShared_5225_ = v_isSharedCheck_5229_;
                        state = 6;
                        continue;
                    }
                }
            }
            2 => {
                if lean_obj_tag(v_a_5202_) == 0 {
                    v___x_5206_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v___x_5206_, 0, v_a_5202_);
                    if v_isShared_5199_ == 0 {
                        lean_ctor_set(v___x_5198_, 0, v___x_5206_);
                        v___x_5208_ = v___x_5198_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_5212_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_5212_, 0, v___x_5206_);
                        lean_ctor_set(v_reuseFailAlloc_5212_, 1, v_snd_5196_);
                        v___x_5208_ = v_reuseFailAlloc_5212_;
                        state = 3;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_5204_);
                    lean_dec(v_snd_5196_);
                    v_a_5213_ = lean_ctor_get(v_a_5202_, 0);
                    lean_inc(v_a_5213_);
                    lean_dec_ref_known(v_a_5202_, 1);
                    v___x_5214_ = lean_box(0);
                    if v_isShared_5199_ == 0 {
                        lean_ctor_set(v___x_5198_, 1, v_a_5213_);
                        lean_ctor_set(v___x_5198_, 0, v___x_5214_);
                        v___x_5216_ = v___x_5198_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_5220_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_5220_, 0, v___x_5214_);
                        lean_ctor_set(v_reuseFailAlloc_5220_, 1, v_a_5213_);
                        v___x_5216_ = v_reuseFailAlloc_5220_;
                        state = 5;
                        continue;
                    }
                }
            }
            3 => {
                if v_isShared_5205_ == 0 {
                    lean_ctor_set(v___x_5204_, 0, v___x_5208_);
                    v___x_5210_ = v___x_5204_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_5211_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5211_, 0, v___x_5208_);
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
                    v_reuseFailAlloc_5228_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5228_, 0, v_a_5222_);
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
    mut v_init_5232_: *mut LeanObject,
    mut v_as_5233_: *mut LeanObject,
    mut v_sz_5234_: *mut LeanObject,
    mut v_i_5235_: *mut LeanObject,
    mut v_b_5236_: *mut LeanObject,
    mut v___y_5237_: *mut LeanObject,
    mut v___y_5238_: *mut LeanObject,
    mut v___y_5239_: *mut LeanObject,
    mut v___y_5240_: *mut LeanObject,
    mut v___y_5241_: *mut LeanObject,
    mut v___y_5242_: *mut LeanObject,
    mut v___y_5243_: *mut LeanObject,
    mut v___y_5244_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_boxed_5245_: usize = 0;
    let mut v_i_boxed_5246_: usize = 0;
    let mut v_res_5247_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_5245_ = lean_unbox_usize(v_sz_5234_);
    lean_dec(v_sz_5234_);
    v_i_boxed_5246_ = lean_unbox_usize(v_i_5235_);
    lean_dec(v_i_5235_);
    v_res_5247_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Try_Collect_0__Lean_Meta_Try_Collector_main_go_spec__0_spec__0_spec__1(v_init_5232_, v_as_5233_, v_sz_boxed_5245_, v_i_boxed_5246_, v_b_5236_, v___y_5237_, v___y_5238_, v___y_5239_, v___y_5240_, v___y_5241_, v___y_5242_, v___y_5243_);
    lean_dec(v___y_5243_);
    lean_dec_ref(v___y_5242_);
    lean_dec(v___y_5241_);
    lean_dec_ref(v___y_5240_);
    lean_dec(v___y_5239_);
    lean_dec_ref(v___y_5238_);
    lean_dec(v___y_5237_);
    lean_dec_ref(v_as_5233_);
    return v_res_5247_;
}
pub unsafe fn l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Try_Collect_0__Lean_Meta_Try_Collector_main_go_spec__0_spec__0___boxed(
    mut v_init_5248_: *mut LeanObject,
    mut v_n_5249_: *mut LeanObject,
    mut v_b_5250_: *mut LeanObject,
    mut v___y_5251_: *mut LeanObject,
    mut v___y_5252_: *mut LeanObject,
    mut v___y_5253_: *mut LeanObject,
    mut v___y_5254_: *mut LeanObject,
    mut v___y_5255_: *mut LeanObject,
    mut v___y_5256_: *mut LeanObject,
    mut v___y_5257_: *mut LeanObject,
    mut v___y_5258_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5259_: *mut LeanObject = core::ptr::null_mut();
    v_res_5259_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Try_Collect_0__Lean_Meta_Try_Collector_main_go_spec__0_spec__0(v_init_5248_, v_n_5249_, v_b_5250_, v___y_5251_, v___y_5252_, v___y_5253_, v___y_5254_, v___y_5255_, v___y_5256_, v___y_5257_);
    lean_dec(v___y_5257_);
    lean_dec_ref(v___y_5256_);
    lean_dec(v___y_5255_);
    lean_dec_ref(v___y_5254_);
    lean_dec(v___y_5253_);
    lean_dec_ref(v___y_5252_);
    lean_dec(v___y_5251_);
    lean_dec_ref(v_n_5249_);
    return v_res_5259_;
}
pub unsafe fn l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Try_Collect_0__Lean_Meta_Try_Collector_main_go_spec__0(
    mut v_t_5260_: *mut LeanObject,
    mut v_init_5261_: *mut LeanObject,
    mut v___y_5262_: *mut LeanObject,
    mut v___y_5263_: *mut LeanObject,
    mut v___y_5264_: *mut LeanObject,
    mut v___y_5265_: *mut LeanObject,
    mut v___y_5266_: *mut LeanObject,
    mut v___y_5267_: *mut LeanObject,
    mut v___y_5268_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_root_5270_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_5271_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5272_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5273_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5275_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5276_: u8 = 0;
    let mut v_a_5277_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5279_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5280_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5281_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5282_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5283_: *mut LeanObject = core::ptr::null_mut();
    let mut v_sz_5284_: usize = 0;
    let mut v___x_5285_: usize = 0;
    let mut v___x_5286_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5287_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5289_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5290_: u8 = 0;
    let mut v_fst_5291_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_5292_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5294_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5295_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_5296_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5298_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5299_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5300_: u8 = 0;
    let mut v_a_5301_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5303_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5304_: u8 = 0;
    let mut v___x_5306_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5307_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5308_: u8 = 0;
    let mut v_isSharedCheck_5309_: u8 = 0;
    let mut v_a_5310_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5312_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5313_: u8 = 0;
    let mut v___x_5315_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5316_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5317_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_root_5270_ = lean_ctor_get(v_t_5260_, 0);
                v_tail_5271_ = lean_ctor_get(v_t_5260_, 1);
                v___x_5272_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Try_Collect_0__Lean_Meta_Try_Collector_main_go_spec__0_spec__0(v_init_5261_, v_root_5270_, v_init_5261_, v___y_5262_, v___y_5263_, v___y_5264_, v___y_5265_, v___y_5266_, v___y_5267_, v___y_5268_);
                if lean_obj_tag(v___x_5272_) == 0 {
                    v_a_5273_ = lean_ctor_get(v___x_5272_, 0);
                    v_isSharedCheck_5309_ = (!lean_is_exclusive(v___x_5272_)) as u8;
                    if v_isSharedCheck_5309_ == 0 {
                        v___x_5275_ = v___x_5272_;
                        v_isShared_5276_ = v_isSharedCheck_5309_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_5273_);
                        lean_dec(v___x_5272_);
                        v___x_5275_ = lean_box(0);
                        v_isShared_5276_ = v_isSharedCheck_5309_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_5310_ = lean_ctor_get(v___x_5272_, 0);
                    v_isSharedCheck_5317_ = (!lean_is_exclusive(v___x_5272_)) as u8;
                    if v_isSharedCheck_5317_ == 0 {
                        v___x_5312_ = v___x_5272_;
                        v_isShared_5313_ = v_isSharedCheck_5317_;
                        state = 8;
                        continue;
                    } else {
                        lean_inc(v_a_5310_);
                        lean_dec(v___x_5272_);
                        v___x_5312_ = lean_box(0);
                        v_isShared_5313_ = v_isSharedCheck_5317_;
                        state = 8;
                        continue;
                    }
                }
            }
            1 => {
                if lean_obj_tag(v_a_5273_) == 0 {
                    v_a_5277_ = lean_ctor_get(v_a_5273_, 0);
                    lean_inc(v_a_5277_);
                    lean_dec_ref_known(v_a_5273_, 1);
                    if v_isShared_5276_ == 0 {
                        lean_ctor_set(v___x_5275_, 0, v_a_5277_);
                        v___x_5279_ = v___x_5275_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_5280_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_5280_, 0, v_a_5277_);
                        v___x_5279_ = v_reuseFailAlloc_5280_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_5275_);
                    v_a_5281_ = lean_ctor_get(v_a_5273_, 0);
                    lean_inc(v_a_5281_);
                    lean_dec_ref_known(v_a_5273_, 1);
                    v___x_5282_ = lean_box(0);
                    v___x_5283_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v___x_5283_, 0, v___x_5282_);
                    lean_ctor_set(v___x_5283_, 1, v_a_5281_);
                    v_sz_5284_ = lean_array_size(v_tail_5271_);
                    v___x_5285_ = 0usize;
                    v___x_5286_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Try_Collect_0__Lean_Meta_Try_Collector_main_go_spec__0_spec__1(v_tail_5271_, v_sz_5284_, v___x_5285_, v___x_5283_, v___y_5262_, v___y_5263_, v___y_5264_, v___y_5265_, v___y_5266_, v___y_5267_, v___y_5268_);
                    if lean_obj_tag(v___x_5286_) == 0 {
                        v_a_5287_ = lean_ctor_get(v___x_5286_, 0);
                        v_isSharedCheck_5300_ = (!lean_is_exclusive(v___x_5286_)) as u8;
                        if v_isSharedCheck_5300_ == 0 {
                            v___x_5289_ = v___x_5286_;
                            v_isShared_5290_ = v_isSharedCheck_5300_;
                            state = 3;
                            continue;
                        } else {
                            lean_inc(v_a_5287_);
                            lean_dec(v___x_5286_);
                            v___x_5289_ = lean_box(0);
                            v_isShared_5290_ = v_isSharedCheck_5300_;
                            state = 3;
                            continue;
                        }
                    } else {
                        v_a_5301_ = lean_ctor_get(v___x_5286_, 0);
                        v_isSharedCheck_5308_ = (!lean_is_exclusive(v___x_5286_)) as u8;
                        if v_isSharedCheck_5308_ == 0 {
                            v___x_5303_ = v___x_5286_;
                            v_isShared_5304_ = v_isSharedCheck_5308_;
                            state = 6;
                            continue;
                        } else {
                            lean_inc(v_a_5301_);
                            lean_dec(v___x_5286_);
                            v___x_5303_ = lean_box(0);
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
                v_fst_5291_ = lean_ctor_get(v_a_5287_, 0);
                if lean_obj_tag(v_fst_5291_) == 0 {
                    v_snd_5292_ = lean_ctor_get(v_a_5287_, 1);
                    lean_inc(v_snd_5292_);
                    lean_dec(v_a_5287_);
                    if v_isShared_5290_ == 0 {
                        lean_ctor_set(v___x_5289_, 0, v_snd_5292_);
                        v___x_5294_ = v___x_5289_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_5295_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_5295_, 0, v_snd_5292_);
                        v___x_5294_ = v_reuseFailAlloc_5295_;
                        state = 4;
                        continue;
                    }
                } else {
                    lean_inc_ref(v_fst_5291_);
                    lean_dec(v_a_5287_);
                    v_val_5296_ = lean_ctor_get(v_fst_5291_, 0);
                    lean_inc(v_val_5296_);
                    lean_dec_ref_known(v_fst_5291_, 1);
                    if v_isShared_5290_ == 0 {
                        lean_ctor_set(v___x_5289_, 0, v_val_5296_);
                        v___x_5298_ = v___x_5289_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_5299_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_5299_, 0, v_val_5296_);
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
                    v_reuseFailAlloc_5307_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5307_, 0, v_a_5301_);
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
                    v_reuseFailAlloc_5316_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5316_, 0, v_a_5310_);
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
    mut v_t_5318_: *mut LeanObject,
    mut v_init_5319_: *mut LeanObject,
    mut v___y_5320_: *mut LeanObject,
    mut v___y_5321_: *mut LeanObject,
    mut v___y_5322_: *mut LeanObject,
    mut v___y_5323_: *mut LeanObject,
    mut v___y_5324_: *mut LeanObject,
    mut v___y_5325_: *mut LeanObject,
    mut v___y_5326_: *mut LeanObject,
    mut v___y_5327_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5328_: *mut LeanObject = core::ptr::null_mut();
    v_res_5328_ = l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Try_Collect_0__Lean_Meta_Try_Collector_main_go_spec__0(v_t_5318_, v_init_5319_, v___y_5320_, v___y_5321_, v___y_5322_, v___y_5323_, v___y_5324_, v___y_5325_, v___y_5326_);
    lean_dec(v___y_5326_);
    lean_dec_ref(v___y_5325_);
    lean_dec(v___y_5324_);
    lean_dec_ref(v___y_5323_);
    lean_dec(v___y_5322_);
    lean_dec_ref(v___y_5321_);
    lean_dec(v___y_5320_);
    lean_dec_ref(v_t_5318_);
    return v_res_5328_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Try_Collect_0__Lean_Meta_Try_Collector_main_go(
    mut v_mvarId_5329_: *mut LeanObject,
    mut v_a_5330_: *mut LeanObject,
    mut v_a_5331_: *mut LeanObject,
    mut v_a_5332_: *mut LeanObject,
    mut v_a_5333_: *mut LeanObject,
    mut v_a_5334_: *mut LeanObject,
    mut v_a_5335_: *mut LeanObject,
    mut v_a_5336_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___y_5339_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5340_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5341_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5342_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5343_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5344_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5345_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5346_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5347_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5348_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5349_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5351_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5352_: u8 = 0;
    let mut v___x_5354_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5355_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5356_: u8 = 0;
    let mut v_targetOnly_5357_: u8 = 0;
    let mut v_lctx_5358_: *mut LeanObject = core::ptr::null_mut();
    let mut v_decls_5359_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5360_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5361_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_targetOnly_5357_ = lean_ctor_get_uint8(
                    v_a_5331_,
                    (core::mem::size_of::<*mut LeanObject>() * 1 + 2) as u32,
                );
                if v_targetOnly_5357_ == 0 {
                    v_lctx_5358_ = lean_ctor_get(v_a_5333_, 2);
                    v_decls_5359_ = lean_ctor_get(v_lctx_5358_, 1);
                    v___x_5360_ = lean_box(0);
                    v___x_5361_ = l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Try_Collect_0__Lean_Meta_Try_Collector_main_go_spec__0(v_decls_5359_, v___x_5360_, v_a_5330_, v_a_5331_, v_a_5332_, v_a_5333_, v_a_5334_, v_a_5335_, v_a_5336_);
                    if lean_obj_tag(v___x_5361_) == 0 {
                        lean_dec_ref_known(v___x_5361_, 1);
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
                        lean_dec(v_mvarId_5329_);
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
                if lean_obj_tag(v___x_5346_) == 0 {
                    v_a_5347_ = lean_ctor_get(v___x_5346_, 0);
                    lean_inc(v_a_5347_);
                    lean_dec_ref_known(v___x_5346_, 1);
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
                    v_a_5349_ = lean_ctor_get(v___x_5346_, 0);
                    v_isSharedCheck_5356_ = (!lean_is_exclusive(v___x_5346_)) as u8;
                    if v_isSharedCheck_5356_ == 0 {
                        v___x_5351_ = v___x_5346_;
                        v_isShared_5352_ = v_isSharedCheck_5356_;
                        state = 2;
                        continue;
                    } else {
                        lean_inc(v_a_5349_);
                        lean_dec(v___x_5346_);
                        v___x_5351_ = lean_box(0);
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
                    v_reuseFailAlloc_5355_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5355_, 0, v_a_5349_);
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
    mut v_mvarId_5362_: *mut LeanObject,
    mut v_a_5363_: *mut LeanObject,
    mut v_a_5364_: *mut LeanObject,
    mut v_a_5365_: *mut LeanObject,
    mut v_a_5366_: *mut LeanObject,
    mut v_a_5367_: *mut LeanObject,
    mut v_a_5368_: *mut LeanObject,
    mut v_a_5369_: *mut LeanObject,
    mut v_a_5370_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5371_: *mut LeanObject = core::ptr::null_mut();
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
    lean_dec(v_a_5369_);
    lean_dec_ref(v_a_5368_);
    lean_dec(v_a_5367_);
    lean_dec_ref(v_a_5366_);
    lean_dec(v_a_5365_);
    lean_dec_ref(v_a_5364_);
    lean_dec(v_a_5363_);
    return v_res_5371_;
}
pub unsafe fn l_Lean_MVarId_withContext___at___00Lean_Meta_Try_Collector_main_spec__0___redArg(
    mut v_mvarId_5372_: *mut LeanObject,
    mut v_x_5373_: *mut LeanObject,
    mut v___y_5374_: *mut LeanObject,
    mut v___y_5375_: *mut LeanObject,
    mut v___y_5376_: *mut LeanObject,
    mut v___y_5377_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5379_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5380_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5382_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5383_: u8 = 0;
    let mut v___x_5385_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5386_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5387_: u8 = 0;
    let mut v_a_5388_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5390_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5391_: u8 = 0;
    let mut v___x_5393_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5394_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5395_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5379_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(
                    lean_box(0),
                    v_mvarId_5372_,
                    v_x_5373_,
                    v___y_5374_,
                    v___y_5375_,
                    v___y_5376_,
                    v___y_5377_,
                );
                if lean_obj_tag(v___x_5379_) == 0 {
                    v_a_5380_ = lean_ctor_get(v___x_5379_, 0);
                    v_isSharedCheck_5387_ = (!lean_is_exclusive(v___x_5379_)) as u8;
                    if v_isSharedCheck_5387_ == 0 {
                        v___x_5382_ = v___x_5379_;
                        v_isShared_5383_ = v_isSharedCheck_5387_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_5380_);
                        lean_dec(v___x_5379_);
                        v___x_5382_ = lean_box(0);
                        v_isShared_5383_ = v_isSharedCheck_5387_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_5388_ = lean_ctor_get(v___x_5379_, 0);
                    v_isSharedCheck_5395_ = (!lean_is_exclusive(v___x_5379_)) as u8;
                    if v_isSharedCheck_5395_ == 0 {
                        v___x_5390_ = v___x_5379_;
                        v_isShared_5391_ = v_isSharedCheck_5395_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_5388_);
                        lean_dec(v___x_5379_);
                        v___x_5390_ = lean_box(0);
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
                    v_reuseFailAlloc_5386_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5386_, 0, v_a_5380_);
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
                    v_reuseFailAlloc_5394_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5394_, 0, v_a_5388_);
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
    mut v_mvarId_5396_: *mut LeanObject,
    mut v_x_5397_: *mut LeanObject,
    mut v___y_5398_: *mut LeanObject,
    mut v___y_5399_: *mut LeanObject,
    mut v___y_5400_: *mut LeanObject,
    mut v___y_5401_: *mut LeanObject,
    mut v___y_5402_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5403_: *mut LeanObject = core::ptr::null_mut();
    v_res_5403_ = l_Lean_MVarId_withContext___at___00Lean_Meta_Try_Collector_main_spec__0___redArg(
        v_mvarId_5396_,
        v_x_5397_,
        v___y_5398_,
        v___y_5399_,
        v___y_5400_,
        v___y_5401_,
    );
    lean_dec(v___y_5401_);
    lean_dec_ref(v___y_5400_);
    lean_dec(v___y_5399_);
    lean_dec_ref(v___y_5398_);
    return v_res_5403_;
}
pub unsafe fn l_Lean_MVarId_withContext___at___00Lean_Meta_Try_Collector_main_spec__0(
    mut v_00_u03b1_5404_: *mut LeanObject,
    mut v_mvarId_5405_: *mut LeanObject,
    mut v_x_5406_: *mut LeanObject,
    mut v___y_5407_: *mut LeanObject,
    mut v___y_5408_: *mut LeanObject,
    mut v___y_5409_: *mut LeanObject,
    mut v___y_5410_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5412_: *mut LeanObject = core::ptr::null_mut();
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
    mut v_00_u03b1_5413_: *mut LeanObject,
    mut v_mvarId_5414_: *mut LeanObject,
    mut v_x_5415_: *mut LeanObject,
    mut v___y_5416_: *mut LeanObject,
    mut v___y_5417_: *mut LeanObject,
    mut v___y_5418_: *mut LeanObject,
    mut v___y_5419_: *mut LeanObject,
    mut v___y_5420_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5421_: *mut LeanObject = core::ptr::null_mut();
    v_res_5421_ = l_Lean_MVarId_withContext___at___00Lean_Meta_Try_Collector_main_spec__0(
        v_00_u03b1_5413_,
        v_mvarId_5414_,
        v_x_5415_,
        v___y_5416_,
        v___y_5417_,
        v___y_5418_,
        v___y_5419_,
    );
    lean_dec(v___y_5419_);
    lean_dec_ref(v___y_5418_);
    lean_dec(v___y_5417_);
    lean_dec_ref(v___y_5416_);
    return v_res_5421_;
}
pub unsafe fn l_Lean_Meta_Try_Collector_main___lam__0(
    mut v___x_5422_: *mut LeanObject,
    mut v___x_5423_: *mut LeanObject,
    mut v_mvarId_5424_: *mut LeanObject,
    mut v_config_5425_: *mut LeanObject,
    mut v___y_5426_: *mut LeanObject,
    mut v___y_5427_: *mut LeanObject,
    mut v___y_5428_: *mut LeanObject,
    mut v___y_5429_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5431_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5432_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5433_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5435_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5436_: u8 = 0;
    let mut v___x_5437_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5438_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5440_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5441_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5442_: u8 = 0;
    let mut v_unused_5443_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5444_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5446_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5447_: u8 = 0;
    let mut v___x_5449_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5450_: *mut LeanObject = core::ptr::null_mut();
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
                if lean_obj_tag(v___x_5433_) == 0 {
                    v_isSharedCheck_5442_ = (!lean_is_exclusive(v___x_5433_)) as u8;
                    if v_isSharedCheck_5442_ == 0 {
                        v_unused_5443_ = lean_ctor_get(v___x_5433_, 0);
                        lean_dec(v_unused_5443_);
                        v___x_5435_ = v___x_5433_;
                        v_isShared_5436_ = v_isSharedCheck_5442_;
                        state = 1;
                        continue;
                    } else {
                        lean_dec(v___x_5433_);
                        v___x_5435_ = lean_box(0);
                        v_isShared_5436_ = v_isSharedCheck_5442_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec(v___x_5432_);
                    lean_dec(v___x_5431_);
                    v_a_5444_ = lean_ctor_get(v___x_5433_, 0);
                    v_isSharedCheck_5451_ = (!lean_is_exclusive(v___x_5433_)) as u8;
                    if v_isSharedCheck_5451_ == 0 {
                        v___x_5446_ = v___x_5433_;
                        v_isShared_5447_ = v_isSharedCheck_5451_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_5444_);
                        lean_dec(v___x_5433_);
                        v___x_5446_ = lean_box(0);
                        v_isShared_5447_ = v_isSharedCheck_5451_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v___x_5437_ = lean_st_ref_get(v___x_5432_);
                lean_dec(v___x_5432_);
                lean_dec(v___x_5437_);
                v___x_5438_ = lean_st_ref_get(v___x_5431_);
                lean_dec(v___x_5431_);
                if v_isShared_5436_ == 0 {
                    lean_ctor_set(v___x_5435_, 0, v___x_5438_);
                    v___x_5440_ = v___x_5435_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5441_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5441_, 0, v___x_5438_);
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
                    v_reuseFailAlloc_5450_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5450_, 0, v_a_5444_);
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
    mut v___x_5452_: *mut LeanObject,
    mut v___x_5453_: *mut LeanObject,
    mut v_mvarId_5454_: *mut LeanObject,
    mut v_config_5455_: *mut LeanObject,
    mut v___y_5456_: *mut LeanObject,
    mut v___y_5457_: *mut LeanObject,
    mut v___y_5458_: *mut LeanObject,
    mut v___y_5459_: *mut LeanObject,
    mut v___y_5460_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5461_: *mut LeanObject = core::ptr::null_mut();
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
    lean_dec(v___y_5459_);
    lean_dec_ref(v___y_5458_);
    lean_dec(v___y_5457_);
    lean_dec_ref(v___y_5456_);
    lean_dec_ref(v_config_5455_);
    return v_res_5461_;
}
pub unsafe fn _init_l_Lean_Meta_Try_Collector_main___closed__0() -> *mut LeanObject {
    let mut v___x_5462_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5463_: *mut LeanObject = core::ptr::null_mut();
    v___x_5462_ = lean_unsigned_to_nat(64);
    v___x_5463_ = l_Lean_mkPtrSet___redArg(v___x_5462_);
    return v___x_5463_;
}
pub unsafe fn _init_l_Lean_Meta_Try_Collector_main___closed__2() -> *mut LeanObject {
    let mut v___x_5466_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5467_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5468_: *mut LeanObject = core::ptr::null_mut();
    v___x_5466_ = lean_box(0);
    v___x_5467_ = lean_unsigned_to_nat(16);
    v___x_5468_ = lean_mk_array(v___x_5467_, v___x_5466_);
    return v___x_5468_;
}
pub unsafe fn _init_l_Lean_Meta_Try_Collector_main___closed__3() -> *mut LeanObject {
    let mut v___x_5469_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5470_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5471_: *mut LeanObject = core::ptr::null_mut();
    v___x_5469_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Try_Collector_main___closed__2),
        core::ptr::addr_of_mut!(l_Lean_Meta_Try_Collector_main___closed__2_once),
        _init_l_Lean_Meta_Try_Collector_main___closed__2,
    );
    v___x_5470_ = lean_unsigned_to_nat(0);
    v___x_5471_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_5471_, 0, v___x_5470_);
    lean_ctor_set(v___x_5471_, 1, v___x_5469_);
    return v___x_5471_;
}
pub unsafe fn _init_l_Lean_Meta_Try_Collector_main___closed__4() -> *mut LeanObject {
    let mut v___x_5472_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5473_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5474_: *mut LeanObject = core::ptr::null_mut();
    v___x_5472_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Try_Collector_main___closed__3),
        core::ptr::addr_of_mut!(l_Lean_Meta_Try_Collector_main___closed__3_once),
        _init_l_Lean_Meta_Try_Collector_main___closed__3,
    );
    v___x_5473_ = l_Lean_Meta_Try_Collector_main___closed__1;
    v___x_5474_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_5474_, 0, v___x_5473_);
    lean_ctor_set(v___x_5474_, 1, v___x_5472_);
    return v___x_5474_;
}
pub unsafe fn _init_l_Lean_Meta_Try_Collector_main___closed__5() -> *mut LeanObject {
    let mut v___x_5475_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5476_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5477_: *mut LeanObject = core::ptr::null_mut();
    v___x_5475_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Try_Collector_main___closed__3),
        core::ptr::addr_of_mut!(l_Lean_Meta_Try_Collector_main___closed__3_once),
        _init_l_Lean_Meta_Try_Collector_main___closed__3,
    );
    v___x_5476_ = l_Lean_Meta_Try_Collector_main___closed__1;
    v___x_5477_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_5477_, 0, v___x_5476_);
    lean_ctor_set(v___x_5477_, 1, v___x_5475_);
    return v___x_5477_;
}
pub unsafe fn _init_l_Lean_Meta_Try_Collector_main___closed__6() -> *mut LeanObject {
    let mut v___x_5478_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5479_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5480_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5481_: *mut LeanObject = core::ptr::null_mut();
    v___x_5478_ = l_Lean_Meta_Try_Collector_main___closed__1;
    v___x_5479_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Try_Collector_main___closed__5),
        core::ptr::addr_of_mut!(l_Lean_Meta_Try_Collector_main___closed__5_once),
        _init_l_Lean_Meta_Try_Collector_main___closed__5,
    );
    v___x_5480_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Try_Collector_main___closed__4),
        core::ptr::addr_of_mut!(l_Lean_Meta_Try_Collector_main___closed__4_once),
        _init_l_Lean_Meta_Try_Collector_main___closed__4,
    );
    v___x_5481_ = lean_alloc_ctor(0, 6, (0) as u32);
    lean_ctor_set(v___x_5481_, 0, v___x_5480_);
    lean_ctor_set(v___x_5481_, 1, v___x_5480_);
    lean_ctor_set(v___x_5481_, 2, v___x_5480_);
    lean_ctor_set(v___x_5481_, 3, v___x_5479_);
    lean_ctor_set(v___x_5481_, 4, v___x_5478_);
    lean_ctor_set(v___x_5481_, 5, v___x_5480_);
    return v___x_5481_;
}
pub unsafe fn l_Lean_Meta_Try_Collector_main(
    mut v_mvarId_5482_: *mut LeanObject,
    mut v_config_5483_: *mut LeanObject,
    mut v_a_5484_: *mut LeanObject,
    mut v_a_5485_: *mut LeanObject,
    mut v_a_5486_: *mut LeanObject,
    mut v_a_5487_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5489_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5490_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_5491_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5492_: *mut LeanObject = core::ptr::null_mut();
    v___x_5489_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Try_Collector_main___closed__0),
        core::ptr::addr_of_mut!(l_Lean_Meta_Try_Collector_main___closed__0_once),
        _init_l_Lean_Meta_Try_Collector_main___closed__0,
    );
    v___x_5490_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Try_Collector_main___closed__6),
        core::ptr::addr_of_mut!(l_Lean_Meta_Try_Collector_main___closed__6_once),
        _init_l_Lean_Meta_Try_Collector_main___closed__6,
    );
    lean_inc(v_mvarId_5482_);
    v___f_5491_ = lean_alloc_closure(
        l_Lean_Meta_Try_Collector_main___lam__0___boxed as *mut core::ffi::c_void,
        9,
        4,
    );
    lean_closure_set(v___f_5491_, 0, v___x_5490_);
    lean_closure_set(v___f_5491_, 1, v___x_5489_);
    lean_closure_set(v___f_5491_, 2, v_mvarId_5482_);
    lean_closure_set(v___f_5491_, 3, v_config_5483_);
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
    mut v_mvarId_5493_: *mut LeanObject,
    mut v_config_5494_: *mut LeanObject,
    mut v_a_5495_: *mut LeanObject,
    mut v_a_5496_: *mut LeanObject,
    mut v_a_5497_: *mut LeanObject,
    mut v_a_5498_: *mut LeanObject,
    mut v_a_5499_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5500_: *mut LeanObject = core::ptr::null_mut();
    v_res_5500_ = l_Lean_Meta_Try_Collector_main(
        v_mvarId_5493_,
        v_config_5494_,
        v_a_5495_,
        v_a_5496_,
        v_a_5497_,
        v_a_5498_,
    );
    lean_dec(v_a_5498_);
    lean_dec_ref(v_a_5497_);
    lean_dec(v_a_5496_);
    lean_dec_ref(v_a_5495_);
    return v_res_5500_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Try_Collect_0__Lean_Meta_Try_collect_unsafe__1(
    mut v_mvarId_5501_: *mut LeanObject,
    mut v_config_5502_: *mut LeanObject,
    mut v_a_5503_: *mut LeanObject,
    mut v_a_5504_: *mut LeanObject,
    mut v_a_5505_: *mut LeanObject,
    mut v_a_5506_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5508_: *mut LeanObject = core::ptr::null_mut();
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
    mut v_mvarId_5509_: *mut LeanObject,
    mut v_config_5510_: *mut LeanObject,
    mut v_a_5511_: *mut LeanObject,
    mut v_a_5512_: *mut LeanObject,
    mut v_a_5513_: *mut LeanObject,
    mut v_a_5514_: *mut LeanObject,
    mut v_a_5515_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5516_: *mut LeanObject = core::ptr::null_mut();
    v_res_5516_ = l___private_Lean_Meta_Tactic_Try_Collect_0__Lean_Meta_Try_collect_unsafe__1(
        v_mvarId_5509_,
        v_config_5510_,
        v_a_5511_,
        v_a_5512_,
        v_a_5513_,
        v_a_5514_,
    );
    lean_dec(v_a_5514_);
    lean_dec_ref(v_a_5513_);
    lean_dec(v_a_5512_);
    lean_dec_ref(v_a_5511_);
    return v_res_5516_;
}
pub unsafe fn l_Lean_Meta_Try_collect(
    mut v_mvarId_5517_: *mut LeanObject,
    mut v_config_5518_: *mut LeanObject,
    mut v_a_5519_: *mut LeanObject,
    mut v_a_5520_: *mut LeanObject,
    mut v_a_5521_: *mut LeanObject,
    mut v_a_5522_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5524_: *mut LeanObject = core::ptr::null_mut();
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
    mut v_mvarId_5525_: *mut LeanObject,
    mut v_config_5526_: *mut LeanObject,
    mut v_a_5527_: *mut LeanObject,
    mut v_a_5528_: *mut LeanObject,
    mut v_a_5529_: *mut LeanObject,
    mut v_a_5530_: *mut LeanObject,
    mut v_a_5531_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5532_: *mut LeanObject = core::ptr::null_mut();
    v_res_5532_ = l_Lean_Meta_Try_collect(
        v_mvarId_5525_,
        v_config_5526_,
        v_a_5527_,
        v_a_5528_,
        v_a_5529_,
        v_a_5530_,
    );
    lean_dec(v_a_5530_);
    lean_dec_ref(v_a_5529_);
    lean_dec(v_a_5528_);
    lean_dec_ref(v_a_5527_);
    return v_res_5532_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Meta_Tactic_Try_Collect(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Try(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_LibrarySearch(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_FunIndCollect(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Meta_Tactic_Try_Collect(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Meta_Tactic_Try_Collect(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_Try(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Meta_Tactic_LibrarySearch(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Meta_Tactic_FunIndCollect(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Try_Collect(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Lean_Meta_Tactic_Try_Collect(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Lean_Meta_Tactic_Try_Collect(builtin);
}
