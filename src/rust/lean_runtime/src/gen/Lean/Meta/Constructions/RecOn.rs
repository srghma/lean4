// Lean compiler output
// Module: Lean.Meta.Constructions.RecOn
// Imports: Lean.AddDecl Lean.Meta.CompletionName
use crate::r#gen::Init::Data::Array::Basic::l_Array_append___redArg;
use crate::r#gen::Init::Data::Array::Subarray::l_Array_toSubarray___redArg;
use crate::r#gen::Init::Data::List::Basic::l_List_reverse___redArg;
use crate::r#gen::Init::Data::Slice::Array::Iterator::l_Subarray_copy___redArg;
use crate::r#gen::Init::Prelude::l_Lean_replaceRef;
use crate::r#gen::Lean::AddDecl::{
    initialize_Lean_AddDecl, l_Lean_addDecl, runtime_initialize_Lean_AddDecl,
};
use crate::r#gen::Lean::AuxRecursor::{l_Lean_markAuxRecursor, l_Lean_mkRecOnName};
use crate::r#gen::Lean::Data::Name::l_Lean_Name_isAnonymous;
use crate::r#gen::Lean::Data::Options::l_Lean_Options_empty;
use crate::r#gen::Lean::Data::PersistentHashMap::l_Lean_PersistentHashMap_mkEmptyEntriesArray;
use crate::r#gen::Lean::Declaration::l_Lean_mkRecName;
use crate::r#gen::Lean::Environment::{
    l_Lean_Environment_contains, l_Lean_Environment_find_x3f,
    l_Lean_Environment_getModuleIdxFor_x3f, l_Lean_Environment_hasUnsafe,
    l_Lean_Environment_header, l_Lean_Environment_setExporting,
    l_Lean_EnvironmentHeader_moduleNames,
};
use crate::r#gen::Lean::Exception::l_Lean_unknownIdentifierMessageTag;
use crate::r#gen::Lean::Expr::{l_Lean_Expr_const___override, l_Lean_mkAppN};
use crate::r#gen::Lean::Level::l_Lean_Level_param___override;
use crate::r#gen::Lean::Message::{
    l_Lean_MessageData_note, l_Lean_MessageData_ofConstName, l_Lean_MessageData_ofName,
    l_Lean_stringToMessageData,
};
use crate::r#gen::Lean::Meta::Basic::{
    l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAuxAux,
    l_Lean_Meta_mkForallFVars, l_Lean_Meta_mkLambdaFVars,
};
use crate::r#gen::Lean::Meta::CompletionName::{
    initialize_Lean_Meta_CompletionName, runtime_initialize_Lean_Meta_CompletionName,
};
use crate::r#gen::Lean::Modifiers::l_Lean_addProtected;
use crate::r#gen::Lean::PrivateName::l_Lean_isPrivateName;
use crate::r#gen::Lean::ReducibilityAttrs::l___private_Lean_ReducibilityAttrs_0__Lean_setReducibilityStatusCore;
use crate::lean_imports_rs::Init::Prelude::{
    lean_array_fget, lean_array_get, lean_array_get_size, lean_array_push,
    lean_mk_empty_array_with_capacity, lean_nat_add, lean_nat_dec_lt, lean_nat_sub,
};
use crate::lean_imports_rs::Init::System::ST::{
    lean_st_ref_get, lean_st_ref_set, lean_st_ref_take,
};
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_alloc_closure, lean_alloc_ctor, lean_apply_7, lean_box,
    lean_closure_set, lean_ctor_get, lean_ctor_get_uint8, lean_ctor_set, lean_ctor_set_tag,
    lean_ctor_set_uint8, lean_ctor_set_usize, lean_dec, lean_dec_ref, lean_dec_ref_known,
    lean_del_object, lean_inc, lean_inc_n, lean_inc_ref, lean_inc_ref_n, lean_io_result_is_error,
    lean_io_result_mk_ok, lean_is_exclusive, lean_obj_once, lean_obj_tag, lean_unbox,
    lean_unsigned_to_nat,
};
pub static l_mkRecOn___lam__0___closed__0_value: LeanArrayObject<0> = LeanArrayObject {
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
static mut l_mkRecOn___lam__0___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_mkRecOn___lam__0___closed__0_value) as *mut LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkRecOn_spec__0_spec__0_spec__3_spec__10_spec__11_spec__12___redArg___closed__0_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkRecOn_spec__0_spec__0_spec__3_spec__10_spec__11_spec__12___redArg___closed__0: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkRecOn_spec__0_spec__0_spec__3_spec__10_spec__11_spec__12___redArg___closed__1_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkRecOn_spec__0_spec__0_spec__3_spec__10_spec__11_spec__12___redArg___closed__1: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkRecOn_spec__0_spec__0_spec__3_spec__10_spec__11_spec__12___redArg___closed__2_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkRecOn_spec__0_spec__0_spec__3_spec__10_spec__11_spec__12___redArg___closed__2: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkRecOn_spec__0_spec__0_spec__3_spec__10_spec__11_spec__12___redArg___closed__3_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkRecOn_spec__0_spec__0_spec__3_spec__10_spec__11_spec__12___redArg___closed__3: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkRecOn_spec__0_spec__0_spec__3_spec__10_spec__11_spec__12___redArg___closed__4_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkRecOn_spec__0_spec__0_spec__3_spec__10_spec__11_spec__12___redArg___closed__4: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkRecOn_spec__0_spec__0_spec__3_spec__10_spec__11_spec__12___redArg___closed__5_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkRecOn_spec__0_spec__0_spec__3_spec__10_spec__11_spec__12___redArg___closed__5: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkRecOn_spec__0_spec__0_spec__3_spec__10_spec__11_spec__12___redArg___closed__6_value: LeanStringObject<24> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 24, m_capacity: 24, m_length: 23, m_data: [65, 32, 112, 114, 105, 118, 97, 116, 101, 32, 100, 101, 99, 108, 97, 114, 97, 116, 105, 111, 110, 32, 96, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkRecOn_spec__0_spec__0_spec__3_spec__10_spec__11_spec__12___redArg___closed__6: *mut LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkRecOn_spec__0_spec__0_spec__3_spec__10_spec__11_spec__12___redArg___closed__6_value) as *mut LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkRecOn_spec__0_spec__0_spec__3_spec__10_spec__11_spec__12___redArg___closed__7_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkRecOn_spec__0_spec__0_spec__3_spec__10_spec__11_spec__12___redArg___closed__7: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkRecOn_spec__0_spec__0_spec__3_spec__10_spec__11_spec__12___redArg___closed__8_value: LeanStringObject<79> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 79, m_capacity: 79, m_length: 78, m_data: [96, 32, 40, 102, 114, 111, 109, 32, 116, 104, 101, 32, 99, 117, 114, 114, 101, 110, 116, 32, 109, 111, 100, 117, 108, 101, 41, 32, 101, 120, 105, 115, 116, 115, 32, 98, 117, 116, 32, 119, 111, 117, 108, 100, 32, 110, 101, 101, 100, 32, 116, 111, 32, 98, 101, 32, 112, 117, 98, 108, 105, 99, 32, 116, 111, 32, 97, 99, 99, 101, 115, 115, 32, 104, 101, 114, 101, 46, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkRecOn_spec__0_spec__0_spec__3_spec__10_spec__11_spec__12___redArg___closed__8: *mut LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkRecOn_spec__0_spec__0_spec__3_spec__10_spec__11_spec__12___redArg___closed__8_value) as *mut LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkRecOn_spec__0_spec__0_spec__3_spec__10_spec__11_spec__12___redArg___closed__9_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkRecOn_spec__0_spec__0_spec__3_spec__10_spec__11_spec__12___redArg___closed__9: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkRecOn_spec__0_spec__0_spec__3_spec__10_spec__11_spec__12___redArg___closed__10_value: LeanStringObject<23> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 23, m_capacity: 23, m_length: 22, m_data: [65, 32, 112, 117, 98, 108, 105, 99, 32, 100, 101, 99, 108, 97, 114, 97, 116, 105, 111, 110, 32, 96, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkRecOn_spec__0_spec__0_spec__3_spec__10_spec__11_spec__12___redArg___closed__10: *mut LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkRecOn_spec__0_spec__0_spec__3_spec__10_spec__11_spec__12___redArg___closed__10_value) as *mut LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkRecOn_spec__0_spec__0_spec__3_spec__10_spec__11_spec__12___redArg___closed__11_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkRecOn_spec__0_spec__0_spec__3_spec__10_spec__11_spec__12___redArg___closed__11: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkRecOn_spec__0_spec__0_spec__3_spec__10_spec__11_spec__12___redArg___closed__12_value: LeanStringObject<68> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 68, m_capacity: 68, m_length: 67, m_data: [96, 32, 101, 120, 105, 115, 116, 115, 32, 98, 117, 116, 32, 105, 115, 32, 105, 109, 112, 111, 114, 116, 101, 100, 32, 112, 114, 105, 118, 97, 116, 101, 108, 121, 59, 32, 99, 111, 110, 115, 105, 100, 101, 114, 32, 97, 100, 100, 105, 110, 103, 32, 96, 112, 117, 98, 108, 105, 99, 32, 105, 109, 112, 111, 114, 116, 32, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkRecOn_spec__0_spec__0_spec__3_spec__10_spec__11_spec__12___redArg___closed__12: *mut LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkRecOn_spec__0_spec__0_spec__3_spec__10_spec__11_spec__12___redArg___closed__12_value) as *mut LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkRecOn_spec__0_spec__0_spec__3_spec__10_spec__11_spec__12___redArg___closed__13_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkRecOn_spec__0_spec__0_spec__3_spec__10_spec__11_spec__12___redArg___closed__13: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkRecOn_spec__0_spec__0_spec__3_spec__10_spec__11_spec__12___redArg___closed__14_value: LeanStringObject<3> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [96, 46, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkRecOn_spec__0_spec__0_spec__3_spec__10_spec__11_spec__12___redArg___closed__14: *mut LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkRecOn_spec__0_spec__0_spec__3_spec__10_spec__11_spec__12___redArg___closed__14_value) as *mut LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkRecOn_spec__0_spec__0_spec__3_spec__10_spec__11_spec__12___redArg___closed__15_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkRecOn_spec__0_spec__0_spec__3_spec__10_spec__11_spec__12___redArg___closed__15: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkRecOn_spec__0_spec__0_spec__3_spec__10_spec__11_spec__12___redArg___closed__16_value: LeanStringObject<10> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [96, 32, 40, 102, 114, 111, 109, 32, 96, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkRecOn_spec__0_spec__0_spec__3_spec__10_spec__11_spec__12___redArg___closed__16: *mut LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkRecOn_spec__0_spec__0_spec__3_spec__10_spec__11_spec__12___redArg___closed__16_value) as *mut LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkRecOn_spec__0_spec__0_spec__3_spec__10_spec__11_spec__12___redArg___closed__17_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkRecOn_spec__0_spec__0_spec__3_spec__10_spec__11_spec__12___redArg___closed__17: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkRecOn_spec__0_spec__0_spec__3_spec__10_spec__11_spec__12___redArg___closed__18_value: LeanStringObject<54> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 54, m_capacity: 54, m_length: 53, m_data: [96, 41, 32, 101, 120, 105, 115, 116, 115, 32, 98, 117, 116, 32, 119, 111, 117, 108, 100, 32, 110, 101, 101, 100, 32, 116, 111, 32, 98, 101, 32, 112, 117, 98, 108, 105, 99, 32, 116, 111, 32, 97, 99, 99, 101, 115, 115, 32, 104, 101, 114, 101, 46, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkRecOn_spec__0_spec__0_spec__3_spec__10_spec__11_spec__12___redArg___closed__18: *mut LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkRecOn_spec__0_spec__0_spec__3_spec__10_spec__11_spec__12___redArg___closed__18_value) as *mut LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkRecOn_spec__0_spec__0_spec__3_spec__10_spec__11_spec__12___redArg___closed__19_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkRecOn_spec__0_spec__0_spec__3_spec__10_spec__11_spec__12___redArg___closed__19: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkRecOn_spec__0_spec__0_spec__3___redArg___closed__0_value: LeanStringObject<19> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 19, m_capacity: 19, m_length: 18, m_data: [85, 110, 107, 110, 111, 119, 110, 32, 99, 111, 110, 115, 116, 97, 110, 116, 32, 96, 0]};
static mut l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkRecOn_spec__0_spec__0_spec__3___redArg___closed__0: *mut LeanObject = core::ptr::addr_of!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkRecOn_spec__0_spec__0_spec__3___redArg___closed__0_value) as *mut LeanObject;
static mut l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkRecOn_spec__0_spec__0_spec__3___redArg___closed__1_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkRecOn_spec__0_spec__0_spec__3___redArg___closed__1: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkRecOn_spec__0_spec__0_spec__3___redArg___closed__2_value: LeanStringObject<2> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [96, 0]};
static mut l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkRecOn_spec__0_spec__0_spec__3___redArg___closed__2: *mut LeanObject = core::ptr::addr_of!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkRecOn_spec__0_spec__0_spec__3___redArg___closed__2_value) as *mut LeanObject;
static mut l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkRecOn_spec__0_spec__0_spec__3___redArg___closed__3_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkRecOn_spec__0_spec__0_spec__3___redArg___closed__3: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00mkRecOn_spec__5_spec__6___redArg___closed__0_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00mkRecOn_spec__5_spec__6___redArg___closed__0: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00mkRecOn_spec__5_spec__6___redArg___closed__1_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00mkRecOn_spec__5_spec__6___redArg___closed__1: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00mkRecOn_spec__5_spec__6___redArg___closed__2_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00mkRecOn_spec__5_spec__6___redArg___closed__2: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00mkRecOn_spec__5_spec__6___redArg___closed__3_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00mkRecOn_spec__5_spec__6___redArg___closed__3: *mut LeanObject = core::ptr::null_mut();
pub static l_mkRecOn___closed__0_value: LeanStringObject<15> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 15,
    m_capacity: 15,
    m_length: 14,
    m_data: [
        32, 110, 111, 116, 32, 97, 32, 114, 101, 99, 105, 110, 102, 111, 0,
    ],
};
static mut l_mkRecOn___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_mkRecOn___closed__0_value) as *mut LeanObject;
static mut l_mkRecOn___closed__1_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_mkRecOn___closed__1: *mut LeanObject = core::ptr::null_mut();
pub unsafe fn l_Lean_mkDefinitionValInferringUnsafe___at___00mkRecOn_spec__3___redArg(
    mut v_name_883_: *mut LeanObject,
    mut v_levelParams_884_: *mut LeanObject,
    mut v_type_885_: *mut LeanObject,
    mut v_value_886_: *mut LeanObject,
    mut v_hints_887_: *mut LeanObject,
    mut v___y_888_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_890_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_892_: u8 = 0;
    let mut v___x_893_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_894_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_895_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_896_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_897_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_899_: u8 = 0;
    let mut v___x_900_: u8 = 0;
    let mut v___x_901_: u8 = 0;
    let mut v_env_902_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_903_: u8 = 0;
    let mut v___x_904_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_890_ = lean_st_ref_get(v___y_888_);
                v_env_902_ = lean_ctor_get(v___x_890_, 0);
                lean_inc_ref_n(v_env_902_, 2);
                lean_dec(v___x_890_);
                v___x_903_ = l_Lean_Environment_hasUnsafe(v_env_902_, v_type_885_);
                if v___x_903_ == 0 {
                    v___x_904_ = l_Lean_Environment_hasUnsafe(v_env_902_, v_value_886_);
                    v___y_899_ = v___x_904_;
                    state = 2;
                    continue;
                } else {
                    lean_dec_ref(v_env_902_);
                    v___y_899_ = v___x_903_;
                    state = 2;
                    continue;
                }
            }
            1 => {
                lean_inc(v_name_883_);
                v___x_893_ = lean_alloc_ctor(0, 3, (0) as u32);
                lean_ctor_set(v___x_893_, 0, v_name_883_);
                lean_ctor_set(v___x_893_, 1, v_levelParams_884_);
                lean_ctor_set(v___x_893_, 2, v_type_885_);
                v___x_894_ = lean_box(0);
                v___x_895_ = lean_alloc_ctor(1, 2, (0) as u32);
                lean_ctor_set(v___x_895_, 0, v_name_883_);
                lean_ctor_set(v___x_895_, 1, v___x_894_);
                v___x_896_ = lean_alloc_ctor(0, 4, (1) as u32);
                lean_ctor_set(v___x_896_, 0, v___x_893_);
                lean_ctor_set(v___x_896_, 1, v_value_886_);
                lean_ctor_set(v___x_896_, 2, v_hints_887_);
                lean_ctor_set(v___x_896_, 3, v___x_895_);
                lean_ctor_set_uint8(
                    v___x_896_,
                    (core::mem::size_of::<*mut LeanObject>() * 4) as u32,
                    v___y_892_,
                );
                v___x_897_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_897_, 0, v___x_896_);
                return v___x_897_;
            }
            2 => {
                if v___y_899_ == 0 {
                    v___x_900_ = 1;
                    v___y_892_ = v___x_900_;
                    state = 1;
                    continue;
                } else {
                    v___x_901_ = 0;
                    v___y_892_ = v___x_901_;
                    state = 1;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_mkDefinitionValInferringUnsafe___at___00mkRecOn_spec__3___redArg___boxed(
    mut v_name_905_: *mut LeanObject,
    mut v_levelParams_906_: *mut LeanObject,
    mut v_type_907_: *mut LeanObject,
    mut v_value_908_: *mut LeanObject,
    mut v_hints_909_: *mut LeanObject,
    mut v___y_910_: *mut LeanObject,
    mut v___y_911_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_912_: *mut LeanObject = core::ptr::null_mut();
    v_res_912_ = l_Lean_mkDefinitionValInferringUnsafe___at___00mkRecOn_spec__3___redArg(
        v_name_905_,
        v_levelParams_906_,
        v_type_907_,
        v_value_908_,
        v_hints_909_,
        v___y_910_,
    );
    lean_dec(v___y_910_);
    return v_res_912_;
}
pub unsafe fn l_Lean_mkDefinitionValInferringUnsafe___at___00mkRecOn_spec__3(
    mut v_name_913_: *mut LeanObject,
    mut v_levelParams_914_: *mut LeanObject,
    mut v_type_915_: *mut LeanObject,
    mut v_value_916_: *mut LeanObject,
    mut v_hints_917_: *mut LeanObject,
    mut v___y_918_: *mut LeanObject,
    mut v___y_919_: *mut LeanObject,
    mut v___y_920_: *mut LeanObject,
    mut v___y_921_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_923_: *mut LeanObject = core::ptr::null_mut();
    v___x_923_ = l_Lean_mkDefinitionValInferringUnsafe___at___00mkRecOn_spec__3___redArg(
        v_name_913_,
        v_levelParams_914_,
        v_type_915_,
        v_value_916_,
        v_hints_917_,
        v___y_921_,
    );
    return v___x_923_;
}
pub unsafe fn l_Lean_mkDefinitionValInferringUnsafe___at___00mkRecOn_spec__3___boxed(
    mut v_name_924_: *mut LeanObject,
    mut v_levelParams_925_: *mut LeanObject,
    mut v_type_926_: *mut LeanObject,
    mut v_value_927_: *mut LeanObject,
    mut v_hints_928_: *mut LeanObject,
    mut v___y_929_: *mut LeanObject,
    mut v___y_930_: *mut LeanObject,
    mut v___y_931_: *mut LeanObject,
    mut v___y_932_: *mut LeanObject,
    mut v___y_933_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_934_: *mut LeanObject = core::ptr::null_mut();
    v_res_934_ = l_Lean_mkDefinitionValInferringUnsafe___at___00mkRecOn_spec__3(
        v_name_924_,
        v_levelParams_925_,
        v_type_926_,
        v_value_927_,
        v_hints_928_,
        v___y_929_,
        v___y_930_,
        v___y_931_,
        v___y_932_,
    );
    lean_dec(v___y_932_);
    lean_dec_ref(v___y_931_);
    lean_dec(v___y_930_);
    lean_dec_ref(v___y_929_);
    return v_res_934_;
}
pub unsafe fn l_Lean_Meta_forallTelescope___at___00mkRecOn_spec__4___redArg___lam__0(
    mut v_k_935_: *mut LeanObject,
    mut v_b_936_: *mut LeanObject,
    mut v_c_937_: *mut LeanObject,
    mut v___y_938_: *mut LeanObject,
    mut v___y_939_: *mut LeanObject,
    mut v___y_940_: *mut LeanObject,
    mut v___y_941_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_943_: *mut LeanObject = core::ptr::null_mut();
    lean_inc(v___y_941_);
    lean_inc_ref(v___y_940_);
    lean_inc(v___y_939_);
    lean_inc_ref(v___y_938_);
    v___x_943_ = lean_apply_7(
        v_k_935_,
        v_b_936_,
        v_c_937_,
        v___y_938_,
        v___y_939_,
        v___y_940_,
        v___y_941_,
        lean_box(0),
    );
    return v___x_943_;
}
pub unsafe fn l_Lean_Meta_forallTelescope___at___00mkRecOn_spec__4___redArg___lam__0___boxed(
    mut v_k_944_: *mut LeanObject,
    mut v_b_945_: *mut LeanObject,
    mut v_c_946_: *mut LeanObject,
    mut v___y_947_: *mut LeanObject,
    mut v___y_948_: *mut LeanObject,
    mut v___y_949_: *mut LeanObject,
    mut v___y_950_: *mut LeanObject,
    mut v___y_951_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_952_: *mut LeanObject = core::ptr::null_mut();
    v_res_952_ = l_Lean_Meta_forallTelescope___at___00mkRecOn_spec__4___redArg___lam__0(
        v_k_944_, v_b_945_, v_c_946_, v___y_947_, v___y_948_, v___y_949_, v___y_950_,
    );
    lean_dec(v___y_950_);
    lean_dec_ref(v___y_949_);
    lean_dec(v___y_948_);
    lean_dec_ref(v___y_947_);
    return v_res_952_;
}
pub unsafe fn l_Lean_Meta_forallTelescope___at___00mkRecOn_spec__4___redArg(
    mut v_type_953_: *mut LeanObject,
    mut v_k_954_: *mut LeanObject,
    mut v_cleanupAnnotations_955_: u8,
    mut v___y_956_: *mut LeanObject,
    mut v___y_957_: *mut LeanObject,
    mut v___y_958_: *mut LeanObject,
    mut v___y_959_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_961_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_962_: u8 = 0;
    let mut v___x_963_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_964_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_965_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_967_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_968_: u8 = 0;
    let mut v___x_970_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_971_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_972_: u8 = 0;
    let mut v_a_973_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_975_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_976_: u8 = 0;
    let mut v___x_978_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_979_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_980_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___f_961_ = lean_alloc_closure(
                    l_Lean_Meta_forallTelescope___at___00mkRecOn_spec__4___redArg___lam__0___boxed
                        as *mut core::ffi::c_void,
                    8,
                    1,
                );
                lean_closure_set(v___f_961_, 0, v_k_954_);
                v___x_962_ = 0;
                v___x_963_ = lean_box(0);
                v___x_964_ = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAuxAux(
                    lean_box(0),
                    v___x_962_,
                    v___x_963_,
                    v_type_953_,
                    v___f_961_,
                    v_cleanupAnnotations_955_,
                    v___x_962_,
                    v___y_956_,
                    v___y_957_,
                    v___y_958_,
                    v___y_959_,
                );
                if lean_obj_tag(v___x_964_) == 0 {
                    v_a_965_ = lean_ctor_get(v___x_964_, 0);
                    v_isSharedCheck_972_ = (!lean_is_exclusive(v___x_964_)) as u8;
                    if v_isSharedCheck_972_ == 0 {
                        v___x_967_ = v___x_964_;
                        v_isShared_968_ = v_isSharedCheck_972_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_965_);
                        lean_dec(v___x_964_);
                        v___x_967_ = lean_box(0);
                        v_isShared_968_ = v_isSharedCheck_972_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_973_ = lean_ctor_get(v___x_964_, 0);
                    v_isSharedCheck_980_ = (!lean_is_exclusive(v___x_964_)) as u8;
                    if v_isSharedCheck_980_ == 0 {
                        v___x_975_ = v___x_964_;
                        v_isShared_976_ = v_isSharedCheck_980_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_973_);
                        lean_dec(v___x_964_);
                        v___x_975_ = lean_box(0);
                        v_isShared_976_ = v_isSharedCheck_980_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_968_ == 0 {
                    v___x_970_ = v___x_967_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_971_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_971_, 0, v_a_965_);
                    v___x_970_ = v_reuseFailAlloc_971_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_970_;
            }
            3 => {
                if v_isShared_976_ == 0 {
                    v___x_978_ = v___x_975_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_979_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_979_, 0, v_a_973_);
                    v___x_978_ = v_reuseFailAlloc_979_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_978_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_forallTelescope___at___00mkRecOn_spec__4___redArg___boxed(
    mut v_type_981_: *mut LeanObject,
    mut v_k_982_: *mut LeanObject,
    mut v_cleanupAnnotations_983_: *mut LeanObject,
    mut v___y_984_: *mut LeanObject,
    mut v___y_985_: *mut LeanObject,
    mut v___y_986_: *mut LeanObject,
    mut v___y_987_: *mut LeanObject,
    mut v___y_988_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_cleanupAnnotations_boxed_989_: u8 = 0;
    let mut v_res_990_: *mut LeanObject = core::ptr::null_mut();
    v_cleanupAnnotations_boxed_989_ = (lean_unbox(v_cleanupAnnotations_983_) as u8);
    v_res_990_ = l_Lean_Meta_forallTelescope___at___00mkRecOn_spec__4___redArg(
        v_type_981_,
        v_k_982_,
        v_cleanupAnnotations_boxed_989_,
        v___y_984_,
        v___y_985_,
        v___y_986_,
        v___y_987_,
    );
    lean_dec(v___y_987_);
    lean_dec_ref(v___y_986_);
    lean_dec(v___y_985_);
    lean_dec_ref(v___y_984_);
    return v_res_990_;
}
pub unsafe fn l_Lean_Meta_forallTelescope___at___00mkRecOn_spec__4(
    mut v_00_u03b1_991_: *mut LeanObject,
    mut v_type_992_: *mut LeanObject,
    mut v_k_993_: *mut LeanObject,
    mut v_cleanupAnnotations_994_: u8,
    mut v___y_995_: *mut LeanObject,
    mut v___y_996_: *mut LeanObject,
    mut v___y_997_: *mut LeanObject,
    mut v___y_998_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1000_: *mut LeanObject = core::ptr::null_mut();
    v___x_1000_ = l_Lean_Meta_forallTelescope___at___00mkRecOn_spec__4___redArg(
        v_type_992_,
        v_k_993_,
        v_cleanupAnnotations_994_,
        v___y_995_,
        v___y_996_,
        v___y_997_,
        v___y_998_,
    );
    return v___x_1000_;
}
pub unsafe fn l_Lean_Meta_forallTelescope___at___00mkRecOn_spec__4___boxed(
    mut v_00_u03b1_1001_: *mut LeanObject,
    mut v_type_1002_: *mut LeanObject,
    mut v_k_1003_: *mut LeanObject,
    mut v_cleanupAnnotations_1004_: *mut LeanObject,
    mut v___y_1005_: *mut LeanObject,
    mut v___y_1006_: *mut LeanObject,
    mut v___y_1007_: *mut LeanObject,
    mut v___y_1008_: *mut LeanObject,
    mut v___y_1009_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_cleanupAnnotations_boxed_1010_: u8 = 0;
    let mut v_res_1011_: *mut LeanObject = core::ptr::null_mut();
    v_cleanupAnnotations_boxed_1010_ = (lean_unbox(v_cleanupAnnotations_1004_) as u8);
    v_res_1011_ = l_Lean_Meta_forallTelescope___at___00mkRecOn_spec__4(
        v_00_u03b1_1001_,
        v_type_1002_,
        v_k_1003_,
        v_cleanupAnnotations_boxed_1010_,
        v___y_1005_,
        v___y_1006_,
        v___y_1007_,
        v___y_1008_,
    );
    lean_dec(v___y_1008_);
    lean_dec_ref(v___y_1007_);
    lean_dec(v___y_1006_);
    lean_dec_ref(v___y_1005_);
    return v_res_1011_;
}
pub unsafe fn l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00mkRecOn_spec__2___redArg(
    mut v_a_1012_: *mut LeanObject,
    mut v_b_1013_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_array_1014_: *mut LeanObject = core::ptr::null_mut();
    let mut v_start_1015_: *mut LeanObject = core::ptr::null_mut();
    let mut v_stop_1016_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1018_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1019_: u8 = 0;
    let mut v___x_1020_: u8 = 0;
    let mut v___x_1021_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1022_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1024_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1025_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1026_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1028_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1029_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_array_1014_ = lean_ctor_get(v_a_1012_, 0);
                v_start_1015_ = lean_ctor_get(v_a_1012_, 1);
                v_stop_1016_ = lean_ctor_get(v_a_1012_, 2);
                v_isSharedCheck_1029_ = (!lean_is_exclusive(v_a_1012_)) as u8;
                if v_isSharedCheck_1029_ == 0 {
                    v___x_1018_ = v_a_1012_;
                    v_isShared_1019_ = v_isSharedCheck_1029_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_stop_1016_);
                    lean_inc(v_start_1015_);
                    lean_inc(v_array_1014_);
                    lean_dec(v_a_1012_);
                    v___x_1018_ = lean_box(0);
                    v_isShared_1019_ = v_isSharedCheck_1029_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_1020_ = lean_nat_dec_lt(v_start_1015_, v_stop_1016_);
                if v___x_1020_ == 0 {
                    lean_del_object(v___x_1018_);
                    lean_dec(v_stop_1016_);
                    lean_dec(v_start_1015_);
                    lean_dec_ref(v_array_1014_);
                    return v_b_1013_;
                } else {
                    v___x_1021_ = lean_unsigned_to_nat(1);
                    v___x_1022_ = lean_nat_add(v_start_1015_, v___x_1021_);
                    lean_inc_ref(v_array_1014_);
                    if v_isShared_1019_ == 0 {
                        lean_ctor_set(v___x_1018_, 1, v___x_1022_);
                        v___x_1024_ = v___x_1018_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_1028_ = lean_alloc_ctor(0, 3, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_1028_, 0, v_array_1014_);
                        lean_ctor_set(v_reuseFailAlloc_1028_, 1, v___x_1022_);
                        lean_ctor_set(v_reuseFailAlloc_1028_, 2, v_stop_1016_);
                        v___x_1024_ = v_reuseFailAlloc_1028_;
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                v___x_1025_ = lean_array_fget(v_array_1014_, v_start_1015_);
                lean_dec(v_start_1015_);
                lean_dec_ref(v_array_1014_);
                v___x_1026_ = lean_array_push(v_b_1013_, v___x_1025_);
                v_a_1012_ = v___x_1024_;
                v_b_1013_ = v___x_1026_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_mapTR_loop___at___00mkRecOn_spec__1(
    mut v_a_1030_: *mut LeanObject,
    mut v_a_1031_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1032_: *mut LeanObject = core::ptr::null_mut();
    let mut v_head_1033_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_1034_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1036_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1037_: u8 = 0;
    let mut v___x_1038_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1040_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1042_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1043_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_a_1030_) == 0 {
                    v___x_1032_ = l_List_reverse___redArg(v_a_1031_);
                    return v___x_1032_;
                } else {
                    v_head_1033_ = lean_ctor_get(v_a_1030_, 0);
                    v_tail_1034_ = lean_ctor_get(v_a_1030_, 1);
                    v_isSharedCheck_1043_ = (!lean_is_exclusive(v_a_1030_)) as u8;
                    if v_isSharedCheck_1043_ == 0 {
                        v___x_1036_ = v_a_1030_;
                        v_isShared_1037_ = v_isSharedCheck_1043_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_tail_1034_);
                        lean_inc(v_head_1033_);
                        lean_dec(v_a_1030_);
                        v___x_1036_ = lean_box(0);
                        v_isShared_1037_ = v_isSharedCheck_1043_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_1038_ = l_Lean_Level_param___override(v_head_1033_);
                if v_isShared_1037_ == 0 {
                    lean_ctor_set(v___x_1036_, 1, v_a_1031_);
                    lean_ctor_set(v___x_1036_, 0, v___x_1038_);
                    v___x_1040_ = v___x_1036_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1042_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1042_, 0, v___x_1038_);
                    lean_ctor_set(v_reuseFailAlloc_1042_, 1, v_a_1031_);
                    v___x_1040_ = v_reuseFailAlloc_1042_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_a_1030_ = v_tail_1034_;
                v_a_1031_ = v___x_1040_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_mkRecOn___lam__0(
    mut v_levelParams_1046_: *mut LeanObject,
    mut v_name_1047_: *mut LeanObject,
    mut v_numMinors_1048_: *mut LeanObject,
    mut v_numIndices_1049_: *mut LeanObject,
    mut v_n_1050_: *mut LeanObject,
    mut v_xs_1051_: *mut LeanObject,
    mut v_t_1052_: *mut LeanObject,
    mut v___y_1053_: *mut LeanObject,
    mut v___y_1054_: *mut LeanObject,
    mut v___y_1055_: *mut LeanObject,
    mut v___y_1056_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1058_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1059_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1060_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1061_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1062_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1063_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1064_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1065_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1066_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1067_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1068_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1069_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1070_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1071_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1072_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1073_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1074_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1075_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1076_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1077_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1078_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1079_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1080_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1081_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1082_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1083_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1084_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1085_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1086_: u8 = 0;
    let mut v___x_1087_: u8 = 0;
    let mut v___x_1088_: u8 = 0;
    let mut v___x_1089_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1090_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1091_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1092_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1093_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1094_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1095_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1096_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1098_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1099_: u8 = 0;
    let mut v___x_1101_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1102_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1103_: u8 = 0;
    let mut v_a_1104_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1106_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1107_: u8 = 0;
    let mut v___x_1109_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1110_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1111_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1058_ = lean_box(0);
                lean_inc(v_levelParams_1046_);
                v___x_1059_ =
                    l_List_mapTR_loop___at___00mkRecOn_spec__1(v_levelParams_1046_, v___x_1058_);
                v___x_1060_ = l_Lean_Expr_const___override(v_name_1047_, v___x_1059_);
                v___x_1061_ = l_Lean_mkAppN(v___x_1060_, v_xs_1051_);
                v___x_1062_ = lean_array_get_size(v_xs_1051_);
                v___x_1063_ = lean_nat_sub(v___x_1062_, v_numMinors_1048_);
                v___x_1064_ = lean_nat_sub(v___x_1063_, v_numIndices_1049_);
                lean_dec(v___x_1063_);
                v___x_1065_ = lean_unsigned_to_nat(1);
                v___x_1066_ = lean_nat_sub(v___x_1064_, v___x_1065_);
                lean_dec(v___x_1064_);
                v___x_1067_ = lean_unsigned_to_nat(0);
                lean_inc(v___x_1066_);
                lean_inc_ref_n(v_xs_1051_, 2);
                v___x_1068_ = l_Array_toSubarray___redArg(v_xs_1051_, v___x_1067_, v___x_1066_);
                v___x_1069_ = lean_nat_add(v___x_1066_, v_numMinors_1048_);
                v___x_1070_ = lean_nat_add(v___x_1069_, v___x_1065_);
                v___x_1071_ = lean_nat_add(v___x_1070_, v_numIndices_1049_);
                lean_dec(v___x_1070_);
                lean_inc(v___x_1069_);
                v___x_1072_ = l_Array_toSubarray___redArg(v_xs_1051_, v___x_1069_, v___x_1071_);
                v___x_1073_ = l_mkRecOn___lam__0___closed__0;
                v___x_1074_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00mkRecOn_spec__2___redArg(v___x_1068_, v___x_1073_);
                v___x_1075_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00mkRecOn_spec__2___redArg(v___x_1072_, v___x_1073_);
                v_a_1076_ = l_Array_append___redArg(v___x_1074_, v___x_1075_);
                lean_dec_ref(v___x_1075_);
                v___x_1077_ = lean_array_get_size(v_a_1076_);
                v___x_1078_ = l_Array_toSubarray___redArg(v_a_1076_, v___x_1067_, v___x_1077_);
                v___x_1079_ = l_Array_toSubarray___redArg(v_xs_1051_, v___x_1066_, v___x_1069_);
                v___x_1080_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00mkRecOn_spec__2___redArg(v___x_1078_, v___x_1073_);
                v___x_1081_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00mkRecOn_spec__2___redArg(v___x_1079_, v___x_1073_);
                v_a_1082_ = l_Array_append___redArg(v___x_1080_, v___x_1081_);
                lean_dec_ref(v___x_1081_);
                v___x_1083_ = lean_array_get_size(v_a_1082_);
                v___x_1084_ = l_Array_toSubarray___redArg(v_a_1082_, v___x_1067_, v___x_1083_);
                v___x_1085_ = l_Subarray_copy___redArg(v___x_1084_);
                v___x_1086_ = 0;
                v___x_1087_ = 1;
                v___x_1088_ = 1;
                v___x_1089_ = l_Lean_Meta_mkForallFVars(
                    v___x_1085_,
                    v_t_1052_,
                    v___x_1086_,
                    v___x_1087_,
                    v___x_1087_,
                    v___x_1088_,
                    v___y_1053_,
                    v___y_1054_,
                    v___y_1055_,
                    v___y_1056_,
                );
                if lean_obj_tag(v___x_1089_) == 0 {
                    v_a_1090_ = lean_ctor_get(v___x_1089_, 0);
                    lean_inc(v_a_1090_);
                    lean_dec_ref_known(v___x_1089_, 1);
                    v___x_1091_ = l_Lean_Meta_mkLambdaFVars(
                        v___x_1085_,
                        v___x_1061_,
                        v___x_1086_,
                        v___x_1087_,
                        v___x_1086_,
                        v___x_1087_,
                        v___x_1088_,
                        v___y_1053_,
                        v___y_1054_,
                        v___y_1055_,
                        v___y_1056_,
                    );
                    lean_dec_ref(v___x_1085_);
                    if lean_obj_tag(v___x_1091_) == 0 {
                        v_a_1092_ = lean_ctor_get(v___x_1091_, 0);
                        lean_inc(v_a_1092_);
                        lean_dec_ref_known(v___x_1091_, 1);
                        v___x_1093_ = l_Lean_mkRecOnName(v_n_1050_);
                        v___x_1094_ = lean_box(1);
                        v___x_1095_ =
                            l_Lean_mkDefinitionValInferringUnsafe___at___00mkRecOn_spec__3___redArg(
                                v___x_1093_,
                                v_levelParams_1046_,
                                v_a_1090_,
                                v_a_1092_,
                                v___x_1094_,
                                v___y_1056_,
                            );
                        return v___x_1095_;
                    } else {
                        lean_dec(v_a_1090_);
                        lean_dec(v_n_1050_);
                        lean_dec(v_levelParams_1046_);
                        v_a_1096_ = lean_ctor_get(v___x_1091_, 0);
                        v_isSharedCheck_1103_ = (!lean_is_exclusive(v___x_1091_)) as u8;
                        if v_isSharedCheck_1103_ == 0 {
                            v___x_1098_ = v___x_1091_;
                            v_isShared_1099_ = v_isSharedCheck_1103_;
                            state = 1;
                            continue;
                        } else {
                            lean_inc(v_a_1096_);
                            lean_dec(v___x_1091_);
                            v___x_1098_ = lean_box(0);
                            v_isShared_1099_ = v_isSharedCheck_1103_;
                            state = 1;
                            continue;
                        }
                    }
                } else {
                    lean_dec_ref(v___x_1085_);
                    lean_dec_ref(v___x_1061_);
                    lean_dec(v_n_1050_);
                    lean_dec(v_levelParams_1046_);
                    v_a_1104_ = lean_ctor_get(v___x_1089_, 0);
                    v_isSharedCheck_1111_ = (!lean_is_exclusive(v___x_1089_)) as u8;
                    if v_isSharedCheck_1111_ == 0 {
                        v___x_1106_ = v___x_1089_;
                        v_isShared_1107_ = v_isSharedCheck_1111_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_1104_);
                        lean_dec(v___x_1089_);
                        v___x_1106_ = lean_box(0);
                        v_isShared_1107_ = v_isSharedCheck_1111_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_1099_ == 0 {
                    v___x_1101_ = v___x_1098_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1102_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1102_, 0, v_a_1096_);
                    v___x_1101_ = v_reuseFailAlloc_1102_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1101_;
            }
            3 => {
                if v_isShared_1107_ == 0 {
                    v___x_1109_ = v___x_1106_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1110_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1110_, 0, v_a_1104_);
                    v___x_1109_ = v_reuseFailAlloc_1110_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_1109_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_mkRecOn___lam__0___boxed(
    mut v_levelParams_1112_: *mut LeanObject,
    mut v_name_1113_: *mut LeanObject,
    mut v_numMinors_1114_: *mut LeanObject,
    mut v_numIndices_1115_: *mut LeanObject,
    mut v_n_1116_: *mut LeanObject,
    mut v_xs_1117_: *mut LeanObject,
    mut v_t_1118_: *mut LeanObject,
    mut v___y_1119_: *mut LeanObject,
    mut v___y_1120_: *mut LeanObject,
    mut v___y_1121_: *mut LeanObject,
    mut v___y_1122_: *mut LeanObject,
    mut v___y_1123_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1124_: *mut LeanObject = core::ptr::null_mut();
    v_res_1124_ = l_mkRecOn___lam__0(
        v_levelParams_1112_,
        v_name_1113_,
        v_numMinors_1114_,
        v_numIndices_1115_,
        v_n_1116_,
        v_xs_1117_,
        v_t_1118_,
        v___y_1119_,
        v___y_1120_,
        v___y_1121_,
        v___y_1122_,
    );
    lean_dec(v___y_1122_);
    lean_dec_ref(v___y_1121_);
    lean_dec(v___y_1120_);
    lean_dec_ref(v___y_1119_);
    lean_dec(v_numIndices_1115_);
    lean_dec(v_numMinors_1114_);
    return v_res_1124_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkRecOn_spec__0_spec__0_spec__3_spec__10_spec__11_spec__12___redArg___closed__0()
-> *mut LeanObject {
    let mut v___x_1125_: *mut LeanObject = core::ptr::null_mut();
    v___x_1125_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
    return v___x_1125_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkRecOn_spec__0_spec__0_spec__3_spec__10_spec__11_spec__12___redArg___closed__1()
-> *mut LeanObject {
    let mut v___x_1126_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1127_: *mut LeanObject = core::ptr::null_mut();
    v___x_1126_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkRecOn_spec__0_spec__0_spec__3_spec__10_spec__11_spec__12___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkRecOn_spec__0_spec__0_spec__3_spec__10_spec__11_spec__12___redArg___closed__0_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkRecOn_spec__0_spec__0_spec__3_spec__10_spec__11_spec__12___redArg___closed__0);
    v___x_1127_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_1127_, 0, v___x_1126_);
    return v___x_1127_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkRecOn_spec__0_spec__0_spec__3_spec__10_spec__11_spec__12___redArg___closed__2()
-> *mut LeanObject {
    let mut v___x_1128_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1129_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1130_: *mut LeanObject = core::ptr::null_mut();
    v___x_1128_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkRecOn_spec__0_spec__0_spec__3_spec__10_spec__11_spec__12___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkRecOn_spec__0_spec__0_spec__3_spec__10_spec__11_spec__12___redArg___closed__1_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkRecOn_spec__0_spec__0_spec__3_spec__10_spec__11_spec__12___redArg___closed__1);
    v___x_1129_ = lean_unsigned_to_nat(0);
    v___x_1130_ = lean_alloc_ctor(0, 10, (0) as u32);
    lean_ctor_set(v___x_1130_, 0, v___x_1129_);
    lean_ctor_set(v___x_1130_, 1, v___x_1129_);
    lean_ctor_set(v___x_1130_, 2, v___x_1129_);
    lean_ctor_set(v___x_1130_, 3, v___x_1129_);
    lean_ctor_set(v___x_1130_, 4, v___x_1128_);
    lean_ctor_set(v___x_1130_, 5, v___x_1128_);
    lean_ctor_set(v___x_1130_, 6, v___x_1128_);
    lean_ctor_set(v___x_1130_, 7, v___x_1128_);
    lean_ctor_set(v___x_1130_, 8, v___x_1128_);
    lean_ctor_set(v___x_1130_, 9, v___x_1128_);
    return v___x_1130_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkRecOn_spec__0_spec__0_spec__3_spec__10_spec__11_spec__12___redArg___closed__3()
-> *mut LeanObject {
    let mut v___x_1131_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1132_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1133_: *mut LeanObject = core::ptr::null_mut();
    v___x_1131_ = lean_unsigned_to_nat(32);
    v___x_1132_ = lean_mk_empty_array_with_capacity(v___x_1131_);
    v___x_1133_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_1133_, 0, v___x_1132_);
    return v___x_1133_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkRecOn_spec__0_spec__0_spec__3_spec__10_spec__11_spec__12___redArg___closed__4()
-> *mut LeanObject {
    let mut v___x_1134_: usize = 0;
    let mut v___x_1135_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1136_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1137_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1138_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1139_: *mut LeanObject = core::ptr::null_mut();
    v___x_1134_ = 5usize;
    v___x_1135_ = lean_unsigned_to_nat(0);
    v___x_1136_ = lean_unsigned_to_nat(32);
    v___x_1137_ = lean_mk_empty_array_with_capacity(v___x_1136_);
    v___x_1138_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkRecOn_spec__0_spec__0_spec__3_spec__10_spec__11_spec__12___redArg___closed__3), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkRecOn_spec__0_spec__0_spec__3_spec__10_spec__11_spec__12___redArg___closed__3_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkRecOn_spec__0_spec__0_spec__3_spec__10_spec__11_spec__12___redArg___closed__3);
    v___x_1139_ = lean_alloc_ctor(0, 4, (core::mem::size_of::<usize>() * 1) as u32);
    lean_ctor_set(v___x_1139_, 0, v___x_1138_);
    lean_ctor_set(v___x_1139_, 1, v___x_1137_);
    lean_ctor_set(v___x_1139_, 2, v___x_1135_);
    lean_ctor_set(v___x_1139_, 3, v___x_1135_);
    lean_ctor_set_usize(v___x_1139_, 4, v___x_1134_);
    return v___x_1139_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkRecOn_spec__0_spec__0_spec__3_spec__10_spec__11_spec__12___redArg___closed__5()
-> *mut LeanObject {
    let mut v___x_1140_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1141_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1142_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1143_: *mut LeanObject = core::ptr::null_mut();
    v___x_1140_ = lean_box(1);
    v___x_1141_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkRecOn_spec__0_spec__0_spec__3_spec__10_spec__11_spec__12___redArg___closed__4), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkRecOn_spec__0_spec__0_spec__3_spec__10_spec__11_spec__12___redArg___closed__4_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkRecOn_spec__0_spec__0_spec__3_spec__10_spec__11_spec__12___redArg___closed__4);
    v___x_1142_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkRecOn_spec__0_spec__0_spec__3_spec__10_spec__11_spec__12___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkRecOn_spec__0_spec__0_spec__3_spec__10_spec__11_spec__12___redArg___closed__1_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkRecOn_spec__0_spec__0_spec__3_spec__10_spec__11_spec__12___redArg___closed__1);
    v___x_1143_ = lean_alloc_ctor(0, 3, (0) as u32);
    lean_ctor_set(v___x_1143_, 0, v___x_1142_);
    lean_ctor_set(v___x_1143_, 1, v___x_1141_);
    lean_ctor_set(v___x_1143_, 2, v___x_1140_);
    return v___x_1143_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkRecOn_spec__0_spec__0_spec__3_spec__10_spec__11_spec__12___redArg___closed__7()
-> *mut LeanObject {
    let mut v___x_1145_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1146_: *mut LeanObject = core::ptr::null_mut();
    v___x_1145_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkRecOn_spec__0_spec__0_spec__3_spec__10_spec__11_spec__12___redArg___closed__6;
    v___x_1146_ = l_Lean_stringToMessageData(v___x_1145_);
    return v___x_1146_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkRecOn_spec__0_spec__0_spec__3_spec__10_spec__11_spec__12___redArg___closed__9()
-> *mut LeanObject {
    let mut v___x_1148_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1149_: *mut LeanObject = core::ptr::null_mut();
    v___x_1148_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkRecOn_spec__0_spec__0_spec__3_spec__10_spec__11_spec__12___redArg___closed__8;
    v___x_1149_ = l_Lean_stringToMessageData(v___x_1148_);
    return v___x_1149_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkRecOn_spec__0_spec__0_spec__3_spec__10_spec__11_spec__12___redArg___closed__11()
-> *mut LeanObject {
    let mut v___x_1151_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1152_: *mut LeanObject = core::ptr::null_mut();
    v___x_1151_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkRecOn_spec__0_spec__0_spec__3_spec__10_spec__11_spec__12___redArg___closed__10;
    v___x_1152_ = l_Lean_stringToMessageData(v___x_1151_);
    return v___x_1152_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkRecOn_spec__0_spec__0_spec__3_spec__10_spec__11_spec__12___redArg___closed__13()
-> *mut LeanObject {
    let mut v___x_1154_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1155_: *mut LeanObject = core::ptr::null_mut();
    v___x_1154_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkRecOn_spec__0_spec__0_spec__3_spec__10_spec__11_spec__12___redArg___closed__12;
    v___x_1155_ = l_Lean_stringToMessageData(v___x_1154_);
    return v___x_1155_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkRecOn_spec__0_spec__0_spec__3_spec__10_spec__11_spec__12___redArg___closed__15()
-> *mut LeanObject {
    let mut v___x_1157_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1158_: *mut LeanObject = core::ptr::null_mut();
    v___x_1157_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkRecOn_spec__0_spec__0_spec__3_spec__10_spec__11_spec__12___redArg___closed__14;
    v___x_1158_ = l_Lean_stringToMessageData(v___x_1157_);
    return v___x_1158_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkRecOn_spec__0_spec__0_spec__3_spec__10_spec__11_spec__12___redArg___closed__17()
-> *mut LeanObject {
    let mut v___x_1160_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1161_: *mut LeanObject = core::ptr::null_mut();
    v___x_1160_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkRecOn_spec__0_spec__0_spec__3_spec__10_spec__11_spec__12___redArg___closed__16;
    v___x_1161_ = l_Lean_stringToMessageData(v___x_1160_);
    return v___x_1161_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkRecOn_spec__0_spec__0_spec__3_spec__10_spec__11_spec__12___redArg___closed__19()
-> *mut LeanObject {
    let mut v___x_1163_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1164_: *mut LeanObject = core::ptr::null_mut();
    v___x_1163_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkRecOn_spec__0_spec__0_spec__3_spec__10_spec__11_spec__12___redArg___closed__18;
    v___x_1164_ = l_Lean_stringToMessageData(v___x_1163_);
    return v___x_1164_;
}
pub unsafe fn l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkRecOn_spec__0_spec__0_spec__3_spec__10_spec__11_spec__12___redArg(
    mut v_msg_1165_: *mut LeanObject,
    mut v_declHint_1166_: *mut LeanObject,
    mut v___y_1167_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1169_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_1170_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1171_: u8 = 0;
    let mut v_isExporting_1172_: u8 = 0;
    let mut v___x_1173_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1174_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1175_: u8 = 0;
    let mut v___x_1176_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1177_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1178_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1179_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1180_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1181_: *mut LeanObject = core::ptr::null_mut();
    let mut v_c_1182_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1183_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1184_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1185_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1186_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1187_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1188_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1189_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1190_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_1191_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1193_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1194_: u8 = 0;
    let mut v___x_1195_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1196_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1197_: *mut LeanObject = core::ptr::null_mut();
    let mut v_mod_1198_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1199_: u8 = 0;
    let mut v___x_1200_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1201_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1202_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1203_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1204_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1205_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1206_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1207_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1208_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1209_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1211_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1212_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1213_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1214_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1215_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1216_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1217_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1218_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1219_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1220_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1221_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1222_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1224_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1225_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1226_: u8 = 0;
    let mut v___x_1227_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1169_ = lean_st_ref_get(v___y_1167_);
                v_env_1170_ = lean_ctor_get(v___x_1169_, 0);
                lean_inc_ref(v_env_1170_);
                lean_dec(v___x_1169_);
                v___x_1171_ = l_Lean_Name_isAnonymous(v_declHint_1166_);
                if v___x_1171_ == 0 {
                    v_isExporting_1172_ = lean_ctor_get_uint8(
                        v_env_1170_,
                        (core::mem::size_of::<*mut LeanObject>() * 8) as u32,
                    );
                    if v_isExporting_1172_ == 0 {
                        lean_dec_ref(v_env_1170_);
                        lean_dec(v_declHint_1166_);
                        v___x_1173_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v___x_1173_, 0, v_msg_1165_);
                        return v___x_1173_;
                    } else {
                        lean_inc_ref(v_env_1170_);
                        v___x_1174_ = l_Lean_Environment_setExporting(v_env_1170_, v___x_1171_);
                        lean_inc(v_declHint_1166_);
                        lean_inc_ref(v___x_1174_);
                        v___x_1175_ = l_Lean_Environment_contains(
                            v___x_1174_,
                            v_declHint_1166_,
                            v_isExporting_1172_,
                        );
                        if v___x_1175_ == 0 {
                            lean_dec_ref(v___x_1174_);
                            lean_dec_ref(v_env_1170_);
                            lean_dec(v_declHint_1166_);
                            v___x_1176_ = lean_alloc_ctor(0, 1, (0) as u32);
                            lean_ctor_set(v___x_1176_, 0, v_msg_1165_);
                            return v___x_1176_;
                        } else {
                            v___x_1177_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkRecOn_spec__0_spec__0_spec__3_spec__10_spec__11_spec__12___redArg___closed__2), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkRecOn_spec__0_spec__0_spec__3_spec__10_spec__11_spec__12___redArg___closed__2_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkRecOn_spec__0_spec__0_spec__3_spec__10_spec__11_spec__12___redArg___closed__2);
                            v___x_1178_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkRecOn_spec__0_spec__0_spec__3_spec__10_spec__11_spec__12___redArg___closed__5), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkRecOn_spec__0_spec__0_spec__3_spec__10_spec__11_spec__12___redArg___closed__5_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkRecOn_spec__0_spec__0_spec__3_spec__10_spec__11_spec__12___redArg___closed__5);
                            v___x_1179_ = l_Lean_Options_empty;
                            v___x_1180_ = lean_alloc_ctor(0, 4, (0) as u32);
                            lean_ctor_set(v___x_1180_, 0, v___x_1174_);
                            lean_ctor_set(v___x_1180_, 1, v___x_1177_);
                            lean_ctor_set(v___x_1180_, 2, v___x_1178_);
                            lean_ctor_set(v___x_1180_, 3, v___x_1179_);
                            lean_inc(v_declHint_1166_);
                            v___x_1181_ =
                                l_Lean_MessageData_ofConstName(v_declHint_1166_, v___x_1171_);
                            v_c_1182_ = lean_alloc_ctor(3, 2, (0) as u32);
                            lean_ctor_set(v_c_1182_, 0, v___x_1180_);
                            lean_ctor_set(v_c_1182_, 1, v___x_1181_);
                            v___x_1183_ = l_Lean_Environment_getModuleIdxFor_x3f(
                                v_env_1170_,
                                v_declHint_1166_,
                            );
                            if lean_obj_tag(v___x_1183_) == 0 {
                                lean_dec_ref(v_env_1170_);
                                lean_dec(v_declHint_1166_);
                                v___x_1184_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkRecOn_spec__0_spec__0_spec__3_spec__10_spec__11_spec__12___redArg___closed__7), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkRecOn_spec__0_spec__0_spec__3_spec__10_spec__11_spec__12___redArg___closed__7_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkRecOn_spec__0_spec__0_spec__3_spec__10_spec__11_spec__12___redArg___closed__7);
                                v___x_1185_ = lean_alloc_ctor(7, 2, (0) as u32);
                                lean_ctor_set(v___x_1185_, 0, v___x_1184_);
                                lean_ctor_set(v___x_1185_, 1, v_c_1182_);
                                v___x_1186_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkRecOn_spec__0_spec__0_spec__3_spec__10_spec__11_spec__12___redArg___closed__9), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkRecOn_spec__0_spec__0_spec__3_spec__10_spec__11_spec__12___redArg___closed__9_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkRecOn_spec__0_spec__0_spec__3_spec__10_spec__11_spec__12___redArg___closed__9);
                                v___x_1187_ = lean_alloc_ctor(7, 2, (0) as u32);
                                lean_ctor_set(v___x_1187_, 0, v___x_1185_);
                                lean_ctor_set(v___x_1187_, 1, v___x_1186_);
                                v___x_1188_ = l_Lean_MessageData_note(v___x_1187_);
                                v___x_1189_ = lean_alloc_ctor(7, 2, (0) as u32);
                                lean_ctor_set(v___x_1189_, 0, v_msg_1165_);
                                lean_ctor_set(v___x_1189_, 1, v___x_1188_);
                                v___x_1190_ = lean_alloc_ctor(0, 1, (0) as u32);
                                lean_ctor_set(v___x_1190_, 0, v___x_1189_);
                                return v___x_1190_;
                            } else {
                                v_val_1191_ = lean_ctor_get(v___x_1183_, 0);
                                v_isSharedCheck_1226_ = (!lean_is_exclusive(v___x_1183_)) as u8;
                                if v_isSharedCheck_1226_ == 0 {
                                    v___x_1193_ = v___x_1183_;
                                    v_isShared_1194_ = v_isSharedCheck_1226_;
                                    state = 1;
                                    continue;
                                } else {
                                    lean_inc(v_val_1191_);
                                    lean_dec(v___x_1183_);
                                    v___x_1193_ = lean_box(0);
                                    v_isShared_1194_ = v_isSharedCheck_1226_;
                                    state = 1;
                                    continue;
                                }
                            }
                        }
                    }
                } else {
                    lean_dec_ref(v_env_1170_);
                    lean_dec(v_declHint_1166_);
                    v___x_1227_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_1227_, 0, v_msg_1165_);
                    return v___x_1227_;
                }
            }
            1 => {
                v___x_1195_ = lean_box(0);
                v___x_1196_ = l_Lean_Environment_header(v_env_1170_);
                lean_dec_ref(v_env_1170_);
                v___x_1197_ = l_Lean_EnvironmentHeader_moduleNames(v___x_1196_);
                v_mod_1198_ = lean_array_get(v___x_1195_, v___x_1197_, v_val_1191_);
                lean_dec(v_val_1191_);
                lean_dec_ref(v___x_1197_);
                v___x_1199_ = l_Lean_isPrivateName(v_declHint_1166_);
                lean_dec(v_declHint_1166_);
                if v___x_1199_ == 0 {
                    v___x_1200_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkRecOn_spec__0_spec__0_spec__3_spec__10_spec__11_spec__12___redArg___closed__11), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkRecOn_spec__0_spec__0_spec__3_spec__10_spec__11_spec__12___redArg___closed__11_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkRecOn_spec__0_spec__0_spec__3_spec__10_spec__11_spec__12___redArg___closed__11);
                    v___x_1201_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_1201_, 0, v___x_1200_);
                    lean_ctor_set(v___x_1201_, 1, v_c_1182_);
                    v___x_1202_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkRecOn_spec__0_spec__0_spec__3_spec__10_spec__11_spec__12___redArg___closed__13), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkRecOn_spec__0_spec__0_spec__3_spec__10_spec__11_spec__12___redArg___closed__13_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkRecOn_spec__0_spec__0_spec__3_spec__10_spec__11_spec__12___redArg___closed__13);
                    v___x_1203_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_1203_, 0, v___x_1201_);
                    lean_ctor_set(v___x_1203_, 1, v___x_1202_);
                    v___x_1204_ = l_Lean_MessageData_ofName(v_mod_1198_);
                    v___x_1205_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_1205_, 0, v___x_1203_);
                    lean_ctor_set(v___x_1205_, 1, v___x_1204_);
                    v___x_1206_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkRecOn_spec__0_spec__0_spec__3_spec__10_spec__11_spec__12___redArg___closed__15), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkRecOn_spec__0_spec__0_spec__3_spec__10_spec__11_spec__12___redArg___closed__15_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkRecOn_spec__0_spec__0_spec__3_spec__10_spec__11_spec__12___redArg___closed__15);
                    v___x_1207_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_1207_, 0, v___x_1205_);
                    lean_ctor_set(v___x_1207_, 1, v___x_1206_);
                    v___x_1208_ = l_Lean_MessageData_note(v___x_1207_);
                    v___x_1209_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_1209_, 0, v_msg_1165_);
                    lean_ctor_set(v___x_1209_, 1, v___x_1208_);
                    if v_isShared_1194_ == 0 {
                        lean_ctor_set_tag(v___x_1193_, 0);
                        lean_ctor_set(v___x_1193_, 0, v___x_1209_);
                        v___x_1211_ = v___x_1193_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_1212_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_1212_, 0, v___x_1209_);
                        v___x_1211_ = v_reuseFailAlloc_1212_;
                        state = 2;
                        continue;
                    }
                } else {
                    v___x_1213_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkRecOn_spec__0_spec__0_spec__3_spec__10_spec__11_spec__12___redArg___closed__7), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkRecOn_spec__0_spec__0_spec__3_spec__10_spec__11_spec__12___redArg___closed__7_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkRecOn_spec__0_spec__0_spec__3_spec__10_spec__11_spec__12___redArg___closed__7);
                    v___x_1214_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_1214_, 0, v___x_1213_);
                    lean_ctor_set(v___x_1214_, 1, v_c_1182_);
                    v___x_1215_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkRecOn_spec__0_spec__0_spec__3_spec__10_spec__11_spec__12___redArg___closed__17), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkRecOn_spec__0_spec__0_spec__3_spec__10_spec__11_spec__12___redArg___closed__17_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkRecOn_spec__0_spec__0_spec__3_spec__10_spec__11_spec__12___redArg___closed__17);
                    v___x_1216_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_1216_, 0, v___x_1214_);
                    lean_ctor_set(v___x_1216_, 1, v___x_1215_);
                    v___x_1217_ = l_Lean_MessageData_ofName(v_mod_1198_);
                    v___x_1218_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_1218_, 0, v___x_1216_);
                    lean_ctor_set(v___x_1218_, 1, v___x_1217_);
                    v___x_1219_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkRecOn_spec__0_spec__0_spec__3_spec__10_spec__11_spec__12___redArg___closed__19), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkRecOn_spec__0_spec__0_spec__3_spec__10_spec__11_spec__12___redArg___closed__19_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkRecOn_spec__0_spec__0_spec__3_spec__10_spec__11_spec__12___redArg___closed__19);
                    v___x_1220_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_1220_, 0, v___x_1218_);
                    lean_ctor_set(v___x_1220_, 1, v___x_1219_);
                    v___x_1221_ = l_Lean_MessageData_note(v___x_1220_);
                    v___x_1222_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_1222_, 0, v_msg_1165_);
                    lean_ctor_set(v___x_1222_, 1, v___x_1221_);
                    if v_isShared_1194_ == 0 {
                        lean_ctor_set_tag(v___x_1193_, 0);
                        lean_ctor_set(v___x_1193_, 0, v___x_1222_);
                        v___x_1224_ = v___x_1193_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_1225_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_1225_, 0, v___x_1222_);
                        v___x_1224_ = v_reuseFailAlloc_1225_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_1211_;
            }
            3 => {
                return v___x_1224_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkRecOn_spec__0_spec__0_spec__3_spec__10_spec__11_spec__12___redArg___boxed(
    mut v_msg_1228_: *mut LeanObject,
    mut v_declHint_1229_: *mut LeanObject,
    mut v___y_1230_: *mut LeanObject,
    mut v___y_1231_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1232_: *mut LeanObject = core::ptr::null_mut();
    v_res_1232_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkRecOn_spec__0_spec__0_spec__3_spec__10_spec__11_spec__12___redArg(v_msg_1228_, v_declHint_1229_, v___y_1230_);
    lean_dec(v___y_1230_);
    return v_res_1232_;
}
pub unsafe fn l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkRecOn_spec__0_spec__0_spec__3_spec__10_spec__11(
    mut v_msg_1233_: *mut LeanObject,
    mut v_declHint_1234_: *mut LeanObject,
    mut v___y_1235_: *mut LeanObject,
    mut v___y_1236_: *mut LeanObject,
    mut v___y_1237_: *mut LeanObject,
    mut v___y_1238_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1240_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1241_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1243_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1244_: u8 = 0;
    let mut v___x_1245_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1246_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1248_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1249_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1250_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1240_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkRecOn_spec__0_spec__0_spec__3_spec__10_spec__11_spec__12___redArg(v_msg_1233_, v_declHint_1234_, v___y_1238_);
                v_a_1241_ = lean_ctor_get(v___x_1240_, 0);
                v_isSharedCheck_1250_ = (!lean_is_exclusive(v___x_1240_)) as u8;
                if v_isSharedCheck_1250_ == 0 {
                    v___x_1243_ = v___x_1240_;
                    v_isShared_1244_ = v_isSharedCheck_1250_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_a_1241_);
                    lean_dec(v___x_1240_);
                    v___x_1243_ = lean_box(0);
                    v_isShared_1244_ = v_isSharedCheck_1250_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_1245_ = l_Lean_unknownIdentifierMessageTag;
                v___x_1246_ = lean_alloc_ctor(8, 2, (0) as u32);
                lean_ctor_set(v___x_1246_, 0, v___x_1245_);
                lean_ctor_set(v___x_1246_, 1, v_a_1241_);
                if v_isShared_1244_ == 0 {
                    lean_ctor_set(v___x_1243_, 0, v___x_1246_);
                    v___x_1248_ = v___x_1243_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1249_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1249_, 0, v___x_1246_);
                    v___x_1248_ = v_reuseFailAlloc_1249_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1248_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkRecOn_spec__0_spec__0_spec__3_spec__10_spec__11___boxed(
    mut v_msg_1251_: *mut LeanObject,
    mut v_declHint_1252_: *mut LeanObject,
    mut v___y_1253_: *mut LeanObject,
    mut v___y_1254_: *mut LeanObject,
    mut v___y_1255_: *mut LeanObject,
    mut v___y_1256_: *mut LeanObject,
    mut v___y_1257_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1258_: *mut LeanObject = core::ptr::null_mut();
    v_res_1258_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkRecOn_spec__0_spec__0_spec__3_spec__10_spec__11(v_msg_1251_, v_declHint_1252_, v___y_1253_, v___y_1254_, v___y_1255_, v___y_1256_);
    lean_dec(v___y_1256_);
    lean_dec_ref(v___y_1255_);
    lean_dec(v___y_1254_);
    lean_dec_ref(v___y_1253_);
    return v_res_1258_;
}
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_throwError___at___00mkRecOn_spec__6_spec__8(
    mut v_msgData_1259_: *mut LeanObject,
    mut v___y_1260_: *mut LeanObject,
    mut v___y_1261_: *mut LeanObject,
    mut v___y_1262_: *mut LeanObject,
    mut v___y_1263_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1265_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_1266_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1267_: *mut LeanObject = core::ptr::null_mut();
    let mut v_mctx_1268_: *mut LeanObject = core::ptr::null_mut();
    let mut v_lctx_1269_: *mut LeanObject = core::ptr::null_mut();
    let mut v_options_1270_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1271_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1272_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1273_: *mut LeanObject = core::ptr::null_mut();
    v___x_1265_ = lean_st_ref_get(v___y_1263_);
    v_env_1266_ = lean_ctor_get(v___x_1265_, 0);
    lean_inc_ref(v_env_1266_);
    lean_dec(v___x_1265_);
    v___x_1267_ = lean_st_ref_get(v___y_1261_);
    v_mctx_1268_ = lean_ctor_get(v___x_1267_, 0);
    lean_inc_ref(v_mctx_1268_);
    lean_dec(v___x_1267_);
    v_lctx_1269_ = lean_ctor_get(v___y_1260_, 2);
    v_options_1270_ = lean_ctor_get(v___y_1262_, 2);
    lean_inc_ref(v_options_1270_);
    lean_inc_ref(v_lctx_1269_);
    v___x_1271_ = lean_alloc_ctor(0, 4, (0) as u32);
    lean_ctor_set(v___x_1271_, 0, v_env_1266_);
    lean_ctor_set(v___x_1271_, 1, v_mctx_1268_);
    lean_ctor_set(v___x_1271_, 2, v_lctx_1269_);
    lean_ctor_set(v___x_1271_, 3, v_options_1270_);
    v___x_1272_ = lean_alloc_ctor(3, 2, (0) as u32);
    lean_ctor_set(v___x_1272_, 0, v___x_1271_);
    lean_ctor_set(v___x_1272_, 1, v_msgData_1259_);
    v___x_1273_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_1273_, 0, v___x_1272_);
    return v___x_1273_;
}
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_throwError___at___00mkRecOn_spec__6_spec__8___boxed(
    mut v_msgData_1274_: *mut LeanObject,
    mut v___y_1275_: *mut LeanObject,
    mut v___y_1276_: *mut LeanObject,
    mut v___y_1277_: *mut LeanObject,
    mut v___y_1278_: *mut LeanObject,
    mut v___y_1279_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1280_: *mut LeanObject = core::ptr::null_mut();
    v_res_1280_ =
        l_Lean_addMessageContextFull___at___00Lean_throwError___at___00mkRecOn_spec__6_spec__8(
            v_msgData_1274_,
            v___y_1275_,
            v___y_1276_,
            v___y_1277_,
            v___y_1278_,
        );
    lean_dec(v___y_1278_);
    lean_dec_ref(v___y_1277_);
    lean_dec(v___y_1276_);
    lean_dec_ref(v___y_1275_);
    return v_res_1280_;
}
pub unsafe fn l_Lean_throwError___at___00mkRecOn_spec__6___redArg(
    mut v_msg_1281_: *mut LeanObject,
    mut v___y_1282_: *mut LeanObject,
    mut v___y_1283_: *mut LeanObject,
    mut v___y_1284_: *mut LeanObject,
    mut v___y_1285_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_ref_1287_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1288_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1289_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1291_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1292_: u8 = 0;
    let mut v___x_1293_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1295_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1296_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1297_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ref_1287_ = lean_ctor_get(v___y_1284_, 5);
                v___x_1288_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00mkRecOn_spec__6_spec__8(v_msg_1281_, v___y_1282_, v___y_1283_, v___y_1284_, v___y_1285_);
                v_a_1289_ = lean_ctor_get(v___x_1288_, 0);
                v_isSharedCheck_1297_ = (!lean_is_exclusive(v___x_1288_)) as u8;
                if v_isSharedCheck_1297_ == 0 {
                    v___x_1291_ = v___x_1288_;
                    v_isShared_1292_ = v_isSharedCheck_1297_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_a_1289_);
                    lean_dec(v___x_1288_);
                    v___x_1291_ = lean_box(0);
                    v_isShared_1292_ = v_isSharedCheck_1297_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                lean_inc(v_ref_1287_);
                v___x_1293_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_1293_, 0, v_ref_1287_);
                lean_ctor_set(v___x_1293_, 1, v_a_1289_);
                if v_isShared_1292_ == 0 {
                    lean_ctor_set_tag(v___x_1291_, 1);
                    lean_ctor_set(v___x_1291_, 0, v___x_1293_);
                    v___x_1295_ = v___x_1291_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1296_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1296_, 0, v___x_1293_);
                    v___x_1295_ = v_reuseFailAlloc_1296_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1295_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_throwError___at___00mkRecOn_spec__6___redArg___boxed(
    mut v_msg_1298_: *mut LeanObject,
    mut v___y_1299_: *mut LeanObject,
    mut v___y_1300_: *mut LeanObject,
    mut v___y_1301_: *mut LeanObject,
    mut v___y_1302_: *mut LeanObject,
    mut v___y_1303_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1304_: *mut LeanObject = core::ptr::null_mut();
    v_res_1304_ = l_Lean_throwError___at___00mkRecOn_spec__6___redArg(
        v_msg_1298_,
        v___y_1299_,
        v___y_1300_,
        v___y_1301_,
        v___y_1302_,
    );
    lean_dec(v___y_1302_);
    lean_dec_ref(v___y_1301_);
    lean_dec(v___y_1300_);
    lean_dec_ref(v___y_1299_);
    return v_res_1304_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkRecOn_spec__0_spec__0_spec__3_spec__10_spec__12___redArg(
    mut v_ref_1305_: *mut LeanObject,
    mut v_msg_1306_: *mut LeanObject,
    mut v___y_1307_: *mut LeanObject,
    mut v___y_1308_: *mut LeanObject,
    mut v___y_1309_: *mut LeanObject,
    mut v___y_1310_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_fileName_1312_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fileMap_1313_: *mut LeanObject = core::ptr::null_mut();
    let mut v_options_1314_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currRecDepth_1315_: *mut LeanObject = core::ptr::null_mut();
    let mut v_maxRecDepth_1316_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ref_1317_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currNamespace_1318_: *mut LeanObject = core::ptr::null_mut();
    let mut v_openDecls_1319_: *mut LeanObject = core::ptr::null_mut();
    let mut v_initHeartbeats_1320_: *mut LeanObject = core::ptr::null_mut();
    let mut v_maxHeartbeats_1321_: *mut LeanObject = core::ptr::null_mut();
    let mut v_quotContext_1322_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currMacroScope_1323_: *mut LeanObject = core::ptr::null_mut();
    let mut v_diag_1324_: u8 = 0;
    let mut v_cancelTk_x3f_1325_: *mut LeanObject = core::ptr::null_mut();
    let mut v_suppressElabErrors_1326_: u8 = 0;
    let mut v_inheritedTraceOptions_1327_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ref_1328_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1329_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1330_: *mut LeanObject = core::ptr::null_mut();
    v_fileName_1312_ = lean_ctor_get(v___y_1309_, 0);
    v_fileMap_1313_ = lean_ctor_get(v___y_1309_, 1);
    v_options_1314_ = lean_ctor_get(v___y_1309_, 2);
    v_currRecDepth_1315_ = lean_ctor_get(v___y_1309_, 3);
    v_maxRecDepth_1316_ = lean_ctor_get(v___y_1309_, 4);
    v_ref_1317_ = lean_ctor_get(v___y_1309_, 5);
    v_currNamespace_1318_ = lean_ctor_get(v___y_1309_, 6);
    v_openDecls_1319_ = lean_ctor_get(v___y_1309_, 7);
    v_initHeartbeats_1320_ = lean_ctor_get(v___y_1309_, 8);
    v_maxHeartbeats_1321_ = lean_ctor_get(v___y_1309_, 9);
    v_quotContext_1322_ = lean_ctor_get(v___y_1309_, 10);
    v_currMacroScope_1323_ = lean_ctor_get(v___y_1309_, 11);
    v_diag_1324_ = lean_ctor_get_uint8(
        v___y_1309_,
        (core::mem::size_of::<*mut LeanObject>() * 14) as u32,
    );
    v_cancelTk_x3f_1325_ = lean_ctor_get(v___y_1309_, 12);
    v_suppressElabErrors_1326_ = lean_ctor_get_uint8(
        v___y_1309_,
        (core::mem::size_of::<*mut LeanObject>() * 14 + 1) as u32,
    );
    v_inheritedTraceOptions_1327_ = lean_ctor_get(v___y_1309_, 13);
    v_ref_1328_ = l_Lean_replaceRef(v_ref_1305_, v_ref_1317_);
    lean_inc_ref(v_inheritedTraceOptions_1327_);
    lean_inc(v_cancelTk_x3f_1325_);
    lean_inc(v_currMacroScope_1323_);
    lean_inc(v_quotContext_1322_);
    lean_inc(v_maxHeartbeats_1321_);
    lean_inc(v_initHeartbeats_1320_);
    lean_inc(v_openDecls_1319_);
    lean_inc(v_currNamespace_1318_);
    lean_inc(v_maxRecDepth_1316_);
    lean_inc(v_currRecDepth_1315_);
    lean_inc_ref(v_options_1314_);
    lean_inc_ref(v_fileMap_1313_);
    lean_inc_ref(v_fileName_1312_);
    v___x_1329_ = lean_alloc_ctor(0, 14, (2) as u32);
    lean_ctor_set(v___x_1329_, 0, v_fileName_1312_);
    lean_ctor_set(v___x_1329_, 1, v_fileMap_1313_);
    lean_ctor_set(v___x_1329_, 2, v_options_1314_);
    lean_ctor_set(v___x_1329_, 3, v_currRecDepth_1315_);
    lean_ctor_set(v___x_1329_, 4, v_maxRecDepth_1316_);
    lean_ctor_set(v___x_1329_, 5, v_ref_1328_);
    lean_ctor_set(v___x_1329_, 6, v_currNamespace_1318_);
    lean_ctor_set(v___x_1329_, 7, v_openDecls_1319_);
    lean_ctor_set(v___x_1329_, 8, v_initHeartbeats_1320_);
    lean_ctor_set(v___x_1329_, 9, v_maxHeartbeats_1321_);
    lean_ctor_set(v___x_1329_, 10, v_quotContext_1322_);
    lean_ctor_set(v___x_1329_, 11, v_currMacroScope_1323_);
    lean_ctor_set(v___x_1329_, 12, v_cancelTk_x3f_1325_);
    lean_ctor_set(v___x_1329_, 13, v_inheritedTraceOptions_1327_);
    lean_ctor_set_uint8(
        v___x_1329_,
        (core::mem::size_of::<*mut LeanObject>() * 14) as u32,
        v_diag_1324_,
    );
    lean_ctor_set_uint8(
        v___x_1329_,
        (core::mem::size_of::<*mut LeanObject>() * 14 + 1) as u32,
        v_suppressElabErrors_1326_,
    );
    v___x_1330_ = l_Lean_throwError___at___00mkRecOn_spec__6___redArg(
        v_msg_1306_,
        v___y_1307_,
        v___y_1308_,
        v___x_1329_,
        v___y_1310_,
    );
    lean_dec_ref_known(v___x_1329_, 14);
    return v___x_1330_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkRecOn_spec__0_spec__0_spec__3_spec__10_spec__12___redArg___boxed(
    mut v_ref_1331_: *mut LeanObject,
    mut v_msg_1332_: *mut LeanObject,
    mut v___y_1333_: *mut LeanObject,
    mut v___y_1334_: *mut LeanObject,
    mut v___y_1335_: *mut LeanObject,
    mut v___y_1336_: *mut LeanObject,
    mut v___y_1337_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1338_: *mut LeanObject = core::ptr::null_mut();
    v_res_1338_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkRecOn_spec__0_spec__0_spec__3_spec__10_spec__12___redArg(v_ref_1331_, v_msg_1332_, v___y_1333_, v___y_1334_, v___y_1335_, v___y_1336_);
    lean_dec(v___y_1336_);
    lean_dec_ref(v___y_1335_);
    lean_dec(v___y_1334_);
    lean_dec_ref(v___y_1333_);
    lean_dec(v_ref_1331_);
    return v_res_1338_;
}
pub unsafe fn l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkRecOn_spec__0_spec__0_spec__3_spec__10___redArg(
    mut v_ref_1339_: *mut LeanObject,
    mut v_msg_1340_: *mut LeanObject,
    mut v_declHint_1341_: *mut LeanObject,
    mut v___y_1342_: *mut LeanObject,
    mut v___y_1343_: *mut LeanObject,
    mut v___y_1344_: *mut LeanObject,
    mut v___y_1345_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1347_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1348_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1349_: *mut LeanObject = core::ptr::null_mut();
    v___x_1347_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkRecOn_spec__0_spec__0_spec__3_spec__10_spec__11(v_msg_1340_, v_declHint_1341_, v___y_1342_, v___y_1343_, v___y_1344_, v___y_1345_);
    v_a_1348_ = lean_ctor_get(v___x_1347_, 0);
    lean_inc(v_a_1348_);
    lean_dec_ref(v___x_1347_);
    v___x_1349_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkRecOn_spec__0_spec__0_spec__3_spec__10_spec__12___redArg(v_ref_1339_, v_a_1348_, v___y_1342_, v___y_1343_, v___y_1344_, v___y_1345_);
    return v___x_1349_;
}
pub unsafe fn l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkRecOn_spec__0_spec__0_spec__3_spec__10___redArg___boxed(
    mut v_ref_1350_: *mut LeanObject,
    mut v_msg_1351_: *mut LeanObject,
    mut v_declHint_1352_: *mut LeanObject,
    mut v___y_1353_: *mut LeanObject,
    mut v___y_1354_: *mut LeanObject,
    mut v___y_1355_: *mut LeanObject,
    mut v___y_1356_: *mut LeanObject,
    mut v___y_1357_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1358_: *mut LeanObject = core::ptr::null_mut();
    v_res_1358_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkRecOn_spec__0_spec__0_spec__3_spec__10___redArg(v_ref_1350_, v_msg_1351_, v_declHint_1352_, v___y_1353_, v___y_1354_, v___y_1355_, v___y_1356_);
    lean_dec(v___y_1356_);
    lean_dec_ref(v___y_1355_);
    lean_dec(v___y_1354_);
    lean_dec_ref(v___y_1353_);
    lean_dec(v_ref_1350_);
    return v_res_1358_;
}
pub unsafe fn _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkRecOn_spec__0_spec__0_spec__3___redArg___closed__1()
-> *mut LeanObject {
    let mut v___x_1360_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1361_: *mut LeanObject = core::ptr::null_mut();
    v___x_1360_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkRecOn_spec__0_spec__0_spec__3___redArg___closed__0;
    v___x_1361_ = l_Lean_stringToMessageData(v___x_1360_);
    return v___x_1361_;
}
pub unsafe fn _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkRecOn_spec__0_spec__0_spec__3___redArg___closed__3()
-> *mut LeanObject {
    let mut v___x_1363_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1364_: *mut LeanObject = core::ptr::null_mut();
    v___x_1363_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkRecOn_spec__0_spec__0_spec__3___redArg___closed__2;
    v___x_1364_ = l_Lean_stringToMessageData(v___x_1363_);
    return v___x_1364_;
}
pub unsafe fn l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkRecOn_spec__0_spec__0_spec__3___redArg(
    mut v_ref_1365_: *mut LeanObject,
    mut v_constName_1366_: *mut LeanObject,
    mut v___y_1367_: *mut LeanObject,
    mut v___y_1368_: *mut LeanObject,
    mut v___y_1369_: *mut LeanObject,
    mut v___y_1370_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1372_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1373_: u8 = 0;
    let mut v___x_1374_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1375_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1376_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1377_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1378_: *mut LeanObject = core::ptr::null_mut();
    v___x_1372_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkRecOn_spec__0_spec__0_spec__3___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkRecOn_spec__0_spec__0_spec__3___redArg___closed__1_once), _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkRecOn_spec__0_spec__0_spec__3___redArg___closed__1);
    v___x_1373_ = 0;
    lean_inc(v_constName_1366_);
    v___x_1374_ = l_Lean_MessageData_ofConstName(v_constName_1366_, v___x_1373_);
    v___x_1375_ = lean_alloc_ctor(7, 2, (0) as u32);
    lean_ctor_set(v___x_1375_, 0, v___x_1372_);
    lean_ctor_set(v___x_1375_, 1, v___x_1374_);
    v___x_1376_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkRecOn_spec__0_spec__0_spec__3___redArg___closed__3), core::ptr::addr_of_mut!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkRecOn_spec__0_spec__0_spec__3___redArg___closed__3_once), _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkRecOn_spec__0_spec__0_spec__3___redArg___closed__3);
    v___x_1377_ = lean_alloc_ctor(7, 2, (0) as u32);
    lean_ctor_set(v___x_1377_, 0, v___x_1375_);
    lean_ctor_set(v___x_1377_, 1, v___x_1376_);
    v___x_1378_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkRecOn_spec__0_spec__0_spec__3_spec__10___redArg(v_ref_1365_, v___x_1377_, v_constName_1366_, v___y_1367_, v___y_1368_, v___y_1369_, v___y_1370_);
    return v___x_1378_;
}
pub unsafe fn l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkRecOn_spec__0_spec__0_spec__3___redArg___boxed(
    mut v_ref_1379_: *mut LeanObject,
    mut v_constName_1380_: *mut LeanObject,
    mut v___y_1381_: *mut LeanObject,
    mut v___y_1382_: *mut LeanObject,
    mut v___y_1383_: *mut LeanObject,
    mut v___y_1384_: *mut LeanObject,
    mut v___y_1385_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1386_: *mut LeanObject = core::ptr::null_mut();
    v_res_1386_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkRecOn_spec__0_spec__0_spec__3___redArg(v_ref_1379_, v_constName_1380_, v___y_1381_, v___y_1382_, v___y_1383_, v___y_1384_);
    lean_dec(v___y_1384_);
    lean_dec_ref(v___y_1383_);
    lean_dec(v___y_1382_);
    lean_dec_ref(v___y_1381_);
    lean_dec(v_ref_1379_);
    return v_res_1386_;
}
pub unsafe fn l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkRecOn_spec__0_spec__0___redArg(
    mut v_constName_1387_: *mut LeanObject,
    mut v___y_1388_: *mut LeanObject,
    mut v___y_1389_: *mut LeanObject,
    mut v___y_1390_: *mut LeanObject,
    mut v___y_1391_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_ref_1393_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1394_: *mut LeanObject = core::ptr::null_mut();
    v_ref_1393_ = lean_ctor_get(v___y_1390_, 5);
    v___x_1394_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkRecOn_spec__0_spec__0_spec__3___redArg(v_ref_1393_, v_constName_1387_, v___y_1388_, v___y_1389_, v___y_1390_, v___y_1391_);
    return v___x_1394_;
}
pub unsafe fn l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkRecOn_spec__0_spec__0___redArg___boxed(
    mut v_constName_1395_: *mut LeanObject,
    mut v___y_1396_: *mut LeanObject,
    mut v___y_1397_: *mut LeanObject,
    mut v___y_1398_: *mut LeanObject,
    mut v___y_1399_: *mut LeanObject,
    mut v___y_1400_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1401_: *mut LeanObject = core::ptr::null_mut();
    v_res_1401_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkRecOn_spec__0_spec__0___redArg(v_constName_1395_, v___y_1396_, v___y_1397_, v___y_1398_, v___y_1399_);
    lean_dec(v___y_1399_);
    lean_dec_ref(v___y_1398_);
    lean_dec(v___y_1397_);
    lean_dec_ref(v___y_1396_);
    return v_res_1401_;
}
pub unsafe fn l_Lean_getConstInfo___at___00mkRecOn_spec__0(
    mut v_constName_1402_: *mut LeanObject,
    mut v___y_1403_: *mut LeanObject,
    mut v___y_1404_: *mut LeanObject,
    mut v___y_1405_: *mut LeanObject,
    mut v___y_1406_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1408_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_1409_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1410_: u8 = 0;
    let mut v___x_1411_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1412_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_1413_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1415_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1416_: u8 = 0;
    let mut v___x_1418_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1419_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1420_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1408_ = lean_st_ref_get(v___y_1406_);
                v_env_1409_ = lean_ctor_get(v___x_1408_, 0);
                lean_inc_ref(v_env_1409_);
                lean_dec(v___x_1408_);
                v___x_1410_ = 0;
                lean_inc(v_constName_1402_);
                v___x_1411_ =
                    l_Lean_Environment_find_x3f(v_env_1409_, v_constName_1402_, v___x_1410_);
                if lean_obj_tag(v___x_1411_) == 0 {
                    v___x_1412_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkRecOn_spec__0_spec__0___redArg(v_constName_1402_, v___y_1403_, v___y_1404_, v___y_1405_, v___y_1406_);
                    return v___x_1412_;
                } else {
                    lean_dec(v_constName_1402_);
                    v_val_1413_ = lean_ctor_get(v___x_1411_, 0);
                    v_isSharedCheck_1420_ = (!lean_is_exclusive(v___x_1411_)) as u8;
                    if v_isSharedCheck_1420_ == 0 {
                        v___x_1415_ = v___x_1411_;
                        v_isShared_1416_ = v_isSharedCheck_1420_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_val_1413_);
                        lean_dec(v___x_1411_);
                        v___x_1415_ = lean_box(0);
                        v_isShared_1416_ = v_isSharedCheck_1420_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_1416_ == 0 {
                    lean_ctor_set_tag(v___x_1415_, 0);
                    v___x_1418_ = v___x_1415_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1419_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1419_, 0, v_val_1413_);
                    v___x_1418_ = v_reuseFailAlloc_1419_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1418_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_getConstInfo___at___00mkRecOn_spec__0___boxed(
    mut v_constName_1421_: *mut LeanObject,
    mut v___y_1422_: *mut LeanObject,
    mut v___y_1423_: *mut LeanObject,
    mut v___y_1424_: *mut LeanObject,
    mut v___y_1425_: *mut LeanObject,
    mut v___y_1426_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1427_: *mut LeanObject = core::ptr::null_mut();
    v_res_1427_ = l_Lean_getConstInfo___at___00mkRecOn_spec__0(
        v_constName_1421_,
        v___y_1422_,
        v___y_1423_,
        v___y_1424_,
        v___y_1425_,
    );
    lean_dec(v___y_1425_);
    lean_dec_ref(v___y_1424_);
    lean_dec(v___y_1423_);
    lean_dec_ref(v___y_1422_);
    return v_res_1427_;
}
pub unsafe fn _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00mkRecOn_spec__5_spec__6___redArg___closed__0()
-> *mut LeanObject {
    let mut v___x_1428_: *mut LeanObject = core::ptr::null_mut();
    v___x_1428_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
    return v___x_1428_;
}
pub unsafe fn _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00mkRecOn_spec__5_spec__6___redArg___closed__1()
-> *mut LeanObject {
    let mut v___x_1429_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1430_: *mut LeanObject = core::ptr::null_mut();
    v___x_1429_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00mkRecOn_spec__5_spec__6___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00mkRecOn_spec__5_spec__6___redArg___closed__0_once), _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00mkRecOn_spec__5_spec__6___redArg___closed__0);
    v___x_1430_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_1430_, 0, v___x_1429_);
    return v___x_1430_;
}
pub unsafe fn _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00mkRecOn_spec__5_spec__6___redArg___closed__2()
-> *mut LeanObject {
    let mut v___x_1431_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1432_: *mut LeanObject = core::ptr::null_mut();
    v___x_1431_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00mkRecOn_spec__5_spec__6___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00mkRecOn_spec__5_spec__6___redArg___closed__1_once), _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00mkRecOn_spec__5_spec__6___redArg___closed__1);
    v___x_1432_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_1432_, 0, v___x_1431_);
    lean_ctor_set(v___x_1432_, 1, v___x_1431_);
    return v___x_1432_;
}
pub unsafe fn _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00mkRecOn_spec__5_spec__6___redArg___closed__3()
-> *mut LeanObject {
    let mut v___x_1433_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1434_: *mut LeanObject = core::ptr::null_mut();
    v___x_1433_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00mkRecOn_spec__5_spec__6___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00mkRecOn_spec__5_spec__6___redArg___closed__1_once), _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00mkRecOn_spec__5_spec__6___redArg___closed__1);
    v___x_1434_ = lean_alloc_ctor(0, 6, (0) as u32);
    lean_ctor_set(v___x_1434_, 0, v___x_1433_);
    lean_ctor_set(v___x_1434_, 1, v___x_1433_);
    lean_ctor_set(v___x_1434_, 2, v___x_1433_);
    lean_ctor_set(v___x_1434_, 3, v___x_1433_);
    lean_ctor_set(v___x_1434_, 4, v___x_1433_);
    lean_ctor_set(v___x_1434_, 5, v___x_1433_);
    return v___x_1434_;
}
pub unsafe fn l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00mkRecOn_spec__5_spec__6___redArg(
    mut v_declName_1435_: *mut LeanObject,
    mut v_s_1436_: u8,
    mut v___y_1437_: *mut LeanObject,
    mut v___y_1438_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1440_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_1441_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_1442_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ngen_1443_: *mut LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_1444_: *mut LeanObject = core::ptr::null_mut();
    let mut v_traceState_1445_: *mut LeanObject = core::ptr::null_mut();
    let mut v_messages_1446_: *mut LeanObject = core::ptr::null_mut();
    let mut v_infoState_1447_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_1448_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1450_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1451_: u8 = 0;
    let mut v___x_1452_: u8 = 0;
    let mut v___x_1453_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1454_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1455_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1457_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1458_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1459_: *mut LeanObject = core::ptr::null_mut();
    let mut v_mctx_1460_: *mut LeanObject = core::ptr::null_mut();
    let mut v_zetaDeltaFVarIds_1461_: *mut LeanObject = core::ptr::null_mut();
    let mut v_postponed_1462_: *mut LeanObject = core::ptr::null_mut();
    let mut v_diag_1463_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1465_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1466_: u8 = 0;
    let mut v___x_1467_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1469_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1470_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1471_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1472_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1473_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1474_: u8 = 0;
    let mut v_unused_1475_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1476_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1477_: u8 = 0;
    let mut v_unused_1478_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1440_ = lean_st_ref_take(v___y_1438_);
                v_env_1441_ = lean_ctor_get(v___x_1440_, 0);
                v_nextMacroScope_1442_ = lean_ctor_get(v___x_1440_, 1);
                v_ngen_1443_ = lean_ctor_get(v___x_1440_, 2);
                v_auxDeclNGen_1444_ = lean_ctor_get(v___x_1440_, 3);
                v_traceState_1445_ = lean_ctor_get(v___x_1440_, 4);
                v_messages_1446_ = lean_ctor_get(v___x_1440_, 6);
                v_infoState_1447_ = lean_ctor_get(v___x_1440_, 7);
                v_snapshotTasks_1448_ = lean_ctor_get(v___x_1440_, 8);
                v_isSharedCheck_1477_ = (!lean_is_exclusive(v___x_1440_)) as u8;
                if v_isSharedCheck_1477_ == 0 {
                    v_unused_1478_ = lean_ctor_get(v___x_1440_, 5);
                    lean_dec(v_unused_1478_);
                    v___x_1450_ = v___x_1440_;
                    v_isShared_1451_ = v_isSharedCheck_1477_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_snapshotTasks_1448_);
                    lean_inc(v_infoState_1447_);
                    lean_inc(v_messages_1446_);
                    lean_inc(v_traceState_1445_);
                    lean_inc(v_auxDeclNGen_1444_);
                    lean_inc(v_ngen_1443_);
                    lean_inc(v_nextMacroScope_1442_);
                    lean_inc(v_env_1441_);
                    lean_dec(v___x_1440_);
                    v___x_1450_ = lean_box(0);
                    v_isShared_1451_ = v_isSharedCheck_1477_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_1452_ = 0;
                v___x_1453_ = lean_box(0);
                v___x_1454_ = l___private_Lean_ReducibilityAttrs_0__Lean_setReducibilityStatusCore(
                    v_env_1441_,
                    v_declName_1435_,
                    v_s_1436_,
                    v___x_1452_,
                    v___x_1453_,
                );
                v___x_1455_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00mkRecOn_spec__5_spec__6___redArg___closed__2), core::ptr::addr_of_mut!(l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00mkRecOn_spec__5_spec__6___redArg___closed__2_once), _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00mkRecOn_spec__5_spec__6___redArg___closed__2);
                if v_isShared_1451_ == 0 {
                    lean_ctor_set(v___x_1450_, 5, v___x_1455_);
                    lean_ctor_set(v___x_1450_, 0, v___x_1454_);
                    v___x_1457_ = v___x_1450_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1476_ = lean_alloc_ctor(0, 9, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1476_, 0, v___x_1454_);
                    lean_ctor_set(v_reuseFailAlloc_1476_, 1, v_nextMacroScope_1442_);
                    lean_ctor_set(v_reuseFailAlloc_1476_, 2, v_ngen_1443_);
                    lean_ctor_set(v_reuseFailAlloc_1476_, 3, v_auxDeclNGen_1444_);
                    lean_ctor_set(v_reuseFailAlloc_1476_, 4, v_traceState_1445_);
                    lean_ctor_set(v_reuseFailAlloc_1476_, 5, v___x_1455_);
                    lean_ctor_set(v_reuseFailAlloc_1476_, 6, v_messages_1446_);
                    lean_ctor_set(v_reuseFailAlloc_1476_, 7, v_infoState_1447_);
                    lean_ctor_set(v_reuseFailAlloc_1476_, 8, v_snapshotTasks_1448_);
                    v___x_1457_ = v_reuseFailAlloc_1476_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1458_ = lean_st_ref_set(v___y_1438_, v___x_1457_);
                v___x_1459_ = lean_st_ref_take(v___y_1437_);
                v_mctx_1460_ = lean_ctor_get(v___x_1459_, 0);
                v_zetaDeltaFVarIds_1461_ = lean_ctor_get(v___x_1459_, 2);
                v_postponed_1462_ = lean_ctor_get(v___x_1459_, 3);
                v_diag_1463_ = lean_ctor_get(v___x_1459_, 4);
                v_isSharedCheck_1474_ = (!lean_is_exclusive(v___x_1459_)) as u8;
                if v_isSharedCheck_1474_ == 0 {
                    v_unused_1475_ = lean_ctor_get(v___x_1459_, 1);
                    lean_dec(v_unused_1475_);
                    v___x_1465_ = v___x_1459_;
                    v_isShared_1466_ = v_isSharedCheck_1474_;
                    state = 3;
                    continue;
                } else {
                    lean_inc(v_diag_1463_);
                    lean_inc(v_postponed_1462_);
                    lean_inc(v_zetaDeltaFVarIds_1461_);
                    lean_inc(v_mctx_1460_);
                    lean_dec(v___x_1459_);
                    v___x_1465_ = lean_box(0);
                    v_isShared_1466_ = v_isSharedCheck_1474_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_1467_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00mkRecOn_spec__5_spec__6___redArg___closed__3), core::ptr::addr_of_mut!(l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00mkRecOn_spec__5_spec__6___redArg___closed__3_once), _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00mkRecOn_spec__5_spec__6___redArg___closed__3);
                if v_isShared_1466_ == 0 {
                    lean_ctor_set(v___x_1465_, 1, v___x_1467_);
                    v___x_1469_ = v___x_1465_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1473_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1473_, 0, v_mctx_1460_);
                    lean_ctor_set(v_reuseFailAlloc_1473_, 1, v___x_1467_);
                    lean_ctor_set(v_reuseFailAlloc_1473_, 2, v_zetaDeltaFVarIds_1461_);
                    lean_ctor_set(v_reuseFailAlloc_1473_, 3, v_postponed_1462_);
                    lean_ctor_set(v_reuseFailAlloc_1473_, 4, v_diag_1463_);
                    v___x_1469_ = v_reuseFailAlloc_1473_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_1470_ = lean_st_ref_set(v___y_1437_, v___x_1469_);
                v___x_1471_ = lean_box(0);
                v___x_1472_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_1472_, 0, v___x_1471_);
                return v___x_1472_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00mkRecOn_spec__5_spec__6___redArg___boxed(
    mut v_declName_1479_: *mut LeanObject,
    mut v_s_1480_: *mut LeanObject,
    mut v___y_1481_: *mut LeanObject,
    mut v___y_1482_: *mut LeanObject,
    mut v___y_1483_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_s_boxed_1484_: u8 = 0;
    let mut v_res_1485_: *mut LeanObject = core::ptr::null_mut();
    v_s_boxed_1484_ = (lean_unbox(v_s_1480_) as u8);
    v_res_1485_ = l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00mkRecOn_spec__5_spec__6___redArg(v_declName_1479_, v_s_boxed_1484_, v___y_1481_, v___y_1482_);
    lean_dec(v___y_1482_);
    lean_dec(v___y_1481_);
    return v_res_1485_;
}
pub unsafe fn l_Lean_setReducibleAttribute___at___00mkRecOn_spec__5(
    mut v_declName_1486_: *mut LeanObject,
    mut v___y_1487_: *mut LeanObject,
    mut v___y_1488_: *mut LeanObject,
    mut v___y_1489_: *mut LeanObject,
    mut v___y_1490_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1492_: u8 = 0;
    let mut v___x_1493_: *mut LeanObject = core::ptr::null_mut();
    v___x_1492_ = 0;
    v___x_1493_ = l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00mkRecOn_spec__5_spec__6___redArg(v_declName_1486_, v___x_1492_, v___y_1488_, v___y_1490_);
    return v___x_1493_;
}
pub unsafe fn l_Lean_setReducibleAttribute___at___00mkRecOn_spec__5___boxed(
    mut v_declName_1494_: *mut LeanObject,
    mut v___y_1495_: *mut LeanObject,
    mut v___y_1496_: *mut LeanObject,
    mut v___y_1497_: *mut LeanObject,
    mut v___y_1498_: *mut LeanObject,
    mut v___y_1499_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1500_: *mut LeanObject = core::ptr::null_mut();
    v_res_1500_ = l_Lean_setReducibleAttribute___at___00mkRecOn_spec__5(
        v_declName_1494_,
        v___y_1495_,
        v___y_1496_,
        v___y_1497_,
        v___y_1498_,
    );
    lean_dec(v___y_1498_);
    lean_dec_ref(v___y_1497_);
    lean_dec(v___y_1496_);
    lean_dec_ref(v___y_1495_);
    return v_res_1500_;
}
pub unsafe fn _init_l_mkRecOn___closed__1() -> *mut LeanObject {
    let mut v___x_1502_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1503_: *mut LeanObject = core::ptr::null_mut();
    v___x_1502_ = l_mkRecOn___closed__0;
    v___x_1503_ = l_Lean_stringToMessageData(v___x_1502_);
    return v___x_1503_;
}
pub unsafe fn l_mkRecOn(
    mut v_n_1504_: *mut LeanObject,
    mut v_a_1505_: *mut LeanObject,
    mut v_a_1506_: *mut LeanObject,
    mut v_a_1507_: *mut LeanObject,
    mut v_a_1508_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1510_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1511_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1512_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_1513_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1515_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1516_: u8 = 0;
    let mut v_toConstantVal_1517_: *mut LeanObject = core::ptr::null_mut();
    let mut v_numIndices_1518_: *mut LeanObject = core::ptr::null_mut();
    let mut v_numMinors_1519_: *mut LeanObject = core::ptr::null_mut();
    let mut v_name_1520_: *mut LeanObject = core::ptr::null_mut();
    let mut v_levelParams_1521_: *mut LeanObject = core::ptr::null_mut();
    let mut v_type_1522_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1523_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1524_: u8 = 0;
    let mut v___x_1525_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1526_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1528_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1529_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toConstantVal_1530_: *mut LeanObject = core::ptr::null_mut();
    let mut v_name_1531_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1532_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1534_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1535_: u8 = 0;
    let mut v___x_1536_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_1537_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_1538_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ngen_1539_: *mut LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_1540_: *mut LeanObject = core::ptr::null_mut();
    let mut v_traceState_1541_: *mut LeanObject = core::ptr::null_mut();
    let mut v_messages_1542_: *mut LeanObject = core::ptr::null_mut();
    let mut v_infoState_1543_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_1544_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1546_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1547_: u8 = 0;
    let mut v___x_1548_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1549_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1551_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1552_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1553_: *mut LeanObject = core::ptr::null_mut();
    let mut v_mctx_1554_: *mut LeanObject = core::ptr::null_mut();
    let mut v_zetaDeltaFVarIds_1555_: *mut LeanObject = core::ptr::null_mut();
    let mut v_postponed_1556_: *mut LeanObject = core::ptr::null_mut();
    let mut v_diag_1557_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1559_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1560_: u8 = 0;
    let mut v___x_1561_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1563_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1564_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1565_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_1566_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_1567_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ngen_1568_: *mut LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_1569_: *mut LeanObject = core::ptr::null_mut();
    let mut v_traceState_1570_: *mut LeanObject = core::ptr::null_mut();
    let mut v_messages_1571_: *mut LeanObject = core::ptr::null_mut();
    let mut v_infoState_1572_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_1573_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1575_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1576_: u8 = 0;
    let mut v___x_1577_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1579_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1580_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1581_: *mut LeanObject = core::ptr::null_mut();
    let mut v_mctx_1582_: *mut LeanObject = core::ptr::null_mut();
    let mut v_zetaDeltaFVarIds_1583_: *mut LeanObject = core::ptr::null_mut();
    let mut v_postponed_1584_: *mut LeanObject = core::ptr::null_mut();
    let mut v_diag_1585_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1587_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1588_: u8 = 0;
    let mut v___x_1590_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1591_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1592_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1594_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1595_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1596_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1597_: u8 = 0;
    let mut v_unused_1598_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1599_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1600_: u8 = 0;
    let mut v_unused_1601_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1602_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1603_: u8 = 0;
    let mut v_unused_1604_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1605_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1606_: u8 = 0;
    let mut v_unused_1607_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1608_: u8 = 0;
    let mut v_unused_1609_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1610_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1611_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1613_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1614_: u8 = 0;
    let mut v___x_1616_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1617_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1618_: u8 = 0;
    let mut v_isSharedCheck_1619_: u8 = 0;
    let mut v___x_1620_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1621_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1622_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1623_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1624_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1626_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1627_: u8 = 0;
    let mut v___x_1629_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1630_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1631_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                lean_inc(v_n_1504_);
                v___x_1510_ = l_Lean_mkRecName(v_n_1504_);
                lean_inc(v___x_1510_);
                v___x_1511_ = l_Lean_getConstInfo___at___00mkRecOn_spec__0(
                    v___x_1510_,
                    v_a_1505_,
                    v_a_1506_,
                    v_a_1507_,
                    v_a_1508_,
                );
                if lean_obj_tag(v___x_1511_) == 0 {
                    v_a_1512_ = lean_ctor_get(v___x_1511_, 0);
                    lean_inc(v_a_1512_);
                    lean_dec_ref_known(v___x_1511_, 1);
                    if lean_obj_tag(v_a_1512_) == 7 {
                        lean_dec(v___x_1510_);
                        v_val_1513_ = lean_ctor_get(v_a_1512_, 0);
                        v_isSharedCheck_1619_ = (!lean_is_exclusive(v_a_1512_)) as u8;
                        if v_isSharedCheck_1619_ == 0 {
                            v___x_1515_ = v_a_1512_;
                            v_isShared_1516_ = v_isSharedCheck_1619_;
                            state = 1;
                            continue;
                        } else {
                            lean_inc(v_val_1513_);
                            lean_dec(v_a_1512_);
                            v___x_1515_ = lean_box(0);
                            v_isShared_1516_ = v_isSharedCheck_1619_;
                            state = 1;
                            continue;
                        }
                    } else {
                        lean_dec(v_a_1512_);
                        lean_dec(v_n_1504_);
                        v___x_1620_ = l_Lean_MessageData_ofName(v___x_1510_);
                        v___x_1621_ = lean_obj_once(
                            core::ptr::addr_of_mut!(l_mkRecOn___closed__1),
                            core::ptr::addr_of_mut!(l_mkRecOn___closed__1_once),
                            _init_l_mkRecOn___closed__1,
                        );
                        v___x_1622_ = lean_alloc_ctor(7, 2, (0) as u32);
                        lean_ctor_set(v___x_1622_, 0, v___x_1620_);
                        lean_ctor_set(v___x_1622_, 1, v___x_1621_);
                        v___x_1623_ = l_Lean_throwError___at___00mkRecOn_spec__6___redArg(
                            v___x_1622_,
                            v_a_1505_,
                            v_a_1506_,
                            v_a_1507_,
                            v_a_1508_,
                        );
                        return v___x_1623_;
                    }
                } else {
                    lean_dec(v___x_1510_);
                    lean_dec(v_n_1504_);
                    v_a_1624_ = lean_ctor_get(v___x_1511_, 0);
                    v_isSharedCheck_1631_ = (!lean_is_exclusive(v___x_1511_)) as u8;
                    if v_isSharedCheck_1631_ == 0 {
                        v___x_1626_ = v___x_1511_;
                        v_isShared_1627_ = v_isSharedCheck_1631_;
                        state = 15;
                        continue;
                    } else {
                        lean_inc(v_a_1624_);
                        lean_dec(v___x_1511_);
                        v___x_1626_ = lean_box(0);
                        v_isShared_1627_ = v_isSharedCheck_1631_;
                        state = 15;
                        continue;
                    }
                }
            }
            1 => {
                v_toConstantVal_1517_ = lean_ctor_get(v_val_1513_, 0);
                lean_inc_ref(v_toConstantVal_1517_);
                v_numIndices_1518_ = lean_ctor_get(v_val_1513_, 3);
                lean_inc(v_numIndices_1518_);
                v_numMinors_1519_ = lean_ctor_get(v_val_1513_, 5);
                lean_inc(v_numMinors_1519_);
                lean_dec_ref(v_val_1513_);
                v_name_1520_ = lean_ctor_get(v_toConstantVal_1517_, 0);
                lean_inc(v_name_1520_);
                v_levelParams_1521_ = lean_ctor_get(v_toConstantVal_1517_, 1);
                lean_inc(v_levelParams_1521_);
                v_type_1522_ = lean_ctor_get(v_toConstantVal_1517_, 2);
                lean_inc_ref(v_type_1522_);
                lean_dec_ref(v_toConstantVal_1517_);
                v___f_1523_ =
                    lean_alloc_closure(l_mkRecOn___lam__0___boxed as *mut core::ffi::c_void, 12, 5);
                lean_closure_set(v___f_1523_, 0, v_levelParams_1521_);
                lean_closure_set(v___f_1523_, 1, v_name_1520_);
                lean_closure_set(v___f_1523_, 2, v_numMinors_1519_);
                lean_closure_set(v___f_1523_, 3, v_numIndices_1518_);
                lean_closure_set(v___f_1523_, 4, v_n_1504_);
                v___x_1524_ = 0;
                v___x_1525_ = l_Lean_Meta_forallTelescope___at___00mkRecOn_spec__4___redArg(
                    v_type_1522_,
                    v___f_1523_,
                    v___x_1524_,
                    v_a_1505_,
                    v_a_1506_,
                    v_a_1507_,
                    v_a_1508_,
                );
                if lean_obj_tag(v___x_1525_) == 0 {
                    v_a_1526_ = lean_ctor_get(v___x_1525_, 0);
                    lean_inc_n(v_a_1526_, 2);
                    lean_dec_ref_known(v___x_1525_, 1);
                    if v_isShared_1516_ == 0 {
                        lean_ctor_set_tag(v___x_1515_, 1);
                        lean_ctor_set(v___x_1515_, 0, v_a_1526_);
                        v___x_1528_ = v___x_1515_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_1610_ = lean_alloc_ctor(1, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_1610_, 0, v_a_1526_);
                        v___x_1528_ = v_reuseFailAlloc_1610_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_1515_);
                    v_a_1611_ = lean_ctor_get(v___x_1525_, 0);
                    v_isSharedCheck_1618_ = (!lean_is_exclusive(v___x_1525_)) as u8;
                    if v_isSharedCheck_1618_ == 0 {
                        v___x_1613_ = v___x_1525_;
                        v_isShared_1614_ = v_isSharedCheck_1618_;
                        state = 13;
                        continue;
                    } else {
                        lean_inc(v_a_1611_);
                        lean_dec(v___x_1525_);
                        v___x_1613_ = lean_box(0);
                        v_isShared_1614_ = v_isSharedCheck_1618_;
                        state = 13;
                        continue;
                    }
                }
            }
            2 => {
                v___x_1529_ = l_Lean_addDecl(v___x_1528_, v___x_1524_, v_a_1507_, v_a_1508_);
                if lean_obj_tag(v___x_1529_) == 0 {
                    lean_dec_ref_known(v___x_1529_, 1);
                    v_toConstantVal_1530_ = lean_ctor_get(v_a_1526_, 0);
                    lean_inc_ref(v_toConstantVal_1530_);
                    lean_dec(v_a_1526_);
                    v_name_1531_ = lean_ctor_get(v_toConstantVal_1530_, 0);
                    lean_inc_n(v_name_1531_, 2);
                    lean_dec_ref(v_toConstantVal_1530_);
                    v___x_1532_ = l_Lean_setReducibleAttribute___at___00mkRecOn_spec__5(
                        v_name_1531_,
                        v_a_1505_,
                        v_a_1506_,
                        v_a_1507_,
                        v_a_1508_,
                    );
                    v_isSharedCheck_1608_ = (!lean_is_exclusive(v___x_1532_)) as u8;
                    if v_isSharedCheck_1608_ == 0 {
                        v_unused_1609_ = lean_ctor_get(v___x_1532_, 0);
                        lean_dec(v_unused_1609_);
                        v___x_1534_ = v___x_1532_;
                        v_isShared_1535_ = v_isSharedCheck_1608_;
                        state = 3;
                        continue;
                    } else {
                        lean_dec(v___x_1532_);
                        v___x_1534_ = lean_box(0);
                        v_isShared_1535_ = v_isSharedCheck_1608_;
                        state = 3;
                        continue;
                    }
                } else {
                    lean_dec(v_a_1526_);
                    return v___x_1529_;
                }
            }
            3 => {
                v___x_1536_ = lean_st_ref_take(v_a_1508_);
                v_env_1537_ = lean_ctor_get(v___x_1536_, 0);
                v_nextMacroScope_1538_ = lean_ctor_get(v___x_1536_, 1);
                v_ngen_1539_ = lean_ctor_get(v___x_1536_, 2);
                v_auxDeclNGen_1540_ = lean_ctor_get(v___x_1536_, 3);
                v_traceState_1541_ = lean_ctor_get(v___x_1536_, 4);
                v_messages_1542_ = lean_ctor_get(v___x_1536_, 6);
                v_infoState_1543_ = lean_ctor_get(v___x_1536_, 7);
                v_snapshotTasks_1544_ = lean_ctor_get(v___x_1536_, 8);
                v_isSharedCheck_1606_ = (!lean_is_exclusive(v___x_1536_)) as u8;
                if v_isSharedCheck_1606_ == 0 {
                    v_unused_1607_ = lean_ctor_get(v___x_1536_, 5);
                    lean_dec(v_unused_1607_);
                    v___x_1546_ = v___x_1536_;
                    v_isShared_1547_ = v_isSharedCheck_1606_;
                    state = 4;
                    continue;
                } else {
                    lean_inc(v_snapshotTasks_1544_);
                    lean_inc(v_infoState_1543_);
                    lean_inc(v_messages_1542_);
                    lean_inc(v_traceState_1541_);
                    lean_inc(v_auxDeclNGen_1540_);
                    lean_inc(v_ngen_1539_);
                    lean_inc(v_nextMacroScope_1538_);
                    lean_inc(v_env_1537_);
                    lean_dec(v___x_1536_);
                    v___x_1546_ = lean_box(0);
                    v_isShared_1547_ = v_isSharedCheck_1606_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                lean_inc(v_name_1531_);
                v___x_1548_ = l_Lean_markAuxRecursor(v_env_1537_, v_name_1531_);
                v___x_1549_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00mkRecOn_spec__5_spec__6___redArg___closed__2), core::ptr::addr_of_mut!(l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00mkRecOn_spec__5_spec__6___redArg___closed__2_once), _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00mkRecOn_spec__5_spec__6___redArg___closed__2);
                if v_isShared_1547_ == 0 {
                    lean_ctor_set(v___x_1546_, 5, v___x_1549_);
                    lean_ctor_set(v___x_1546_, 0, v___x_1548_);
                    v___x_1551_ = v___x_1546_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_1605_ = lean_alloc_ctor(0, 9, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1605_, 0, v___x_1548_);
                    lean_ctor_set(v_reuseFailAlloc_1605_, 1, v_nextMacroScope_1538_);
                    lean_ctor_set(v_reuseFailAlloc_1605_, 2, v_ngen_1539_);
                    lean_ctor_set(v_reuseFailAlloc_1605_, 3, v_auxDeclNGen_1540_);
                    lean_ctor_set(v_reuseFailAlloc_1605_, 4, v_traceState_1541_);
                    lean_ctor_set(v_reuseFailAlloc_1605_, 5, v___x_1549_);
                    lean_ctor_set(v_reuseFailAlloc_1605_, 6, v_messages_1542_);
                    lean_ctor_set(v_reuseFailAlloc_1605_, 7, v_infoState_1543_);
                    lean_ctor_set(v_reuseFailAlloc_1605_, 8, v_snapshotTasks_1544_);
                    v___x_1551_ = v_reuseFailAlloc_1605_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v___x_1552_ = lean_st_ref_set(v_a_1508_, v___x_1551_);
                v___x_1553_ = lean_st_ref_take(v_a_1506_);
                v_mctx_1554_ = lean_ctor_get(v___x_1553_, 0);
                v_zetaDeltaFVarIds_1555_ = lean_ctor_get(v___x_1553_, 2);
                v_postponed_1556_ = lean_ctor_get(v___x_1553_, 3);
                v_diag_1557_ = lean_ctor_get(v___x_1553_, 4);
                v_isSharedCheck_1603_ = (!lean_is_exclusive(v___x_1553_)) as u8;
                if v_isSharedCheck_1603_ == 0 {
                    v_unused_1604_ = lean_ctor_get(v___x_1553_, 1);
                    lean_dec(v_unused_1604_);
                    v___x_1559_ = v___x_1553_;
                    v_isShared_1560_ = v_isSharedCheck_1603_;
                    state = 6;
                    continue;
                } else {
                    lean_inc(v_diag_1557_);
                    lean_inc(v_postponed_1556_);
                    lean_inc(v_zetaDeltaFVarIds_1555_);
                    lean_inc(v_mctx_1554_);
                    lean_dec(v___x_1553_);
                    v___x_1559_ = lean_box(0);
                    v_isShared_1560_ = v_isSharedCheck_1603_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                v___x_1561_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00mkRecOn_spec__5_spec__6___redArg___closed__3), core::ptr::addr_of_mut!(l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00mkRecOn_spec__5_spec__6___redArg___closed__3_once), _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00mkRecOn_spec__5_spec__6___redArg___closed__3);
                if v_isShared_1560_ == 0 {
                    lean_ctor_set(v___x_1559_, 1, v___x_1561_);
                    v___x_1563_ = v___x_1559_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_1602_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1602_, 0, v_mctx_1554_);
                    lean_ctor_set(v_reuseFailAlloc_1602_, 1, v___x_1561_);
                    lean_ctor_set(v_reuseFailAlloc_1602_, 2, v_zetaDeltaFVarIds_1555_);
                    lean_ctor_set(v_reuseFailAlloc_1602_, 3, v_postponed_1556_);
                    lean_ctor_set(v_reuseFailAlloc_1602_, 4, v_diag_1557_);
                    v___x_1563_ = v_reuseFailAlloc_1602_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                v___x_1564_ = lean_st_ref_set(v_a_1506_, v___x_1563_);
                v___x_1565_ = lean_st_ref_take(v_a_1508_);
                v_env_1566_ = lean_ctor_get(v___x_1565_, 0);
                v_nextMacroScope_1567_ = lean_ctor_get(v___x_1565_, 1);
                v_ngen_1568_ = lean_ctor_get(v___x_1565_, 2);
                v_auxDeclNGen_1569_ = lean_ctor_get(v___x_1565_, 3);
                v_traceState_1570_ = lean_ctor_get(v___x_1565_, 4);
                v_messages_1571_ = lean_ctor_get(v___x_1565_, 6);
                v_infoState_1572_ = lean_ctor_get(v___x_1565_, 7);
                v_snapshotTasks_1573_ = lean_ctor_get(v___x_1565_, 8);
                v_isSharedCheck_1600_ = (!lean_is_exclusive(v___x_1565_)) as u8;
                if v_isSharedCheck_1600_ == 0 {
                    v_unused_1601_ = lean_ctor_get(v___x_1565_, 5);
                    lean_dec(v_unused_1601_);
                    v___x_1575_ = v___x_1565_;
                    v_isShared_1576_ = v_isSharedCheck_1600_;
                    state = 8;
                    continue;
                } else {
                    lean_inc(v_snapshotTasks_1573_);
                    lean_inc(v_infoState_1572_);
                    lean_inc(v_messages_1571_);
                    lean_inc(v_traceState_1570_);
                    lean_inc(v_auxDeclNGen_1569_);
                    lean_inc(v_ngen_1568_);
                    lean_inc(v_nextMacroScope_1567_);
                    lean_inc(v_env_1566_);
                    lean_dec(v___x_1565_);
                    v___x_1575_ = lean_box(0);
                    v_isShared_1576_ = v_isSharedCheck_1600_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                v___x_1577_ = l_Lean_addProtected(v_env_1566_, v_name_1531_);
                if v_isShared_1576_ == 0 {
                    lean_ctor_set(v___x_1575_, 5, v___x_1549_);
                    lean_ctor_set(v___x_1575_, 0, v___x_1577_);
                    v___x_1579_ = v___x_1575_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_1599_ = lean_alloc_ctor(0, 9, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1599_, 0, v___x_1577_);
                    lean_ctor_set(v_reuseFailAlloc_1599_, 1, v_nextMacroScope_1567_);
                    lean_ctor_set(v_reuseFailAlloc_1599_, 2, v_ngen_1568_);
                    lean_ctor_set(v_reuseFailAlloc_1599_, 3, v_auxDeclNGen_1569_);
                    lean_ctor_set(v_reuseFailAlloc_1599_, 4, v_traceState_1570_);
                    lean_ctor_set(v_reuseFailAlloc_1599_, 5, v___x_1549_);
                    lean_ctor_set(v_reuseFailAlloc_1599_, 6, v_messages_1571_);
                    lean_ctor_set(v_reuseFailAlloc_1599_, 7, v_infoState_1572_);
                    lean_ctor_set(v_reuseFailAlloc_1599_, 8, v_snapshotTasks_1573_);
                    v___x_1579_ = v_reuseFailAlloc_1599_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                v___x_1580_ = lean_st_ref_set(v_a_1508_, v___x_1579_);
                v___x_1581_ = lean_st_ref_take(v_a_1506_);
                v_mctx_1582_ = lean_ctor_get(v___x_1581_, 0);
                v_zetaDeltaFVarIds_1583_ = lean_ctor_get(v___x_1581_, 2);
                v_postponed_1584_ = lean_ctor_get(v___x_1581_, 3);
                v_diag_1585_ = lean_ctor_get(v___x_1581_, 4);
                v_isSharedCheck_1597_ = (!lean_is_exclusive(v___x_1581_)) as u8;
                if v_isSharedCheck_1597_ == 0 {
                    v_unused_1598_ = lean_ctor_get(v___x_1581_, 1);
                    lean_dec(v_unused_1598_);
                    v___x_1587_ = v___x_1581_;
                    v_isShared_1588_ = v_isSharedCheck_1597_;
                    state = 10;
                    continue;
                } else {
                    lean_inc(v_diag_1585_);
                    lean_inc(v_postponed_1584_);
                    lean_inc(v_zetaDeltaFVarIds_1583_);
                    lean_inc(v_mctx_1582_);
                    lean_dec(v___x_1581_);
                    v___x_1587_ = lean_box(0);
                    v_isShared_1588_ = v_isSharedCheck_1597_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                if v_isShared_1588_ == 0 {
                    lean_ctor_set(v___x_1587_, 1, v___x_1561_);
                    v___x_1590_ = v___x_1587_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_1596_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1596_, 0, v_mctx_1582_);
                    lean_ctor_set(v_reuseFailAlloc_1596_, 1, v___x_1561_);
                    lean_ctor_set(v_reuseFailAlloc_1596_, 2, v_zetaDeltaFVarIds_1583_);
                    lean_ctor_set(v_reuseFailAlloc_1596_, 3, v_postponed_1584_);
                    lean_ctor_set(v_reuseFailAlloc_1596_, 4, v_diag_1585_);
                    v___x_1590_ = v_reuseFailAlloc_1596_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                v___x_1591_ = lean_st_ref_set(v_a_1506_, v___x_1590_);
                v___x_1592_ = lean_box(0);
                if v_isShared_1535_ == 0 {
                    lean_ctor_set(v___x_1534_, 0, v___x_1592_);
                    v___x_1594_ = v___x_1534_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_1595_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1595_, 0, v___x_1592_);
                    v___x_1594_ = v_reuseFailAlloc_1595_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                return v___x_1594_;
            }
            13 => {
                if v_isShared_1614_ == 0 {
                    v___x_1616_ = v___x_1613_;
                    state = 14;
                    continue;
                } else {
                    v_reuseFailAlloc_1617_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1617_, 0, v_a_1611_);
                    v___x_1616_ = v_reuseFailAlloc_1617_;
                    state = 14;
                    continue;
                }
            }
            14 => {
                return v___x_1616_;
            }
            15 => {
                if v_isShared_1627_ == 0 {
                    v___x_1629_ = v___x_1626_;
                    state = 16;
                    continue;
                } else {
                    v_reuseFailAlloc_1630_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1630_, 0, v_a_1624_);
                    v___x_1629_ = v_reuseFailAlloc_1630_;
                    state = 16;
                    continue;
                }
            }
            16 => {
                return v___x_1629_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_mkRecOn___boxed(
    mut v_n_1632_: *mut LeanObject,
    mut v_a_1633_: *mut LeanObject,
    mut v_a_1634_: *mut LeanObject,
    mut v_a_1635_: *mut LeanObject,
    mut v_a_1636_: *mut LeanObject,
    mut v_a_1637_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1638_: *mut LeanObject = core::ptr::null_mut();
    v_res_1638_ = l_mkRecOn(v_n_1632_, v_a_1633_, v_a_1634_, v_a_1635_, v_a_1636_);
    lean_dec(v_a_1636_);
    lean_dec_ref(v_a_1635_);
    lean_dec(v_a_1634_);
    lean_dec_ref(v_a_1633_);
    return v_res_1638_;
}
pub unsafe fn l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00mkRecOn_spec__2(
    mut v_inst_1639_: *mut LeanObject,
    mut v_R_1640_: *mut LeanObject,
    mut v_a_1641_: *mut LeanObject,
    mut v_b_1642_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1643_: *mut LeanObject = core::ptr::null_mut();
    v___x_1643_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00mkRecOn_spec__2___redArg(v_a_1641_, v_b_1642_);
    return v___x_1643_;
}
pub unsafe fn l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00mkRecOn_spec__5_spec__6(
    mut v_declName_1644_: *mut LeanObject,
    mut v_s_1645_: u8,
    mut v___y_1646_: *mut LeanObject,
    mut v___y_1647_: *mut LeanObject,
    mut v___y_1648_: *mut LeanObject,
    mut v___y_1649_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1651_: *mut LeanObject = core::ptr::null_mut();
    v___x_1651_ = l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00mkRecOn_spec__5_spec__6___redArg(v_declName_1644_, v_s_1645_, v___y_1647_, v___y_1649_);
    return v___x_1651_;
}
pub unsafe fn l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00mkRecOn_spec__5_spec__6___boxed(
    mut v_declName_1652_: *mut LeanObject,
    mut v_s_1653_: *mut LeanObject,
    mut v___y_1654_: *mut LeanObject,
    mut v___y_1655_: *mut LeanObject,
    mut v___y_1656_: *mut LeanObject,
    mut v___y_1657_: *mut LeanObject,
    mut v___y_1658_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_s_boxed_1659_: u8 = 0;
    let mut v_res_1660_: *mut LeanObject = core::ptr::null_mut();
    v_s_boxed_1659_ = (lean_unbox(v_s_1653_) as u8);
    v_res_1660_ = l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00mkRecOn_spec__5_spec__6(v_declName_1652_, v_s_boxed_1659_, v___y_1654_, v___y_1655_, v___y_1656_, v___y_1657_);
    lean_dec(v___y_1657_);
    lean_dec_ref(v___y_1656_);
    lean_dec(v___y_1655_);
    lean_dec_ref(v___y_1654_);
    return v_res_1660_;
}
pub unsafe fn l_Lean_throwError___at___00mkRecOn_spec__6(
    mut v_00_u03b1_1661_: *mut LeanObject,
    mut v_msg_1662_: *mut LeanObject,
    mut v___y_1663_: *mut LeanObject,
    mut v___y_1664_: *mut LeanObject,
    mut v___y_1665_: *mut LeanObject,
    mut v___y_1666_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1668_: *mut LeanObject = core::ptr::null_mut();
    v___x_1668_ = l_Lean_throwError___at___00mkRecOn_spec__6___redArg(
        v_msg_1662_,
        v___y_1663_,
        v___y_1664_,
        v___y_1665_,
        v___y_1666_,
    );
    return v___x_1668_;
}
pub unsafe fn l_Lean_throwError___at___00mkRecOn_spec__6___boxed(
    mut v_00_u03b1_1669_: *mut LeanObject,
    mut v_msg_1670_: *mut LeanObject,
    mut v___y_1671_: *mut LeanObject,
    mut v___y_1672_: *mut LeanObject,
    mut v___y_1673_: *mut LeanObject,
    mut v___y_1674_: *mut LeanObject,
    mut v___y_1675_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1676_: *mut LeanObject = core::ptr::null_mut();
    v_res_1676_ = l_Lean_throwError___at___00mkRecOn_spec__6(
        v_00_u03b1_1669_,
        v_msg_1670_,
        v___y_1671_,
        v___y_1672_,
        v___y_1673_,
        v___y_1674_,
    );
    lean_dec(v___y_1674_);
    lean_dec_ref(v___y_1673_);
    lean_dec(v___y_1672_);
    lean_dec_ref(v___y_1671_);
    return v_res_1676_;
}
pub unsafe fn l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkRecOn_spec__0_spec__0(
    mut v_00_u03b1_1677_: *mut LeanObject,
    mut v_constName_1678_: *mut LeanObject,
    mut v___y_1679_: *mut LeanObject,
    mut v___y_1680_: *mut LeanObject,
    mut v___y_1681_: *mut LeanObject,
    mut v___y_1682_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1684_: *mut LeanObject = core::ptr::null_mut();
    v___x_1684_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkRecOn_spec__0_spec__0___redArg(v_constName_1678_, v___y_1679_, v___y_1680_, v___y_1681_, v___y_1682_);
    return v___x_1684_;
}
pub unsafe fn l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkRecOn_spec__0_spec__0___boxed(
    mut v_00_u03b1_1685_: *mut LeanObject,
    mut v_constName_1686_: *mut LeanObject,
    mut v___y_1687_: *mut LeanObject,
    mut v___y_1688_: *mut LeanObject,
    mut v___y_1689_: *mut LeanObject,
    mut v___y_1690_: *mut LeanObject,
    mut v___y_1691_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1692_: *mut LeanObject = core::ptr::null_mut();
    v_res_1692_ =
        l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkRecOn_spec__0_spec__0(
            v_00_u03b1_1685_,
            v_constName_1686_,
            v___y_1687_,
            v___y_1688_,
            v___y_1689_,
            v___y_1690_,
        );
    lean_dec(v___y_1690_);
    lean_dec_ref(v___y_1689_);
    lean_dec(v___y_1688_);
    lean_dec_ref(v___y_1687_);
    return v_res_1692_;
}
pub unsafe fn l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkRecOn_spec__0_spec__0_spec__3(
    mut v_00_u03b1_1693_: *mut LeanObject,
    mut v_ref_1694_: *mut LeanObject,
    mut v_constName_1695_: *mut LeanObject,
    mut v___y_1696_: *mut LeanObject,
    mut v___y_1697_: *mut LeanObject,
    mut v___y_1698_: *mut LeanObject,
    mut v___y_1699_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1701_: *mut LeanObject = core::ptr::null_mut();
    v___x_1701_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkRecOn_spec__0_spec__0_spec__3___redArg(v_ref_1694_, v_constName_1695_, v___y_1696_, v___y_1697_, v___y_1698_, v___y_1699_);
    return v___x_1701_;
}
pub unsafe fn l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkRecOn_spec__0_spec__0_spec__3___boxed(
    mut v_00_u03b1_1702_: *mut LeanObject,
    mut v_ref_1703_: *mut LeanObject,
    mut v_constName_1704_: *mut LeanObject,
    mut v___y_1705_: *mut LeanObject,
    mut v___y_1706_: *mut LeanObject,
    mut v___y_1707_: *mut LeanObject,
    mut v___y_1708_: *mut LeanObject,
    mut v___y_1709_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1710_: *mut LeanObject = core::ptr::null_mut();
    v_res_1710_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkRecOn_spec__0_spec__0_spec__3(v_00_u03b1_1702_, v_ref_1703_, v_constName_1704_, v___y_1705_, v___y_1706_, v___y_1707_, v___y_1708_);
    lean_dec(v___y_1708_);
    lean_dec_ref(v___y_1707_);
    lean_dec(v___y_1706_);
    lean_dec_ref(v___y_1705_);
    lean_dec(v_ref_1703_);
    return v_res_1710_;
}
pub unsafe fn l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkRecOn_spec__0_spec__0_spec__3_spec__10(
    mut v_00_u03b1_1711_: *mut LeanObject,
    mut v_ref_1712_: *mut LeanObject,
    mut v_msg_1713_: *mut LeanObject,
    mut v_declHint_1714_: *mut LeanObject,
    mut v___y_1715_: *mut LeanObject,
    mut v___y_1716_: *mut LeanObject,
    mut v___y_1717_: *mut LeanObject,
    mut v___y_1718_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1720_: *mut LeanObject = core::ptr::null_mut();
    v___x_1720_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkRecOn_spec__0_spec__0_spec__3_spec__10___redArg(v_ref_1712_, v_msg_1713_, v_declHint_1714_, v___y_1715_, v___y_1716_, v___y_1717_, v___y_1718_);
    return v___x_1720_;
}
pub unsafe fn l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkRecOn_spec__0_spec__0_spec__3_spec__10___boxed(
    mut v_00_u03b1_1721_: *mut LeanObject,
    mut v_ref_1722_: *mut LeanObject,
    mut v_msg_1723_: *mut LeanObject,
    mut v_declHint_1724_: *mut LeanObject,
    mut v___y_1725_: *mut LeanObject,
    mut v___y_1726_: *mut LeanObject,
    mut v___y_1727_: *mut LeanObject,
    mut v___y_1728_: *mut LeanObject,
    mut v___y_1729_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1730_: *mut LeanObject = core::ptr::null_mut();
    v_res_1730_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkRecOn_spec__0_spec__0_spec__3_spec__10(v_00_u03b1_1721_, v_ref_1722_, v_msg_1723_, v_declHint_1724_, v___y_1725_, v___y_1726_, v___y_1727_, v___y_1728_);
    lean_dec(v___y_1728_);
    lean_dec_ref(v___y_1727_);
    lean_dec(v___y_1726_);
    lean_dec_ref(v___y_1725_);
    lean_dec(v_ref_1722_);
    return v_res_1730_;
}
pub unsafe fn l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkRecOn_spec__0_spec__0_spec__3_spec__10_spec__11_spec__12(
    mut v_msg_1731_: *mut LeanObject,
    mut v_declHint_1732_: *mut LeanObject,
    mut v___y_1733_: *mut LeanObject,
    mut v___y_1734_: *mut LeanObject,
    mut v___y_1735_: *mut LeanObject,
    mut v___y_1736_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1738_: *mut LeanObject = core::ptr::null_mut();
    v___x_1738_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkRecOn_spec__0_spec__0_spec__3_spec__10_spec__11_spec__12___redArg(v_msg_1731_, v_declHint_1732_, v___y_1736_);
    return v___x_1738_;
}
pub unsafe fn l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkRecOn_spec__0_spec__0_spec__3_spec__10_spec__11_spec__12___boxed(
    mut v_msg_1739_: *mut LeanObject,
    mut v_declHint_1740_: *mut LeanObject,
    mut v___y_1741_: *mut LeanObject,
    mut v___y_1742_: *mut LeanObject,
    mut v___y_1743_: *mut LeanObject,
    mut v___y_1744_: *mut LeanObject,
    mut v___y_1745_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1746_: *mut LeanObject = core::ptr::null_mut();
    v_res_1746_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkRecOn_spec__0_spec__0_spec__3_spec__10_spec__11_spec__12(v_msg_1739_, v_declHint_1740_, v___y_1741_, v___y_1742_, v___y_1743_, v___y_1744_);
    lean_dec(v___y_1744_);
    lean_dec_ref(v___y_1743_);
    lean_dec(v___y_1742_);
    lean_dec_ref(v___y_1741_);
    return v_res_1746_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkRecOn_spec__0_spec__0_spec__3_spec__10_spec__12(
    mut v_00_u03b1_1747_: *mut LeanObject,
    mut v_ref_1748_: *mut LeanObject,
    mut v_msg_1749_: *mut LeanObject,
    mut v___y_1750_: *mut LeanObject,
    mut v___y_1751_: *mut LeanObject,
    mut v___y_1752_: *mut LeanObject,
    mut v___y_1753_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1755_: *mut LeanObject = core::ptr::null_mut();
    v___x_1755_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkRecOn_spec__0_spec__0_spec__3_spec__10_spec__12___redArg(v_ref_1748_, v_msg_1749_, v___y_1750_, v___y_1751_, v___y_1752_, v___y_1753_);
    return v___x_1755_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkRecOn_spec__0_spec__0_spec__3_spec__10_spec__12___boxed(
    mut v_00_u03b1_1756_: *mut LeanObject,
    mut v_ref_1757_: *mut LeanObject,
    mut v_msg_1758_: *mut LeanObject,
    mut v___y_1759_: *mut LeanObject,
    mut v___y_1760_: *mut LeanObject,
    mut v___y_1761_: *mut LeanObject,
    mut v___y_1762_: *mut LeanObject,
    mut v___y_1763_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1764_: *mut LeanObject = core::ptr::null_mut();
    v_res_1764_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkRecOn_spec__0_spec__0_spec__3_spec__10_spec__12(v_00_u03b1_1756_, v_ref_1757_, v_msg_1758_, v___y_1759_, v___y_1760_, v___y_1761_, v___y_1762_);
    lean_dec(v___y_1762_);
    lean_dec_ref(v___y_1761_);
    lean_dec(v___y_1760_);
    lean_dec_ref(v___y_1759_);
    lean_dec(v_ref_1757_);
    return v_res_1764_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Meta_Constructions_RecOn(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_AddDecl(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_CompletionName(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Meta_Constructions_RecOn(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Meta_Constructions_RecOn(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_AddDecl(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Meta_CompletionName(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Constructions_RecOn(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Lean_Meta_Constructions_RecOn(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Lean_Meta_Constructions_RecOn(builtin);
}
