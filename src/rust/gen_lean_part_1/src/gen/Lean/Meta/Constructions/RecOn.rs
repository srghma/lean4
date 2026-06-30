// Lean compiler output
// Module: Lean.Meta.Constructions.RecOn
// Imports: Lean.AddDecl Lean.Meta.CompletionName
use crate::ffi::{
    lean_array_fget, lean_array_get, lean_array_get_size, lean_array_push,
    lean_mk_empty_array_with_capacity, lean_nat_add, lean_nat_dec_lt, lean_nat_sub,
    lean_st_ref_get, lean_st_ref_set, lean_st_ref_take,
};
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
pub static l_mkRecOn___lam__0___closed__0_value: leanh::LeanArrayObject<0> =
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
static mut l_mkRecOn___lam__0___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_mkRecOn___lam__0___closed__0_value) as *mut leanh::LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkRecOn_spec__0_spec__0_spec__3_spec__10_spec__11_spec__12___redArg___closed__0_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkRecOn_spec__0_spec__0_spec__3_spec__10_spec__11_spec__12___redArg___closed__0: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkRecOn_spec__0_spec__0_spec__3_spec__10_spec__11_spec__12___redArg___closed__1_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkRecOn_spec__0_spec__0_spec__3_spec__10_spec__11_spec__12___redArg___closed__1: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkRecOn_spec__0_spec__0_spec__3_spec__10_spec__11_spec__12___redArg___closed__2_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkRecOn_spec__0_spec__0_spec__3_spec__10_spec__11_spec__12___redArg___closed__2: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkRecOn_spec__0_spec__0_spec__3_spec__10_spec__11_spec__12___redArg___closed__3_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkRecOn_spec__0_spec__0_spec__3_spec__10_spec__11_spec__12___redArg___closed__3: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkRecOn_spec__0_spec__0_spec__3_spec__10_spec__11_spec__12___redArg___closed__4_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkRecOn_spec__0_spec__0_spec__3_spec__10_spec__11_spec__12___redArg___closed__4: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkRecOn_spec__0_spec__0_spec__3_spec__10_spec__11_spec__12___redArg___closed__5_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkRecOn_spec__0_spec__0_spec__3_spec__10_spec__11_spec__12___redArg___closed__5: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkRecOn_spec__0_spec__0_spec__3_spec__10_spec__11_spec__12___redArg___closed__6_value: leanh::LeanStringObject<24> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 24, m_capacity: 24, m_length: 23, m_data: [65, 32, 112, 114, 105, 118, 97, 116, 101, 32, 100, 101, 99, 108, 97, 114, 97, 116, 105, 111, 110, 32, 96, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkRecOn_spec__0_spec__0_spec__3_spec__10_spec__11_spec__12___redArg___closed__6: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkRecOn_spec__0_spec__0_spec__3_spec__10_spec__11_spec__12___redArg___closed__6_value) as *mut leanh::LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkRecOn_spec__0_spec__0_spec__3_spec__10_spec__11_spec__12___redArg___closed__7_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkRecOn_spec__0_spec__0_spec__3_spec__10_spec__11_spec__12___redArg___closed__7: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkRecOn_spec__0_spec__0_spec__3_spec__10_spec__11_spec__12___redArg___closed__8_value: leanh::LeanStringObject<79> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 79, m_capacity: 79, m_length: 78, m_data: [96, 32, 40, 102, 114, 111, 109, 32, 116, 104, 101, 32, 99, 117, 114, 114, 101, 110, 116, 32, 109, 111, 100, 117, 108, 101, 41, 32, 101, 120, 105, 115, 116, 115, 32, 98, 117, 116, 32, 119, 111, 117, 108, 100, 32, 110, 101, 101, 100, 32, 116, 111, 32, 98, 101, 32, 112, 117, 98, 108, 105, 99, 32, 116, 111, 32, 97, 99, 99, 101, 115, 115, 32, 104, 101, 114, 101, 46, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkRecOn_spec__0_spec__0_spec__3_spec__10_spec__11_spec__12___redArg___closed__8: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkRecOn_spec__0_spec__0_spec__3_spec__10_spec__11_spec__12___redArg___closed__8_value) as *mut leanh::LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkRecOn_spec__0_spec__0_spec__3_spec__10_spec__11_spec__12___redArg___closed__9_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkRecOn_spec__0_spec__0_spec__3_spec__10_spec__11_spec__12___redArg___closed__9: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkRecOn_spec__0_spec__0_spec__3_spec__10_spec__11_spec__12___redArg___closed__10_value: leanh::LeanStringObject<23> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 23, m_capacity: 23, m_length: 22, m_data: [65, 32, 112, 117, 98, 108, 105, 99, 32, 100, 101, 99, 108, 97, 114, 97, 116, 105, 111, 110, 32, 96, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkRecOn_spec__0_spec__0_spec__3_spec__10_spec__11_spec__12___redArg___closed__10: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkRecOn_spec__0_spec__0_spec__3_spec__10_spec__11_spec__12___redArg___closed__10_value) as *mut leanh::LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkRecOn_spec__0_spec__0_spec__3_spec__10_spec__11_spec__12___redArg___closed__11_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkRecOn_spec__0_spec__0_spec__3_spec__10_spec__11_spec__12___redArg___closed__11: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkRecOn_spec__0_spec__0_spec__3_spec__10_spec__11_spec__12___redArg___closed__12_value: leanh::LeanStringObject<68> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 68, m_capacity: 68, m_length: 67, m_data: [96, 32, 101, 120, 105, 115, 116, 115, 32, 98, 117, 116, 32, 105, 115, 32, 105, 109, 112, 111, 114, 116, 101, 100, 32, 112, 114, 105, 118, 97, 116, 101, 108, 121, 59, 32, 99, 111, 110, 115, 105, 100, 101, 114, 32, 97, 100, 100, 105, 110, 103, 32, 96, 112, 117, 98, 108, 105, 99, 32, 105, 109, 112, 111, 114, 116, 32, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkRecOn_spec__0_spec__0_spec__3_spec__10_spec__11_spec__12___redArg___closed__12: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkRecOn_spec__0_spec__0_spec__3_spec__10_spec__11_spec__12___redArg___closed__12_value) as *mut leanh::LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkRecOn_spec__0_spec__0_spec__3_spec__10_spec__11_spec__12___redArg___closed__13_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkRecOn_spec__0_spec__0_spec__3_spec__10_spec__11_spec__12___redArg___closed__13: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkRecOn_spec__0_spec__0_spec__3_spec__10_spec__11_spec__12___redArg___closed__14_value: leanh::LeanStringObject<3> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [96, 46, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkRecOn_spec__0_spec__0_spec__3_spec__10_spec__11_spec__12___redArg___closed__14: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkRecOn_spec__0_spec__0_spec__3_spec__10_spec__11_spec__12___redArg___closed__14_value) as *mut leanh::LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkRecOn_spec__0_spec__0_spec__3_spec__10_spec__11_spec__12___redArg___closed__15_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkRecOn_spec__0_spec__0_spec__3_spec__10_spec__11_spec__12___redArg___closed__15: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkRecOn_spec__0_spec__0_spec__3_spec__10_spec__11_spec__12___redArg___closed__16_value: leanh::LeanStringObject<10> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [96, 32, 40, 102, 114, 111, 109, 32, 96, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkRecOn_spec__0_spec__0_spec__3_spec__10_spec__11_spec__12___redArg___closed__16: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkRecOn_spec__0_spec__0_spec__3_spec__10_spec__11_spec__12___redArg___closed__16_value) as *mut leanh::LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkRecOn_spec__0_spec__0_spec__3_spec__10_spec__11_spec__12___redArg___closed__17_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkRecOn_spec__0_spec__0_spec__3_spec__10_spec__11_spec__12___redArg___closed__17: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkRecOn_spec__0_spec__0_spec__3_spec__10_spec__11_spec__12___redArg___closed__18_value: leanh::LeanStringObject<54> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 54, m_capacity: 54, m_length: 53, m_data: [96, 41, 32, 101, 120, 105, 115, 116, 115, 32, 98, 117, 116, 32, 119, 111, 117, 108, 100, 32, 110, 101, 101, 100, 32, 116, 111, 32, 98, 101, 32, 112, 117, 98, 108, 105, 99, 32, 116, 111, 32, 97, 99, 99, 101, 115, 115, 32, 104, 101, 114, 101, 46, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkRecOn_spec__0_spec__0_spec__3_spec__10_spec__11_spec__12___redArg___closed__18: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkRecOn_spec__0_spec__0_spec__3_spec__10_spec__11_spec__12___redArg___closed__18_value) as *mut leanh::LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkRecOn_spec__0_spec__0_spec__3_spec__10_spec__11_spec__12___redArg___closed__19_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkRecOn_spec__0_spec__0_spec__3_spec__10_spec__11_spec__12___redArg___closed__19: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkRecOn_spec__0_spec__0_spec__3___redArg___closed__0_value: leanh::LeanStringObject<19> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 19, m_capacity: 19, m_length: 18, m_data: [85, 110, 107, 110, 111, 119, 110, 32, 99, 111, 110, 115, 116, 97, 110, 116, 32, 96, 0]};
static mut l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkRecOn_spec__0_spec__0_spec__3___redArg___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkRecOn_spec__0_spec__0_spec__3___redArg___closed__0_value) as *mut leanh::LeanObject;
static mut l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkRecOn_spec__0_spec__0_spec__3___redArg___closed__1_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkRecOn_spec__0_spec__0_spec__3___redArg___closed__1: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkRecOn_spec__0_spec__0_spec__3___redArg___closed__2_value: leanh::LeanStringObject<2> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [96, 0]};
static mut l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkRecOn_spec__0_spec__0_spec__3___redArg___closed__2: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkRecOn_spec__0_spec__0_spec__3___redArg___closed__2_value) as *mut leanh::LeanObject;
static mut l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkRecOn_spec__0_spec__0_spec__3___redArg___closed__3_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkRecOn_spec__0_spec__0_spec__3___redArg___closed__3: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00mkRecOn_spec__5_spec__6___redArg___closed__0_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00mkRecOn_spec__5_spec__6___redArg___closed__0: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00mkRecOn_spec__5_spec__6___redArg___closed__1_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00mkRecOn_spec__5_spec__6___redArg___closed__1: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00mkRecOn_spec__5_spec__6___redArg___closed__2_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00mkRecOn_spec__5_spec__6___redArg___closed__2: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00mkRecOn_spec__5_spec__6___redArg___closed__3_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00mkRecOn_spec__5_spec__6___redArg___closed__3: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_mkRecOn___closed__0_value: leanh::LeanStringObject<15> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
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
static mut l_mkRecOn___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_mkRecOn___closed__0_value) as *mut leanh::LeanObject;
static mut l_mkRecOn___closed__1_once: leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_mkRecOn___closed__1: *mut leanh::LeanObject = core::ptr::null_mut();
pub unsafe fn l_Lean_mkDefinitionValInferringUnsafe___at___00mkRecOn_spec__3___redArg(
    mut v_name_883_: *mut leanh::LeanObject,
    mut v_levelParams_884_: *mut leanh::LeanObject,
    mut v_type_885_: *mut leanh::LeanObject,
    mut v_value_886_: *mut leanh::LeanObject,
    mut v_hints_887_: *mut leanh::LeanObject,
    mut v___y_888_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_890_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_892_: u8 = 0;
    let mut v___x_893_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_894_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_895_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_896_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_897_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_899_: u8 = 0;
    let mut v___x_900_: u8 = 0;
    let mut v___x_901_: u8 = 0;
    let mut v_env_902_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_903_: u8 = 0;
    let mut v___x_904_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_890_ = lean_st_ref_get(v___y_888_);
                v_env_902_ = leanh::lean_ctor_get(v___x_890_, 0);
                leanh::lean_inc_ref_n(v_env_902_, 2);
                leanh::lean_dec(v___x_890_);
                v___x_903_ = l_Lean_Environment_hasUnsafe(v_env_902_, v_type_885_);
                if v___x_903_ == 0 {
                    v___x_904_ = l_Lean_Environment_hasUnsafe(v_env_902_, v_value_886_);
                    v___y_899_ = v___x_904_;
                    state = 2;
                    continue;
                } else {
                    leanh::lean_dec_ref(v_env_902_);
                    v___y_899_ = v___x_903_;
                    state = 2;
                    continue;
                }
            }
            1 => {
                leanh::lean_inc(v_name_883_);
                v___x_893_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
                leanh::lean_ctor_set(v___x_893_, 0, v_name_883_);
                leanh::lean_ctor_set(v___x_893_, 1, v_levelParams_884_);
                leanh::lean_ctor_set(v___x_893_, 2, v_type_885_);
                v___x_894_ = leanh::lean_box(0);
                v___x_895_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_895_, 0, v_name_883_);
                leanh::lean_ctor_set(v___x_895_, 1, v___x_894_);
                v___x_896_ = leanh::lean_alloc_ctor(0, 4, (1) as u32);
                leanh::lean_ctor_set(v___x_896_, 0, v___x_893_);
                leanh::lean_ctor_set(v___x_896_, 1, v_value_886_);
                leanh::lean_ctor_set(v___x_896_, 2, v_hints_887_);
                leanh::lean_ctor_set(v___x_896_, 3, v___x_895_);
                leanh::lean_ctor_set_uint8(
                    v___x_896_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 4) as u32,
                    v___y_892_,
                );
                v___x_897_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_897_, 0, v___x_896_);
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
    mut v_name_905_: *mut leanh::LeanObject,
    mut v_levelParams_906_: *mut leanh::LeanObject,
    mut v_type_907_: *mut leanh::LeanObject,
    mut v_value_908_: *mut leanh::LeanObject,
    mut v_hints_909_: *mut leanh::LeanObject,
    mut v___y_910_: *mut leanh::LeanObject,
    mut v___y_911_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_912_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_912_ = l_Lean_mkDefinitionValInferringUnsafe___at___00mkRecOn_spec__3___redArg(
        v_name_905_,
        v_levelParams_906_,
        v_type_907_,
        v_value_908_,
        v_hints_909_,
        v___y_910_,
    );
    leanh::lean_dec(v___y_910_);
    return v_res_912_;
}
pub unsafe fn l_Lean_mkDefinitionValInferringUnsafe___at___00mkRecOn_spec__3(
    mut v_name_913_: *mut leanh::LeanObject,
    mut v_levelParams_914_: *mut leanh::LeanObject,
    mut v_type_915_: *mut leanh::LeanObject,
    mut v_value_916_: *mut leanh::LeanObject,
    mut v_hints_917_: *mut leanh::LeanObject,
    mut v___y_918_: *mut leanh::LeanObject,
    mut v___y_919_: *mut leanh::LeanObject,
    mut v___y_920_: *mut leanh::LeanObject,
    mut v___y_921_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_923_: *mut leanh::LeanObject = core::ptr::null_mut();
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
    mut v_name_924_: *mut leanh::LeanObject,
    mut v_levelParams_925_: *mut leanh::LeanObject,
    mut v_type_926_: *mut leanh::LeanObject,
    mut v_value_927_: *mut leanh::LeanObject,
    mut v_hints_928_: *mut leanh::LeanObject,
    mut v___y_929_: *mut leanh::LeanObject,
    mut v___y_930_: *mut leanh::LeanObject,
    mut v___y_931_: *mut leanh::LeanObject,
    mut v___y_932_: *mut leanh::LeanObject,
    mut v___y_933_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_934_: *mut leanh::LeanObject = core::ptr::null_mut();
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
    leanh::lean_dec(v___y_932_);
    leanh::lean_dec_ref(v___y_931_);
    leanh::lean_dec(v___y_930_);
    leanh::lean_dec_ref(v___y_929_);
    return v_res_934_;
}
pub unsafe fn l_Lean_Meta_forallTelescope___at___00mkRecOn_spec__4___redArg___lam__0(
    mut v_k_935_: *mut leanh::LeanObject,
    mut v_b_936_: *mut leanh::LeanObject,
    mut v_c_937_: *mut leanh::LeanObject,
    mut v___y_938_: *mut leanh::LeanObject,
    mut v___y_939_: *mut leanh::LeanObject,
    mut v___y_940_: *mut leanh::LeanObject,
    mut v___y_941_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_943_: *mut leanh::LeanObject = core::ptr::null_mut();
    leanh::lean_inc(v___y_941_);
    leanh::lean_inc_ref(v___y_940_);
    leanh::lean_inc(v___y_939_);
    leanh::lean_inc_ref(v___y_938_);
    v___x_943_ = leanh::lean_apply_7(
        v_k_935_,
        v_b_936_,
        v_c_937_,
        v___y_938_,
        v___y_939_,
        v___y_940_,
        v___y_941_,
        leanh::lean_box(0),
    );
    return v___x_943_;
}
pub unsafe fn l_Lean_Meta_forallTelescope___at___00mkRecOn_spec__4___redArg___lam__0___boxed(
    mut v_k_944_: *mut leanh::LeanObject,
    mut v_b_945_: *mut leanh::LeanObject,
    mut v_c_946_: *mut leanh::LeanObject,
    mut v___y_947_: *mut leanh::LeanObject,
    mut v___y_948_: *mut leanh::LeanObject,
    mut v___y_949_: *mut leanh::LeanObject,
    mut v___y_950_: *mut leanh::LeanObject,
    mut v___y_951_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_952_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_952_ = l_Lean_Meta_forallTelescope___at___00mkRecOn_spec__4___redArg___lam__0(
        v_k_944_, v_b_945_, v_c_946_, v___y_947_, v___y_948_, v___y_949_, v___y_950_,
    );
    leanh::lean_dec(v___y_950_);
    leanh::lean_dec_ref(v___y_949_);
    leanh::lean_dec(v___y_948_);
    leanh::lean_dec_ref(v___y_947_);
    return v_res_952_;
}
pub unsafe fn l_Lean_Meta_forallTelescope___at___00mkRecOn_spec__4___redArg(
    mut v_type_953_: *mut leanh::LeanObject,
    mut v_k_954_: *mut leanh::LeanObject,
    mut v_cleanupAnnotations_955_: u8,
    mut v___y_956_: *mut leanh::LeanObject,
    mut v___y_957_: *mut leanh::LeanObject,
    mut v___y_958_: *mut leanh::LeanObject,
    mut v___y_959_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_961_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_962_: u8 = 0;
    let mut v___x_963_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_964_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_965_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_967_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_968_: u8 = 0;
    let mut v___x_970_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_971_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_972_: u8 = 0;
    let mut v_a_973_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_975_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_976_: u8 = 0;
    let mut v___x_978_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_979_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_980_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___f_961_ = leanh::lean_alloc_closure(
                    l_Lean_Meta_forallTelescope___at___00mkRecOn_spec__4___redArg___lam__0___boxed
                        as *mut core::ffi::c_void,
                    8,
                    1,
                );
                leanh::lean_closure_set(v___f_961_, 0, v_k_954_);
                v___x_962_ = 0;
                v___x_963_ = leanh::lean_box(0);
                v___x_964_ = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAuxAux(
                    leanh::lean_box(0),
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
                if leanh::lean_obj_tag(v___x_964_) == 0 {
                    v_a_965_ = leanh::lean_ctor_get(v___x_964_, 0);
                    v_isSharedCheck_972_ = (!leanh::lean_is_exclusive(v___x_964_)) as u8;
                    if v_isSharedCheck_972_ == 0 {
                        v___x_967_ = v___x_964_;
                        v_isShared_968_ = v_isSharedCheck_972_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_965_);
                        leanh::lean_dec(v___x_964_);
                        v___x_967_ = leanh::lean_box(0);
                        v_isShared_968_ = v_isSharedCheck_972_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_973_ = leanh::lean_ctor_get(v___x_964_, 0);
                    v_isSharedCheck_980_ = (!leanh::lean_is_exclusive(v___x_964_)) as u8;
                    if v_isSharedCheck_980_ == 0 {
                        v___x_975_ = v___x_964_;
                        v_isShared_976_ = v_isSharedCheck_980_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_973_);
                        leanh::lean_dec(v___x_964_);
                        v___x_975_ = leanh::lean_box(0);
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
                    v_reuseFailAlloc_971_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_971_, 0, v_a_965_);
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
                    v_reuseFailAlloc_979_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_979_, 0, v_a_973_);
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
    mut v_type_981_: *mut leanh::LeanObject,
    mut v_k_982_: *mut leanh::LeanObject,
    mut v_cleanupAnnotations_983_: *mut leanh::LeanObject,
    mut v___y_984_: *mut leanh::LeanObject,
    mut v___y_985_: *mut leanh::LeanObject,
    mut v___y_986_: *mut leanh::LeanObject,
    mut v___y_987_: *mut leanh::LeanObject,
    mut v___y_988_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_cleanupAnnotations_boxed_989_: u8 = 0;
    let mut v_res_990_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_cleanupAnnotations_boxed_989_ = (leanh::lean_unbox(v_cleanupAnnotations_983_) as u8);
    v_res_990_ = l_Lean_Meta_forallTelescope___at___00mkRecOn_spec__4___redArg(
        v_type_981_,
        v_k_982_,
        v_cleanupAnnotations_boxed_989_,
        v___y_984_,
        v___y_985_,
        v___y_986_,
        v___y_987_,
    );
    leanh::lean_dec(v___y_987_);
    leanh::lean_dec_ref(v___y_986_);
    leanh::lean_dec(v___y_985_);
    leanh::lean_dec_ref(v___y_984_);
    return v_res_990_;
}
pub unsafe fn l_Lean_Meta_forallTelescope___at___00mkRecOn_spec__4(
    mut v_00_u03b1_991_: *mut leanh::LeanObject,
    mut v_type_992_: *mut leanh::LeanObject,
    mut v_k_993_: *mut leanh::LeanObject,
    mut v_cleanupAnnotations_994_: u8,
    mut v___y_995_: *mut leanh::LeanObject,
    mut v___y_996_: *mut leanh::LeanObject,
    mut v___y_997_: *mut leanh::LeanObject,
    mut v___y_998_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1000_: *mut leanh::LeanObject = core::ptr::null_mut();
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
    mut v_00_u03b1_1001_: *mut leanh::LeanObject,
    mut v_type_1002_: *mut leanh::LeanObject,
    mut v_k_1003_: *mut leanh::LeanObject,
    mut v_cleanupAnnotations_1004_: *mut leanh::LeanObject,
    mut v___y_1005_: *mut leanh::LeanObject,
    mut v___y_1006_: *mut leanh::LeanObject,
    mut v___y_1007_: *mut leanh::LeanObject,
    mut v___y_1008_: *mut leanh::LeanObject,
    mut v___y_1009_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_cleanupAnnotations_boxed_1010_: u8 = 0;
    let mut v_res_1011_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_cleanupAnnotations_boxed_1010_ = (leanh::lean_unbox(v_cleanupAnnotations_1004_) as u8);
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
    leanh::lean_dec(v___y_1008_);
    leanh::lean_dec_ref(v___y_1007_);
    leanh::lean_dec(v___y_1006_);
    leanh::lean_dec_ref(v___y_1005_);
    return v_res_1011_;
}
pub unsafe fn l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00mkRecOn_spec__2___redArg(
    mut v_a_1012_: *mut leanh::LeanObject,
    mut v_b_1013_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_array_1014_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_start_1015_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_stop_1016_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1018_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1019_: u8 = 0;
    let mut v___x_1020_: u8 = 0;
    let mut v___x_1021_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1022_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1024_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1025_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1026_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1028_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1029_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_array_1014_ = leanh::lean_ctor_get(v_a_1012_, 0);
                v_start_1015_ = leanh::lean_ctor_get(v_a_1012_, 1);
                v_stop_1016_ = leanh::lean_ctor_get(v_a_1012_, 2);
                v_isSharedCheck_1029_ = (!leanh::lean_is_exclusive(v_a_1012_)) as u8;
                if v_isSharedCheck_1029_ == 0 {
                    v___x_1018_ = v_a_1012_;
                    v_isShared_1019_ = v_isSharedCheck_1029_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_stop_1016_);
                    leanh::lean_inc(v_start_1015_);
                    leanh::lean_inc(v_array_1014_);
                    leanh::lean_dec(v_a_1012_);
                    v___x_1018_ = leanh::lean_box(0);
                    v_isShared_1019_ = v_isSharedCheck_1029_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_1020_ = lean_nat_dec_lt(v_start_1015_, v_stop_1016_);
                if v___x_1020_ == 0 {
                    leanh::lean_del_object(v___x_1018_);
                    leanh::lean_dec(v_stop_1016_);
                    leanh::lean_dec(v_start_1015_);
                    leanh::lean_dec_ref(v_array_1014_);
                    return v_b_1013_;
                } else {
                    v___x_1021_ = leanh::lean_unsigned_to_nat(1);
                    v___x_1022_ = lean_nat_add(v_start_1015_, v___x_1021_);
                    leanh::lean_inc_ref(v_array_1014_);
                    if v_isShared_1019_ == 0 {
                        leanh::lean_ctor_set(v___x_1018_, 1, v___x_1022_);
                        v___x_1024_ = v___x_1018_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_1028_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1028_, 0, v_array_1014_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1028_, 1, v___x_1022_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1028_, 2, v_stop_1016_);
                        v___x_1024_ = v_reuseFailAlloc_1028_;
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                v___x_1025_ = lean_array_fget(v_array_1014_, v_start_1015_);
                leanh::lean_dec(v_start_1015_);
                leanh::lean_dec_ref(v_array_1014_);
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
    mut v_a_1030_: *mut leanh::LeanObject,
    mut v_a_1031_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1032_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_1033_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_1034_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1036_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1037_: u8 = 0;
    let mut v___x_1038_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1040_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1042_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1043_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_a_1030_) == 0 {
                    v___x_1032_ = l_List_reverse___redArg(v_a_1031_);
                    return v___x_1032_;
                } else {
                    v_head_1033_ = leanh::lean_ctor_get(v_a_1030_, 0);
                    v_tail_1034_ = leanh::lean_ctor_get(v_a_1030_, 1);
                    v_isSharedCheck_1043_ = (!leanh::lean_is_exclusive(v_a_1030_)) as u8;
                    if v_isSharedCheck_1043_ == 0 {
                        v___x_1036_ = v_a_1030_;
                        v_isShared_1037_ = v_isSharedCheck_1043_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_tail_1034_);
                        leanh::lean_inc(v_head_1033_);
                        leanh::lean_dec(v_a_1030_);
                        v___x_1036_ = leanh::lean_box(0);
                        v_isShared_1037_ = v_isSharedCheck_1043_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_1038_ = l_Lean_Level_param___override(v_head_1033_);
                if v_isShared_1037_ == 0 {
                    leanh::lean_ctor_set(v___x_1036_, 1, v_a_1031_);
                    leanh::lean_ctor_set(v___x_1036_, 0, v___x_1038_);
                    v___x_1040_ = v___x_1036_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1042_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1042_, 0, v___x_1038_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1042_, 1, v_a_1031_);
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
    mut v_levelParams_1046_: *mut leanh::LeanObject,
    mut v_name_1047_: *mut leanh::LeanObject,
    mut v_numMinors_1048_: *mut leanh::LeanObject,
    mut v_numIndices_1049_: *mut leanh::LeanObject,
    mut v_n_1050_: *mut leanh::LeanObject,
    mut v_xs_1051_: *mut leanh::LeanObject,
    mut v_t_1052_: *mut leanh::LeanObject,
    mut v___y_1053_: *mut leanh::LeanObject,
    mut v___y_1054_: *mut leanh::LeanObject,
    mut v___y_1055_: *mut leanh::LeanObject,
    mut v___y_1056_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1058_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1059_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1060_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1061_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1062_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1063_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1064_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1065_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1066_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1067_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1068_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1069_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1070_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1071_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1072_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1073_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1074_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1075_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1076_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1077_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1078_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1079_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1080_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1081_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1082_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1083_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1084_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1085_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1086_: u8 = 0;
    let mut v___x_1087_: u8 = 0;
    let mut v___x_1088_: u8 = 0;
    let mut v___x_1089_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1090_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1091_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1092_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1093_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1094_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1095_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1096_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1098_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1099_: u8 = 0;
    let mut v___x_1101_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1102_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1103_: u8 = 0;
    let mut v_a_1104_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1106_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1107_: u8 = 0;
    let mut v___x_1109_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1110_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1111_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1058_ = leanh::lean_box(0);
                leanh::lean_inc(v_levelParams_1046_);
                v___x_1059_ =
                    l_List_mapTR_loop___at___00mkRecOn_spec__1(v_levelParams_1046_, v___x_1058_);
                v___x_1060_ = l_Lean_Expr_const___override(v_name_1047_, v___x_1059_);
                v___x_1061_ = l_Lean_mkAppN(v___x_1060_, v_xs_1051_);
                v___x_1062_ = lean_array_get_size(v_xs_1051_);
                v___x_1063_ = lean_nat_sub(v___x_1062_, v_numMinors_1048_);
                v___x_1064_ = lean_nat_sub(v___x_1063_, v_numIndices_1049_);
                leanh::lean_dec(v___x_1063_);
                v___x_1065_ = leanh::lean_unsigned_to_nat(1);
                v___x_1066_ = lean_nat_sub(v___x_1064_, v___x_1065_);
                leanh::lean_dec(v___x_1064_);
                v___x_1067_ = leanh::lean_unsigned_to_nat(0);
                leanh::lean_inc(v___x_1066_);
                leanh::lean_inc_ref_n(v_xs_1051_, 2);
                v___x_1068_ = l_Array_toSubarray___redArg(v_xs_1051_, v___x_1067_, v___x_1066_);
                v___x_1069_ = lean_nat_add(v___x_1066_, v_numMinors_1048_);
                v___x_1070_ = lean_nat_add(v___x_1069_, v___x_1065_);
                v___x_1071_ = lean_nat_add(v___x_1070_, v_numIndices_1049_);
                leanh::lean_dec(v___x_1070_);
                leanh::lean_inc(v___x_1069_);
                v___x_1072_ = l_Array_toSubarray___redArg(v_xs_1051_, v___x_1069_, v___x_1071_);
                v___x_1073_ = l_mkRecOn___lam__0___closed__0;
                v___x_1074_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00mkRecOn_spec__2___redArg(v___x_1068_, v___x_1073_);
                v___x_1075_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00mkRecOn_spec__2___redArg(v___x_1072_, v___x_1073_);
                v_a_1076_ = l_Array_append___redArg(v___x_1074_, v___x_1075_);
                leanh::lean_dec_ref(v___x_1075_);
                v___x_1077_ = lean_array_get_size(v_a_1076_);
                v___x_1078_ = l_Array_toSubarray___redArg(v_a_1076_, v___x_1067_, v___x_1077_);
                v___x_1079_ = l_Array_toSubarray___redArg(v_xs_1051_, v___x_1066_, v___x_1069_);
                v___x_1080_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00mkRecOn_spec__2___redArg(v___x_1078_, v___x_1073_);
                v___x_1081_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00mkRecOn_spec__2___redArg(v___x_1079_, v___x_1073_);
                v_a_1082_ = l_Array_append___redArg(v___x_1080_, v___x_1081_);
                leanh::lean_dec_ref(v___x_1081_);
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
                if leanh::lean_obj_tag(v___x_1089_) == 0 {
                    v_a_1090_ = leanh::lean_ctor_get(v___x_1089_, 0);
                    leanh::lean_inc(v_a_1090_);
                    leanh::lean_dec_ref_known(v___x_1089_, 1);
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
                    leanh::lean_dec_ref(v___x_1085_);
                    if leanh::lean_obj_tag(v___x_1091_) == 0 {
                        v_a_1092_ = leanh::lean_ctor_get(v___x_1091_, 0);
                        leanh::lean_inc(v_a_1092_);
                        leanh::lean_dec_ref_known(v___x_1091_, 1);
                        v___x_1093_ = l_Lean_mkRecOnName(v_n_1050_);
                        v___x_1094_ = leanh::lean_box(1);
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
                        leanh::lean_dec(v_a_1090_);
                        leanh::lean_dec(v_n_1050_);
                        leanh::lean_dec(v_levelParams_1046_);
                        v_a_1096_ = leanh::lean_ctor_get(v___x_1091_, 0);
                        v_isSharedCheck_1103_ =
                            (!leanh::lean_is_exclusive(v___x_1091_)) as u8;
                        if v_isSharedCheck_1103_ == 0 {
                            v___x_1098_ = v___x_1091_;
                            v_isShared_1099_ = v_isSharedCheck_1103_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_1096_);
                            leanh::lean_dec(v___x_1091_);
                            v___x_1098_ = leanh::lean_box(0);
                            v_isShared_1099_ = v_isSharedCheck_1103_;
                            state = 1;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_dec_ref(v___x_1085_);
                    leanh::lean_dec_ref(v___x_1061_);
                    leanh::lean_dec(v_n_1050_);
                    leanh::lean_dec(v_levelParams_1046_);
                    v_a_1104_ = leanh::lean_ctor_get(v___x_1089_, 0);
                    v_isSharedCheck_1111_ = (!leanh::lean_is_exclusive(v___x_1089_)) as u8;
                    if v_isSharedCheck_1111_ == 0 {
                        v___x_1106_ = v___x_1089_;
                        v_isShared_1107_ = v_isSharedCheck_1111_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_1104_);
                        leanh::lean_dec(v___x_1089_);
                        v___x_1106_ = leanh::lean_box(0);
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
                    v_reuseFailAlloc_1102_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1102_, 0, v_a_1096_);
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
                    v_reuseFailAlloc_1110_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1110_, 0, v_a_1104_);
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
    mut v_levelParams_1112_: *mut leanh::LeanObject,
    mut v_name_1113_: *mut leanh::LeanObject,
    mut v_numMinors_1114_: *mut leanh::LeanObject,
    mut v_numIndices_1115_: *mut leanh::LeanObject,
    mut v_n_1116_: *mut leanh::LeanObject,
    mut v_xs_1117_: *mut leanh::LeanObject,
    mut v_t_1118_: *mut leanh::LeanObject,
    mut v___y_1119_: *mut leanh::LeanObject,
    mut v___y_1120_: *mut leanh::LeanObject,
    mut v___y_1121_: *mut leanh::LeanObject,
    mut v___y_1122_: *mut leanh::LeanObject,
    mut v___y_1123_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1124_: *mut leanh::LeanObject = core::ptr::null_mut();
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
    leanh::lean_dec(v___y_1122_);
    leanh::lean_dec_ref(v___y_1121_);
    leanh::lean_dec(v___y_1120_);
    leanh::lean_dec_ref(v___y_1119_);
    leanh::lean_dec(v_numIndices_1115_);
    leanh::lean_dec(v_numMinors_1114_);
    return v_res_1124_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkRecOn_spec__0_spec__0_spec__3_spec__10_spec__11_spec__12___redArg___closed__0()
-> *mut leanh::LeanObject {
    let mut v___x_1125_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1125_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(
        leanh::lean_box(0),
        leanh::lean_box(0),
    );
    return v___x_1125_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkRecOn_spec__0_spec__0_spec__3_spec__10_spec__11_spec__12___redArg___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_1126_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1127_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1126_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkRecOn_spec__0_spec__0_spec__3_spec__10_spec__11_spec__12___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkRecOn_spec__0_spec__0_spec__3_spec__10_spec__11_spec__12___redArg___closed__0_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkRecOn_spec__0_spec__0_spec__3_spec__10_spec__11_spec__12___redArg___closed__0);
    v___x_1127_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_1127_, 0, v___x_1126_);
    return v___x_1127_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkRecOn_spec__0_spec__0_spec__3_spec__10_spec__11_spec__12___redArg___closed__2()
-> *mut leanh::LeanObject {
    let mut v___x_1128_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1129_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1130_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1128_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkRecOn_spec__0_spec__0_spec__3_spec__10_spec__11_spec__12___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkRecOn_spec__0_spec__0_spec__3_spec__10_spec__11_spec__12___redArg___closed__1_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkRecOn_spec__0_spec__0_spec__3_spec__10_spec__11_spec__12___redArg___closed__1);
    v___x_1129_ = leanh::lean_unsigned_to_nat(0);
    v___x_1130_ = leanh::lean_alloc_ctor(0, 10, (0) as u32);
    leanh::lean_ctor_set(v___x_1130_, 0, v___x_1129_);
    leanh::lean_ctor_set(v___x_1130_, 1, v___x_1129_);
    leanh::lean_ctor_set(v___x_1130_, 2, v___x_1129_);
    leanh::lean_ctor_set(v___x_1130_, 3, v___x_1129_);
    leanh::lean_ctor_set(v___x_1130_, 4, v___x_1128_);
    leanh::lean_ctor_set(v___x_1130_, 5, v___x_1128_);
    leanh::lean_ctor_set(v___x_1130_, 6, v___x_1128_);
    leanh::lean_ctor_set(v___x_1130_, 7, v___x_1128_);
    leanh::lean_ctor_set(v___x_1130_, 8, v___x_1128_);
    leanh::lean_ctor_set(v___x_1130_, 9, v___x_1128_);
    return v___x_1130_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkRecOn_spec__0_spec__0_spec__3_spec__10_spec__11_spec__12___redArg___closed__3()
-> *mut leanh::LeanObject {
    let mut v___x_1131_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1132_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1133_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1131_ = leanh::lean_unsigned_to_nat(32);
    v___x_1132_ = lean_mk_empty_array_with_capacity(v___x_1131_);
    v___x_1133_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_1133_, 0, v___x_1132_);
    return v___x_1133_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkRecOn_spec__0_spec__0_spec__3_spec__10_spec__11_spec__12___redArg___closed__4()
-> *mut leanh::LeanObject {
    let mut v___x_1134_: usize = 0;
    let mut v___x_1135_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1136_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1137_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1138_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1139_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1134_ = 5usize;
    v___x_1135_ = leanh::lean_unsigned_to_nat(0);
    v___x_1136_ = leanh::lean_unsigned_to_nat(32);
    v___x_1137_ = lean_mk_empty_array_with_capacity(v___x_1136_);
    v___x_1138_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkRecOn_spec__0_spec__0_spec__3_spec__10_spec__11_spec__12___redArg___closed__3), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkRecOn_spec__0_spec__0_spec__3_spec__10_spec__11_spec__12___redArg___closed__3_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkRecOn_spec__0_spec__0_spec__3_spec__10_spec__11_spec__12___redArg___closed__3);
    v___x_1139_ = leanh::lean_alloc_ctor(0, 4, (core::mem::size_of::<usize>() * 1) as u32);
    leanh::lean_ctor_set(v___x_1139_, 0, v___x_1138_);
    leanh::lean_ctor_set(v___x_1139_, 1, v___x_1137_);
    leanh::lean_ctor_set(v___x_1139_, 2, v___x_1135_);
    leanh::lean_ctor_set(v___x_1139_, 3, v___x_1135_);
    leanh::lean_ctor_set_usize(v___x_1139_, 4, v___x_1134_);
    return v___x_1139_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkRecOn_spec__0_spec__0_spec__3_spec__10_spec__11_spec__12___redArg___closed__5()
-> *mut leanh::LeanObject {
    let mut v___x_1140_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1141_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1142_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1143_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1140_ = leanh::lean_box(1);
    v___x_1141_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkRecOn_spec__0_spec__0_spec__3_spec__10_spec__11_spec__12___redArg___closed__4), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkRecOn_spec__0_spec__0_spec__3_spec__10_spec__11_spec__12___redArg___closed__4_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkRecOn_spec__0_spec__0_spec__3_spec__10_spec__11_spec__12___redArg___closed__4);
    v___x_1142_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkRecOn_spec__0_spec__0_spec__3_spec__10_spec__11_spec__12___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkRecOn_spec__0_spec__0_spec__3_spec__10_spec__11_spec__12___redArg___closed__1_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkRecOn_spec__0_spec__0_spec__3_spec__10_spec__11_spec__12___redArg___closed__1);
    v___x_1143_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_1143_, 0, v___x_1142_);
    leanh::lean_ctor_set(v___x_1143_, 1, v___x_1141_);
    leanh::lean_ctor_set(v___x_1143_, 2, v___x_1140_);
    return v___x_1143_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkRecOn_spec__0_spec__0_spec__3_spec__10_spec__11_spec__12___redArg___closed__7()
-> *mut leanh::LeanObject {
    let mut v___x_1145_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1146_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1145_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkRecOn_spec__0_spec__0_spec__3_spec__10_spec__11_spec__12___redArg___closed__6;
    v___x_1146_ = l_Lean_stringToMessageData(v___x_1145_);
    return v___x_1146_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkRecOn_spec__0_spec__0_spec__3_spec__10_spec__11_spec__12___redArg___closed__9()
-> *mut leanh::LeanObject {
    let mut v___x_1148_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1149_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1148_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkRecOn_spec__0_spec__0_spec__3_spec__10_spec__11_spec__12___redArg___closed__8;
    v___x_1149_ = l_Lean_stringToMessageData(v___x_1148_);
    return v___x_1149_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkRecOn_spec__0_spec__0_spec__3_spec__10_spec__11_spec__12___redArg___closed__11()
-> *mut leanh::LeanObject {
    let mut v___x_1151_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1152_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1151_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkRecOn_spec__0_spec__0_spec__3_spec__10_spec__11_spec__12___redArg___closed__10;
    v___x_1152_ = l_Lean_stringToMessageData(v___x_1151_);
    return v___x_1152_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkRecOn_spec__0_spec__0_spec__3_spec__10_spec__11_spec__12___redArg___closed__13()
-> *mut leanh::LeanObject {
    let mut v___x_1154_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1155_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1154_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkRecOn_spec__0_spec__0_spec__3_spec__10_spec__11_spec__12___redArg___closed__12;
    v___x_1155_ = l_Lean_stringToMessageData(v___x_1154_);
    return v___x_1155_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkRecOn_spec__0_spec__0_spec__3_spec__10_spec__11_spec__12___redArg___closed__15()
-> *mut leanh::LeanObject {
    let mut v___x_1157_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1158_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1157_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkRecOn_spec__0_spec__0_spec__3_spec__10_spec__11_spec__12___redArg___closed__14;
    v___x_1158_ = l_Lean_stringToMessageData(v___x_1157_);
    return v___x_1158_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkRecOn_spec__0_spec__0_spec__3_spec__10_spec__11_spec__12___redArg___closed__17()
-> *mut leanh::LeanObject {
    let mut v___x_1160_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1161_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1160_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkRecOn_spec__0_spec__0_spec__3_spec__10_spec__11_spec__12___redArg___closed__16;
    v___x_1161_ = l_Lean_stringToMessageData(v___x_1160_);
    return v___x_1161_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkRecOn_spec__0_spec__0_spec__3_spec__10_spec__11_spec__12___redArg___closed__19()
-> *mut leanh::LeanObject {
    let mut v___x_1163_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1164_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1163_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkRecOn_spec__0_spec__0_spec__3_spec__10_spec__11_spec__12___redArg___closed__18;
    v___x_1164_ = l_Lean_stringToMessageData(v___x_1163_);
    return v___x_1164_;
}
pub unsafe fn l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkRecOn_spec__0_spec__0_spec__3_spec__10_spec__11_spec__12___redArg(
    mut v_msg_1165_: *mut leanh::LeanObject,
    mut v_declHint_1166_: *mut leanh::LeanObject,
    mut v___y_1167_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1169_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_1170_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1171_: u8 = 0;
    let mut v_isExporting_1172_: u8 = 0;
    let mut v___x_1173_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1174_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1175_: u8 = 0;
    let mut v___x_1176_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1177_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1178_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1179_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1180_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1181_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_c_1182_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1183_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1184_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1185_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1186_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1187_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1188_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1189_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1190_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1191_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1193_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1194_: u8 = 0;
    let mut v___x_1195_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1196_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1197_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_mod_1198_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1199_: u8 = 0;
    let mut v___x_1200_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1201_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1202_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1203_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1204_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1205_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1206_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1207_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1208_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1209_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1211_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1212_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1213_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1214_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1215_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1216_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1217_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1218_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1219_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1220_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1221_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1222_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1224_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1225_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1226_: u8 = 0;
    let mut v___x_1227_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1169_ = lean_st_ref_get(v___y_1167_);
                v_env_1170_ = leanh::lean_ctor_get(v___x_1169_, 0);
                leanh::lean_inc_ref(v_env_1170_);
                leanh::lean_dec(v___x_1169_);
                v___x_1171_ = l_Lean_Name_isAnonymous(v_declHint_1166_);
                if v___x_1171_ == 0 {
                    v_isExporting_1172_ = leanh::lean_ctor_get_uint8(
                        v_env_1170_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 8) as u32,
                    );
                    if v_isExporting_1172_ == 0 {
                        leanh::lean_dec_ref(v_env_1170_);
                        leanh::lean_dec(v_declHint_1166_);
                        v___x_1173_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v___x_1173_, 0, v_msg_1165_);
                        return v___x_1173_;
                    } else {
                        leanh::lean_inc_ref(v_env_1170_);
                        v___x_1174_ = l_Lean_Environment_setExporting(v_env_1170_, v___x_1171_);
                        leanh::lean_inc(v_declHint_1166_);
                        leanh::lean_inc_ref(v___x_1174_);
                        v___x_1175_ = l_Lean_Environment_contains(
                            v___x_1174_,
                            v_declHint_1166_,
                            v_isExporting_1172_,
                        );
                        if v___x_1175_ == 0 {
                            leanh::lean_dec_ref(v___x_1174_);
                            leanh::lean_dec_ref(v_env_1170_);
                            leanh::lean_dec(v_declHint_1166_);
                            v___x_1176_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                            leanh::lean_ctor_set(v___x_1176_, 0, v_msg_1165_);
                            return v___x_1176_;
                        } else {
                            v___x_1177_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkRecOn_spec__0_spec__0_spec__3_spec__10_spec__11_spec__12___redArg___closed__2), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkRecOn_spec__0_spec__0_spec__3_spec__10_spec__11_spec__12___redArg___closed__2_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkRecOn_spec__0_spec__0_spec__3_spec__10_spec__11_spec__12___redArg___closed__2);
                            v___x_1178_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkRecOn_spec__0_spec__0_spec__3_spec__10_spec__11_spec__12___redArg___closed__5), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkRecOn_spec__0_spec__0_spec__3_spec__10_spec__11_spec__12___redArg___closed__5_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkRecOn_spec__0_spec__0_spec__3_spec__10_spec__11_spec__12___redArg___closed__5);
                            v___x_1179_ = l_Lean_Options_empty;
                            v___x_1180_ = leanh::lean_alloc_ctor(0, 4, (0) as u32);
                            leanh::lean_ctor_set(v___x_1180_, 0, v___x_1174_);
                            leanh::lean_ctor_set(v___x_1180_, 1, v___x_1177_);
                            leanh::lean_ctor_set(v___x_1180_, 2, v___x_1178_);
                            leanh::lean_ctor_set(v___x_1180_, 3, v___x_1179_);
                            leanh::lean_inc(v_declHint_1166_);
                            v___x_1181_ =
                                l_Lean_MessageData_ofConstName(v_declHint_1166_, v___x_1171_);
                            v_c_1182_ = leanh::lean_alloc_ctor(3, 2, (0) as u32);
                            leanh::lean_ctor_set(v_c_1182_, 0, v___x_1180_);
                            leanh::lean_ctor_set(v_c_1182_, 1, v___x_1181_);
                            v___x_1183_ = l_Lean_Environment_getModuleIdxFor_x3f(
                                v_env_1170_,
                                v_declHint_1166_,
                            );
                            if leanh::lean_obj_tag(v___x_1183_) == 0 {
                                leanh::lean_dec_ref(v_env_1170_);
                                leanh::lean_dec(v_declHint_1166_);
                                v___x_1184_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkRecOn_spec__0_spec__0_spec__3_spec__10_spec__11_spec__12___redArg___closed__7), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkRecOn_spec__0_spec__0_spec__3_spec__10_spec__11_spec__12___redArg___closed__7_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkRecOn_spec__0_spec__0_spec__3_spec__10_spec__11_spec__12___redArg___closed__7);
                                v___x_1185_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                                leanh::lean_ctor_set(v___x_1185_, 0, v___x_1184_);
                                leanh::lean_ctor_set(v___x_1185_, 1, v_c_1182_);
                                v___x_1186_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkRecOn_spec__0_spec__0_spec__3_spec__10_spec__11_spec__12___redArg___closed__9), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkRecOn_spec__0_spec__0_spec__3_spec__10_spec__11_spec__12___redArg___closed__9_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkRecOn_spec__0_spec__0_spec__3_spec__10_spec__11_spec__12___redArg___closed__9);
                                v___x_1187_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                                leanh::lean_ctor_set(v___x_1187_, 0, v___x_1185_);
                                leanh::lean_ctor_set(v___x_1187_, 1, v___x_1186_);
                                v___x_1188_ = l_Lean_MessageData_note(v___x_1187_);
                                v___x_1189_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                                leanh::lean_ctor_set(v___x_1189_, 0, v_msg_1165_);
                                leanh::lean_ctor_set(v___x_1189_, 1, v___x_1188_);
                                v___x_1190_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                                leanh::lean_ctor_set(v___x_1190_, 0, v___x_1189_);
                                return v___x_1190_;
                            } else {
                                v_val_1191_ = leanh::lean_ctor_get(v___x_1183_, 0);
                                v_isSharedCheck_1226_ =
                                    (!leanh::lean_is_exclusive(v___x_1183_)) as u8;
                                if v_isSharedCheck_1226_ == 0 {
                                    v___x_1193_ = v___x_1183_;
                                    v_isShared_1194_ = v_isSharedCheck_1226_;
                                    state = 1;
                                    continue;
                                } else {
                                    leanh::lean_inc(v_val_1191_);
                                    leanh::lean_dec(v___x_1183_);
                                    v___x_1193_ = leanh::lean_box(0);
                                    v_isShared_1194_ = v_isSharedCheck_1226_;
                                    state = 1;
                                    continue;
                                }
                            }
                        }
                    }
                } else {
                    leanh::lean_dec_ref(v_env_1170_);
                    leanh::lean_dec(v_declHint_1166_);
                    v___x_1227_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_1227_, 0, v_msg_1165_);
                    return v___x_1227_;
                }
            }
            1 => {
                v___x_1195_ = leanh::lean_box(0);
                v___x_1196_ = l_Lean_Environment_header(v_env_1170_);
                leanh::lean_dec_ref(v_env_1170_);
                v___x_1197_ = l_Lean_EnvironmentHeader_moduleNames(v___x_1196_);
                v_mod_1198_ = lean_array_get(v___x_1195_, v___x_1197_, v_val_1191_);
                leanh::lean_dec(v_val_1191_);
                leanh::lean_dec_ref(v___x_1197_);
                v___x_1199_ = l_Lean_isPrivateName(v_declHint_1166_);
                leanh::lean_dec(v_declHint_1166_);
                if v___x_1199_ == 0 {
                    v___x_1200_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkRecOn_spec__0_spec__0_spec__3_spec__10_spec__11_spec__12___redArg___closed__11), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkRecOn_spec__0_spec__0_spec__3_spec__10_spec__11_spec__12___redArg___closed__11_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkRecOn_spec__0_spec__0_spec__3_spec__10_spec__11_spec__12___redArg___closed__11);
                    v___x_1201_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_1201_, 0, v___x_1200_);
                    leanh::lean_ctor_set(v___x_1201_, 1, v_c_1182_);
                    v___x_1202_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkRecOn_spec__0_spec__0_spec__3_spec__10_spec__11_spec__12___redArg___closed__13), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkRecOn_spec__0_spec__0_spec__3_spec__10_spec__11_spec__12___redArg___closed__13_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkRecOn_spec__0_spec__0_spec__3_spec__10_spec__11_spec__12___redArg___closed__13);
                    v___x_1203_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_1203_, 0, v___x_1201_);
                    leanh::lean_ctor_set(v___x_1203_, 1, v___x_1202_);
                    v___x_1204_ = l_Lean_MessageData_ofName(v_mod_1198_);
                    v___x_1205_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_1205_, 0, v___x_1203_);
                    leanh::lean_ctor_set(v___x_1205_, 1, v___x_1204_);
                    v___x_1206_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkRecOn_spec__0_spec__0_spec__3_spec__10_spec__11_spec__12___redArg___closed__15), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkRecOn_spec__0_spec__0_spec__3_spec__10_spec__11_spec__12___redArg___closed__15_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkRecOn_spec__0_spec__0_spec__3_spec__10_spec__11_spec__12___redArg___closed__15);
                    v___x_1207_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_1207_, 0, v___x_1205_);
                    leanh::lean_ctor_set(v___x_1207_, 1, v___x_1206_);
                    v___x_1208_ = l_Lean_MessageData_note(v___x_1207_);
                    v___x_1209_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_1209_, 0, v_msg_1165_);
                    leanh::lean_ctor_set(v___x_1209_, 1, v___x_1208_);
                    if v_isShared_1194_ == 0 {
                        leanh::lean_ctor_set_tag(v___x_1193_, 0);
                        leanh::lean_ctor_set(v___x_1193_, 0, v___x_1209_);
                        v___x_1211_ = v___x_1193_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_1212_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1212_, 0, v___x_1209_);
                        v___x_1211_ = v_reuseFailAlloc_1212_;
                        state = 2;
                        continue;
                    }
                } else {
                    v___x_1213_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkRecOn_spec__0_spec__0_spec__3_spec__10_spec__11_spec__12___redArg___closed__7), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkRecOn_spec__0_spec__0_spec__3_spec__10_spec__11_spec__12___redArg___closed__7_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkRecOn_spec__0_spec__0_spec__3_spec__10_spec__11_spec__12___redArg___closed__7);
                    v___x_1214_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_1214_, 0, v___x_1213_);
                    leanh::lean_ctor_set(v___x_1214_, 1, v_c_1182_);
                    v___x_1215_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkRecOn_spec__0_spec__0_spec__3_spec__10_spec__11_spec__12___redArg___closed__17), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkRecOn_spec__0_spec__0_spec__3_spec__10_spec__11_spec__12___redArg___closed__17_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkRecOn_spec__0_spec__0_spec__3_spec__10_spec__11_spec__12___redArg___closed__17);
                    v___x_1216_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_1216_, 0, v___x_1214_);
                    leanh::lean_ctor_set(v___x_1216_, 1, v___x_1215_);
                    v___x_1217_ = l_Lean_MessageData_ofName(v_mod_1198_);
                    v___x_1218_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_1218_, 0, v___x_1216_);
                    leanh::lean_ctor_set(v___x_1218_, 1, v___x_1217_);
                    v___x_1219_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkRecOn_spec__0_spec__0_spec__3_spec__10_spec__11_spec__12___redArg___closed__19), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkRecOn_spec__0_spec__0_spec__3_spec__10_spec__11_spec__12___redArg___closed__19_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkRecOn_spec__0_spec__0_spec__3_spec__10_spec__11_spec__12___redArg___closed__19);
                    v___x_1220_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_1220_, 0, v___x_1218_);
                    leanh::lean_ctor_set(v___x_1220_, 1, v___x_1219_);
                    v___x_1221_ = l_Lean_MessageData_note(v___x_1220_);
                    v___x_1222_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_1222_, 0, v_msg_1165_);
                    leanh::lean_ctor_set(v___x_1222_, 1, v___x_1221_);
                    if v_isShared_1194_ == 0 {
                        leanh::lean_ctor_set_tag(v___x_1193_, 0);
                        leanh::lean_ctor_set(v___x_1193_, 0, v___x_1222_);
                        v___x_1224_ = v___x_1193_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_1225_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1225_, 0, v___x_1222_);
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
    mut v_msg_1228_: *mut leanh::LeanObject,
    mut v_declHint_1229_: *mut leanh::LeanObject,
    mut v___y_1230_: *mut leanh::LeanObject,
    mut v___y_1231_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1232_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1232_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkRecOn_spec__0_spec__0_spec__3_spec__10_spec__11_spec__12___redArg(v_msg_1228_, v_declHint_1229_, v___y_1230_);
    leanh::lean_dec(v___y_1230_);
    return v_res_1232_;
}
pub unsafe fn l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkRecOn_spec__0_spec__0_spec__3_spec__10_spec__11(
    mut v_msg_1233_: *mut leanh::LeanObject,
    mut v_declHint_1234_: *mut leanh::LeanObject,
    mut v___y_1235_: *mut leanh::LeanObject,
    mut v___y_1236_: *mut leanh::LeanObject,
    mut v___y_1237_: *mut leanh::LeanObject,
    mut v___y_1238_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1240_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1241_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1243_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1244_: u8 = 0;
    let mut v___x_1245_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1246_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1248_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1249_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1250_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1240_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkRecOn_spec__0_spec__0_spec__3_spec__10_spec__11_spec__12___redArg(v_msg_1233_, v_declHint_1234_, v___y_1238_);
                v_a_1241_ = leanh::lean_ctor_get(v___x_1240_, 0);
                v_isSharedCheck_1250_ = (!leanh::lean_is_exclusive(v___x_1240_)) as u8;
                if v_isSharedCheck_1250_ == 0 {
                    v___x_1243_ = v___x_1240_;
                    v_isShared_1244_ = v_isSharedCheck_1250_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_a_1241_);
                    leanh::lean_dec(v___x_1240_);
                    v___x_1243_ = leanh::lean_box(0);
                    v_isShared_1244_ = v_isSharedCheck_1250_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_1245_ = l_Lean_unknownIdentifierMessageTag;
                v___x_1246_ = leanh::lean_alloc_ctor(8, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_1246_, 0, v___x_1245_);
                leanh::lean_ctor_set(v___x_1246_, 1, v_a_1241_);
                if v_isShared_1244_ == 0 {
                    leanh::lean_ctor_set(v___x_1243_, 0, v___x_1246_);
                    v___x_1248_ = v___x_1243_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1249_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1249_, 0, v___x_1246_);
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
    mut v_msg_1251_: *mut leanh::LeanObject,
    mut v_declHint_1252_: *mut leanh::LeanObject,
    mut v___y_1253_: *mut leanh::LeanObject,
    mut v___y_1254_: *mut leanh::LeanObject,
    mut v___y_1255_: *mut leanh::LeanObject,
    mut v___y_1256_: *mut leanh::LeanObject,
    mut v___y_1257_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1258_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1258_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkRecOn_spec__0_spec__0_spec__3_spec__10_spec__11(v_msg_1251_, v_declHint_1252_, v___y_1253_, v___y_1254_, v___y_1255_, v___y_1256_);
    leanh::lean_dec(v___y_1256_);
    leanh::lean_dec_ref(v___y_1255_);
    leanh::lean_dec(v___y_1254_);
    leanh::lean_dec_ref(v___y_1253_);
    return v_res_1258_;
}
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_throwError___at___00mkRecOn_spec__6_spec__8(
    mut v_msgData_1259_: *mut leanh::LeanObject,
    mut v___y_1260_: *mut leanh::LeanObject,
    mut v___y_1261_: *mut leanh::LeanObject,
    mut v___y_1262_: *mut leanh::LeanObject,
    mut v___y_1263_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1265_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_1266_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1267_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_1268_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_lctx_1269_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_1270_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1271_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1272_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1273_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1265_ = lean_st_ref_get(v___y_1263_);
    v_env_1266_ = leanh::lean_ctor_get(v___x_1265_, 0);
    leanh::lean_inc_ref(v_env_1266_);
    leanh::lean_dec(v___x_1265_);
    v___x_1267_ = lean_st_ref_get(v___y_1261_);
    v_mctx_1268_ = leanh::lean_ctor_get(v___x_1267_, 0);
    leanh::lean_inc_ref(v_mctx_1268_);
    leanh::lean_dec(v___x_1267_);
    v_lctx_1269_ = leanh::lean_ctor_get(v___y_1260_, 2);
    v_options_1270_ = leanh::lean_ctor_get(v___y_1262_, 2);
    leanh::lean_inc_ref(v_options_1270_);
    leanh::lean_inc_ref(v_lctx_1269_);
    v___x_1271_ = leanh::lean_alloc_ctor(0, 4, (0) as u32);
    leanh::lean_ctor_set(v___x_1271_, 0, v_env_1266_);
    leanh::lean_ctor_set(v___x_1271_, 1, v_mctx_1268_);
    leanh::lean_ctor_set(v___x_1271_, 2, v_lctx_1269_);
    leanh::lean_ctor_set(v___x_1271_, 3, v_options_1270_);
    v___x_1272_ = leanh::lean_alloc_ctor(3, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1272_, 0, v___x_1271_);
    leanh::lean_ctor_set(v___x_1272_, 1, v_msgData_1259_);
    v___x_1273_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_1273_, 0, v___x_1272_);
    return v___x_1273_;
}
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_throwError___at___00mkRecOn_spec__6_spec__8___boxed(
    mut v_msgData_1274_: *mut leanh::LeanObject,
    mut v___y_1275_: *mut leanh::LeanObject,
    mut v___y_1276_: *mut leanh::LeanObject,
    mut v___y_1277_: *mut leanh::LeanObject,
    mut v___y_1278_: *mut leanh::LeanObject,
    mut v___y_1279_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1280_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1280_ =
        l_Lean_addMessageContextFull___at___00Lean_throwError___at___00mkRecOn_spec__6_spec__8(
            v_msgData_1274_,
            v___y_1275_,
            v___y_1276_,
            v___y_1277_,
            v___y_1278_,
        );
    leanh::lean_dec(v___y_1278_);
    leanh::lean_dec_ref(v___y_1277_);
    leanh::lean_dec(v___y_1276_);
    leanh::lean_dec_ref(v___y_1275_);
    return v_res_1280_;
}
pub unsafe fn l_Lean_throwError___at___00mkRecOn_spec__6___redArg(
    mut v_msg_1281_: *mut leanh::LeanObject,
    mut v___y_1282_: *mut leanh::LeanObject,
    mut v___y_1283_: *mut leanh::LeanObject,
    mut v___y_1284_: *mut leanh::LeanObject,
    mut v___y_1285_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_ref_1287_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1288_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1289_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1291_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1292_: u8 = 0;
    let mut v___x_1293_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1295_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1296_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1297_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ref_1287_ = leanh::lean_ctor_get(v___y_1284_, 5);
                v___x_1288_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00mkRecOn_spec__6_spec__8(v_msg_1281_, v___y_1282_, v___y_1283_, v___y_1284_, v___y_1285_);
                v_a_1289_ = leanh::lean_ctor_get(v___x_1288_, 0);
                v_isSharedCheck_1297_ = (!leanh::lean_is_exclusive(v___x_1288_)) as u8;
                if v_isSharedCheck_1297_ == 0 {
                    v___x_1291_ = v___x_1288_;
                    v_isShared_1292_ = v_isSharedCheck_1297_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_a_1289_);
                    leanh::lean_dec(v___x_1288_);
                    v___x_1291_ = leanh::lean_box(0);
                    v_isShared_1292_ = v_isSharedCheck_1297_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                leanh::lean_inc(v_ref_1287_);
                v___x_1293_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_1293_, 0, v_ref_1287_);
                leanh::lean_ctor_set(v___x_1293_, 1, v_a_1289_);
                if v_isShared_1292_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_1291_, 1);
                    leanh::lean_ctor_set(v___x_1291_, 0, v___x_1293_);
                    v___x_1295_ = v___x_1291_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1296_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1296_, 0, v___x_1293_);
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
    mut v_msg_1298_: *mut leanh::LeanObject,
    mut v___y_1299_: *mut leanh::LeanObject,
    mut v___y_1300_: *mut leanh::LeanObject,
    mut v___y_1301_: *mut leanh::LeanObject,
    mut v___y_1302_: *mut leanh::LeanObject,
    mut v___y_1303_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1304_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1304_ = l_Lean_throwError___at___00mkRecOn_spec__6___redArg(
        v_msg_1298_,
        v___y_1299_,
        v___y_1300_,
        v___y_1301_,
        v___y_1302_,
    );
    leanh::lean_dec(v___y_1302_);
    leanh::lean_dec_ref(v___y_1301_);
    leanh::lean_dec(v___y_1300_);
    leanh::lean_dec_ref(v___y_1299_);
    return v_res_1304_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkRecOn_spec__0_spec__0_spec__3_spec__10_spec__12___redArg(
    mut v_ref_1305_: *mut leanh::LeanObject,
    mut v_msg_1306_: *mut leanh::LeanObject,
    mut v___y_1307_: *mut leanh::LeanObject,
    mut v___y_1308_: *mut leanh::LeanObject,
    mut v___y_1309_: *mut leanh::LeanObject,
    mut v___y_1310_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_fileName_1312_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fileMap_1313_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_1314_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_currRecDepth_1315_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_maxRecDepth_1316_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_1317_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_currNamespace_1318_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_openDecls_1319_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_initHeartbeats_1320_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_maxHeartbeats_1321_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_quotContext_1322_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_currMacroScope_1323_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_diag_1324_: u8 = 0;
    let mut v_cancelTk_x3f_1325_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_suppressElabErrors_1326_: u8 = 0;
    let mut v_inheritedTraceOptions_1327_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_1328_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1329_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1330_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_fileName_1312_ = leanh::lean_ctor_get(v___y_1309_, 0);
    v_fileMap_1313_ = leanh::lean_ctor_get(v___y_1309_, 1);
    v_options_1314_ = leanh::lean_ctor_get(v___y_1309_, 2);
    v_currRecDepth_1315_ = leanh::lean_ctor_get(v___y_1309_, 3);
    v_maxRecDepth_1316_ = leanh::lean_ctor_get(v___y_1309_, 4);
    v_ref_1317_ = leanh::lean_ctor_get(v___y_1309_, 5);
    v_currNamespace_1318_ = leanh::lean_ctor_get(v___y_1309_, 6);
    v_openDecls_1319_ = leanh::lean_ctor_get(v___y_1309_, 7);
    v_initHeartbeats_1320_ = leanh::lean_ctor_get(v___y_1309_, 8);
    v_maxHeartbeats_1321_ = leanh::lean_ctor_get(v___y_1309_, 9);
    v_quotContext_1322_ = leanh::lean_ctor_get(v___y_1309_, 10);
    v_currMacroScope_1323_ = leanh::lean_ctor_get(v___y_1309_, 11);
    v_diag_1324_ = leanh::lean_ctor_get_uint8(
        v___y_1309_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 14) as u32,
    );
    v_cancelTk_x3f_1325_ = leanh::lean_ctor_get(v___y_1309_, 12);
    v_suppressElabErrors_1326_ = leanh::lean_ctor_get_uint8(
        v___y_1309_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 14 + 1) as u32,
    );
    v_inheritedTraceOptions_1327_ = leanh::lean_ctor_get(v___y_1309_, 13);
    v_ref_1328_ = l_Lean_replaceRef(v_ref_1305_, v_ref_1317_);
    leanh::lean_inc_ref(v_inheritedTraceOptions_1327_);
    leanh::lean_inc(v_cancelTk_x3f_1325_);
    leanh::lean_inc(v_currMacroScope_1323_);
    leanh::lean_inc(v_quotContext_1322_);
    leanh::lean_inc(v_maxHeartbeats_1321_);
    leanh::lean_inc(v_initHeartbeats_1320_);
    leanh::lean_inc(v_openDecls_1319_);
    leanh::lean_inc(v_currNamespace_1318_);
    leanh::lean_inc(v_maxRecDepth_1316_);
    leanh::lean_inc(v_currRecDepth_1315_);
    leanh::lean_inc_ref(v_options_1314_);
    leanh::lean_inc_ref(v_fileMap_1313_);
    leanh::lean_inc_ref(v_fileName_1312_);
    v___x_1329_ = leanh::lean_alloc_ctor(0, 14, (2) as u32);
    leanh::lean_ctor_set(v___x_1329_, 0, v_fileName_1312_);
    leanh::lean_ctor_set(v___x_1329_, 1, v_fileMap_1313_);
    leanh::lean_ctor_set(v___x_1329_, 2, v_options_1314_);
    leanh::lean_ctor_set(v___x_1329_, 3, v_currRecDepth_1315_);
    leanh::lean_ctor_set(v___x_1329_, 4, v_maxRecDepth_1316_);
    leanh::lean_ctor_set(v___x_1329_, 5, v_ref_1328_);
    leanh::lean_ctor_set(v___x_1329_, 6, v_currNamespace_1318_);
    leanh::lean_ctor_set(v___x_1329_, 7, v_openDecls_1319_);
    leanh::lean_ctor_set(v___x_1329_, 8, v_initHeartbeats_1320_);
    leanh::lean_ctor_set(v___x_1329_, 9, v_maxHeartbeats_1321_);
    leanh::lean_ctor_set(v___x_1329_, 10, v_quotContext_1322_);
    leanh::lean_ctor_set(v___x_1329_, 11, v_currMacroScope_1323_);
    leanh::lean_ctor_set(v___x_1329_, 12, v_cancelTk_x3f_1325_);
    leanh::lean_ctor_set(v___x_1329_, 13, v_inheritedTraceOptions_1327_);
    leanh::lean_ctor_set_uint8(
        v___x_1329_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 14) as u32,
        v_diag_1324_,
    );
    leanh::lean_ctor_set_uint8(
        v___x_1329_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 14 + 1) as u32,
        v_suppressElabErrors_1326_,
    );
    v___x_1330_ = l_Lean_throwError___at___00mkRecOn_spec__6___redArg(
        v_msg_1306_,
        v___y_1307_,
        v___y_1308_,
        v___x_1329_,
        v___y_1310_,
    );
    leanh::lean_dec_ref_known(v___x_1329_, 14);
    return v___x_1330_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkRecOn_spec__0_spec__0_spec__3_spec__10_spec__12___redArg___boxed(
    mut v_ref_1331_: *mut leanh::LeanObject,
    mut v_msg_1332_: *mut leanh::LeanObject,
    mut v___y_1333_: *mut leanh::LeanObject,
    mut v___y_1334_: *mut leanh::LeanObject,
    mut v___y_1335_: *mut leanh::LeanObject,
    mut v___y_1336_: *mut leanh::LeanObject,
    mut v___y_1337_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1338_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1338_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkRecOn_spec__0_spec__0_spec__3_spec__10_spec__12___redArg(v_ref_1331_, v_msg_1332_, v___y_1333_, v___y_1334_, v___y_1335_, v___y_1336_);
    leanh::lean_dec(v___y_1336_);
    leanh::lean_dec_ref(v___y_1335_);
    leanh::lean_dec(v___y_1334_);
    leanh::lean_dec_ref(v___y_1333_);
    leanh::lean_dec(v_ref_1331_);
    return v_res_1338_;
}
pub unsafe fn l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkRecOn_spec__0_spec__0_spec__3_spec__10___redArg(
    mut v_ref_1339_: *mut leanh::LeanObject,
    mut v_msg_1340_: *mut leanh::LeanObject,
    mut v_declHint_1341_: *mut leanh::LeanObject,
    mut v___y_1342_: *mut leanh::LeanObject,
    mut v___y_1343_: *mut leanh::LeanObject,
    mut v___y_1344_: *mut leanh::LeanObject,
    mut v___y_1345_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1347_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1348_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1349_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1347_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkRecOn_spec__0_spec__0_spec__3_spec__10_spec__11(v_msg_1340_, v_declHint_1341_, v___y_1342_, v___y_1343_, v___y_1344_, v___y_1345_);
    v_a_1348_ = leanh::lean_ctor_get(v___x_1347_, 0);
    leanh::lean_inc(v_a_1348_);
    leanh::lean_dec_ref(v___x_1347_);
    v___x_1349_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkRecOn_spec__0_spec__0_spec__3_spec__10_spec__12___redArg(v_ref_1339_, v_a_1348_, v___y_1342_, v___y_1343_, v___y_1344_, v___y_1345_);
    return v___x_1349_;
}
pub unsafe fn l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkRecOn_spec__0_spec__0_spec__3_spec__10___redArg___boxed(
    mut v_ref_1350_: *mut leanh::LeanObject,
    mut v_msg_1351_: *mut leanh::LeanObject,
    mut v_declHint_1352_: *mut leanh::LeanObject,
    mut v___y_1353_: *mut leanh::LeanObject,
    mut v___y_1354_: *mut leanh::LeanObject,
    mut v___y_1355_: *mut leanh::LeanObject,
    mut v___y_1356_: *mut leanh::LeanObject,
    mut v___y_1357_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1358_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1358_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkRecOn_spec__0_spec__0_spec__3_spec__10___redArg(v_ref_1350_, v_msg_1351_, v_declHint_1352_, v___y_1353_, v___y_1354_, v___y_1355_, v___y_1356_);
    leanh::lean_dec(v___y_1356_);
    leanh::lean_dec_ref(v___y_1355_);
    leanh::lean_dec(v___y_1354_);
    leanh::lean_dec_ref(v___y_1353_);
    leanh::lean_dec(v_ref_1350_);
    return v_res_1358_;
}
pub unsafe fn _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkRecOn_spec__0_spec__0_spec__3___redArg___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_1360_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1361_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1360_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkRecOn_spec__0_spec__0_spec__3___redArg___closed__0;
    v___x_1361_ = l_Lean_stringToMessageData(v___x_1360_);
    return v___x_1361_;
}
pub unsafe fn _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkRecOn_spec__0_spec__0_spec__3___redArg___closed__3()
-> *mut leanh::LeanObject {
    let mut v___x_1363_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1364_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1363_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkRecOn_spec__0_spec__0_spec__3___redArg___closed__2;
    v___x_1364_ = l_Lean_stringToMessageData(v___x_1363_);
    return v___x_1364_;
}
pub unsafe fn l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkRecOn_spec__0_spec__0_spec__3___redArg(
    mut v_ref_1365_: *mut leanh::LeanObject,
    mut v_constName_1366_: *mut leanh::LeanObject,
    mut v___y_1367_: *mut leanh::LeanObject,
    mut v___y_1368_: *mut leanh::LeanObject,
    mut v___y_1369_: *mut leanh::LeanObject,
    mut v___y_1370_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1372_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1373_: u8 = 0;
    let mut v___x_1374_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1375_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1376_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1377_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1378_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1372_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkRecOn_spec__0_spec__0_spec__3___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkRecOn_spec__0_spec__0_spec__3___redArg___closed__1_once), _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkRecOn_spec__0_spec__0_spec__3___redArg___closed__1);
    v___x_1373_ = 0;
    leanh::lean_inc(v_constName_1366_);
    v___x_1374_ = l_Lean_MessageData_ofConstName(v_constName_1366_, v___x_1373_);
    v___x_1375_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1375_, 0, v___x_1372_);
    leanh::lean_ctor_set(v___x_1375_, 1, v___x_1374_);
    v___x_1376_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkRecOn_spec__0_spec__0_spec__3___redArg___closed__3), core::ptr::addr_of_mut!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkRecOn_spec__0_spec__0_spec__3___redArg___closed__3_once), _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkRecOn_spec__0_spec__0_spec__3___redArg___closed__3);
    v___x_1377_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1377_, 0, v___x_1375_);
    leanh::lean_ctor_set(v___x_1377_, 1, v___x_1376_);
    v___x_1378_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkRecOn_spec__0_spec__0_spec__3_spec__10___redArg(v_ref_1365_, v___x_1377_, v_constName_1366_, v___y_1367_, v___y_1368_, v___y_1369_, v___y_1370_);
    return v___x_1378_;
}
pub unsafe fn l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkRecOn_spec__0_spec__0_spec__3___redArg___boxed(
    mut v_ref_1379_: *mut leanh::LeanObject,
    mut v_constName_1380_: *mut leanh::LeanObject,
    mut v___y_1381_: *mut leanh::LeanObject,
    mut v___y_1382_: *mut leanh::LeanObject,
    mut v___y_1383_: *mut leanh::LeanObject,
    mut v___y_1384_: *mut leanh::LeanObject,
    mut v___y_1385_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1386_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1386_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkRecOn_spec__0_spec__0_spec__3___redArg(v_ref_1379_, v_constName_1380_, v___y_1381_, v___y_1382_, v___y_1383_, v___y_1384_);
    leanh::lean_dec(v___y_1384_);
    leanh::lean_dec_ref(v___y_1383_);
    leanh::lean_dec(v___y_1382_);
    leanh::lean_dec_ref(v___y_1381_);
    leanh::lean_dec(v_ref_1379_);
    return v_res_1386_;
}
pub unsafe fn l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkRecOn_spec__0_spec__0___redArg(
    mut v_constName_1387_: *mut leanh::LeanObject,
    mut v___y_1388_: *mut leanh::LeanObject,
    mut v___y_1389_: *mut leanh::LeanObject,
    mut v___y_1390_: *mut leanh::LeanObject,
    mut v___y_1391_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_ref_1393_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1394_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_ref_1393_ = leanh::lean_ctor_get(v___y_1390_, 5);
    v___x_1394_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkRecOn_spec__0_spec__0_spec__3___redArg(v_ref_1393_, v_constName_1387_, v___y_1388_, v___y_1389_, v___y_1390_, v___y_1391_);
    return v___x_1394_;
}
pub unsafe fn l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkRecOn_spec__0_spec__0___redArg___boxed(
    mut v_constName_1395_: *mut leanh::LeanObject,
    mut v___y_1396_: *mut leanh::LeanObject,
    mut v___y_1397_: *mut leanh::LeanObject,
    mut v___y_1398_: *mut leanh::LeanObject,
    mut v___y_1399_: *mut leanh::LeanObject,
    mut v___y_1400_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1401_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1401_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkRecOn_spec__0_spec__0___redArg(v_constName_1395_, v___y_1396_, v___y_1397_, v___y_1398_, v___y_1399_);
    leanh::lean_dec(v___y_1399_);
    leanh::lean_dec_ref(v___y_1398_);
    leanh::lean_dec(v___y_1397_);
    leanh::lean_dec_ref(v___y_1396_);
    return v_res_1401_;
}
pub unsafe fn l_Lean_getConstInfo___at___00mkRecOn_spec__0(
    mut v_constName_1402_: *mut leanh::LeanObject,
    mut v___y_1403_: *mut leanh::LeanObject,
    mut v___y_1404_: *mut leanh::LeanObject,
    mut v___y_1405_: *mut leanh::LeanObject,
    mut v___y_1406_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1408_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_1409_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1410_: u8 = 0;
    let mut v___x_1411_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1412_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1413_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1415_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1416_: u8 = 0;
    let mut v___x_1418_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1419_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1420_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1408_ = lean_st_ref_get(v___y_1406_);
                v_env_1409_ = leanh::lean_ctor_get(v___x_1408_, 0);
                leanh::lean_inc_ref(v_env_1409_);
                leanh::lean_dec(v___x_1408_);
                v___x_1410_ = 0;
                leanh::lean_inc(v_constName_1402_);
                v___x_1411_ =
                    l_Lean_Environment_find_x3f(v_env_1409_, v_constName_1402_, v___x_1410_);
                if leanh::lean_obj_tag(v___x_1411_) == 0 {
                    v___x_1412_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkRecOn_spec__0_spec__0___redArg(v_constName_1402_, v___y_1403_, v___y_1404_, v___y_1405_, v___y_1406_);
                    return v___x_1412_;
                } else {
                    leanh::lean_dec(v_constName_1402_);
                    v_val_1413_ = leanh::lean_ctor_get(v___x_1411_, 0);
                    v_isSharedCheck_1420_ = (!leanh::lean_is_exclusive(v___x_1411_)) as u8;
                    if v_isSharedCheck_1420_ == 0 {
                        v___x_1415_ = v___x_1411_;
                        v_isShared_1416_ = v_isSharedCheck_1420_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_val_1413_);
                        leanh::lean_dec(v___x_1411_);
                        v___x_1415_ = leanh::lean_box(0);
                        v_isShared_1416_ = v_isSharedCheck_1420_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_1416_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_1415_, 0);
                    v___x_1418_ = v___x_1415_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1419_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1419_, 0, v_val_1413_);
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
    mut v_constName_1421_: *mut leanh::LeanObject,
    mut v___y_1422_: *mut leanh::LeanObject,
    mut v___y_1423_: *mut leanh::LeanObject,
    mut v___y_1424_: *mut leanh::LeanObject,
    mut v___y_1425_: *mut leanh::LeanObject,
    mut v___y_1426_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1427_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1427_ = l_Lean_getConstInfo___at___00mkRecOn_spec__0(
        v_constName_1421_,
        v___y_1422_,
        v___y_1423_,
        v___y_1424_,
        v___y_1425_,
    );
    leanh::lean_dec(v___y_1425_);
    leanh::lean_dec_ref(v___y_1424_);
    leanh::lean_dec(v___y_1423_);
    leanh::lean_dec_ref(v___y_1422_);
    return v_res_1427_;
}
pub unsafe fn _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00mkRecOn_spec__5_spec__6___redArg___closed__0()
-> *mut leanh::LeanObject {
    let mut v___x_1428_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1428_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(
        leanh::lean_box(0),
        leanh::lean_box(0),
    );
    return v___x_1428_;
}
pub unsafe fn _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00mkRecOn_spec__5_spec__6___redArg___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_1429_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1430_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1429_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00mkRecOn_spec__5_spec__6___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00mkRecOn_spec__5_spec__6___redArg___closed__0_once), _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00mkRecOn_spec__5_spec__6___redArg___closed__0);
    v___x_1430_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_1430_, 0, v___x_1429_);
    return v___x_1430_;
}
pub unsafe fn _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00mkRecOn_spec__5_spec__6___redArg___closed__2()
-> *mut leanh::LeanObject {
    let mut v___x_1431_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1432_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1431_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00mkRecOn_spec__5_spec__6___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00mkRecOn_spec__5_spec__6___redArg___closed__1_once), _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00mkRecOn_spec__5_spec__6___redArg___closed__1);
    v___x_1432_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1432_, 0, v___x_1431_);
    leanh::lean_ctor_set(v___x_1432_, 1, v___x_1431_);
    return v___x_1432_;
}
pub unsafe fn _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00mkRecOn_spec__5_spec__6___redArg___closed__3()
-> *mut leanh::LeanObject {
    let mut v___x_1433_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1434_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1433_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00mkRecOn_spec__5_spec__6___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00mkRecOn_spec__5_spec__6___redArg___closed__1_once), _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00mkRecOn_spec__5_spec__6___redArg___closed__1);
    v___x_1434_ = leanh::lean_alloc_ctor(0, 6, (0) as u32);
    leanh::lean_ctor_set(v___x_1434_, 0, v___x_1433_);
    leanh::lean_ctor_set(v___x_1434_, 1, v___x_1433_);
    leanh::lean_ctor_set(v___x_1434_, 2, v___x_1433_);
    leanh::lean_ctor_set(v___x_1434_, 3, v___x_1433_);
    leanh::lean_ctor_set(v___x_1434_, 4, v___x_1433_);
    leanh::lean_ctor_set(v___x_1434_, 5, v___x_1433_);
    return v___x_1434_;
}
pub unsafe fn l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00mkRecOn_spec__5_spec__6___redArg(
    mut v_declName_1435_: *mut leanh::LeanObject,
    mut v_s_1436_: u8,
    mut v___y_1437_: *mut leanh::LeanObject,
    mut v___y_1438_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1440_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_1441_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_1442_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ngen_1443_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_1444_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_traceState_1445_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_messages_1446_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_infoState_1447_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_1448_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1450_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1451_: u8 = 0;
    let mut v___x_1452_: u8 = 0;
    let mut v___x_1453_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1454_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1455_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1457_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1458_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1459_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_1460_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_zetaDeltaFVarIds_1461_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_postponed_1462_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_diag_1463_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1465_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1466_: u8 = 0;
    let mut v___x_1467_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1469_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1470_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1471_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1472_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1473_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1474_: u8 = 0;
    let mut v_unused_1475_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1476_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1477_: u8 = 0;
    let mut v_unused_1478_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1440_ = lean_st_ref_take(v___y_1438_);
                v_env_1441_ = leanh::lean_ctor_get(v___x_1440_, 0);
                v_nextMacroScope_1442_ = leanh::lean_ctor_get(v___x_1440_, 1);
                v_ngen_1443_ = leanh::lean_ctor_get(v___x_1440_, 2);
                v_auxDeclNGen_1444_ = leanh::lean_ctor_get(v___x_1440_, 3);
                v_traceState_1445_ = leanh::lean_ctor_get(v___x_1440_, 4);
                v_messages_1446_ = leanh::lean_ctor_get(v___x_1440_, 6);
                v_infoState_1447_ = leanh::lean_ctor_get(v___x_1440_, 7);
                v_snapshotTasks_1448_ = leanh::lean_ctor_get(v___x_1440_, 8);
                v_isSharedCheck_1477_ = (!leanh::lean_is_exclusive(v___x_1440_)) as u8;
                if v_isSharedCheck_1477_ == 0 {
                    v_unused_1478_ = leanh::lean_ctor_get(v___x_1440_, 5);
                    leanh::lean_dec(v_unused_1478_);
                    v___x_1450_ = v___x_1440_;
                    v_isShared_1451_ = v_isSharedCheck_1477_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_snapshotTasks_1448_);
                    leanh::lean_inc(v_infoState_1447_);
                    leanh::lean_inc(v_messages_1446_);
                    leanh::lean_inc(v_traceState_1445_);
                    leanh::lean_inc(v_auxDeclNGen_1444_);
                    leanh::lean_inc(v_ngen_1443_);
                    leanh::lean_inc(v_nextMacroScope_1442_);
                    leanh::lean_inc(v_env_1441_);
                    leanh::lean_dec(v___x_1440_);
                    v___x_1450_ = leanh::lean_box(0);
                    v_isShared_1451_ = v_isSharedCheck_1477_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_1452_ = 0;
                v___x_1453_ = leanh::lean_box(0);
                v___x_1454_ = l___private_Lean_ReducibilityAttrs_0__Lean_setReducibilityStatusCore(
                    v_env_1441_,
                    v_declName_1435_,
                    v_s_1436_,
                    v___x_1452_,
                    v___x_1453_,
                );
                v___x_1455_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00mkRecOn_spec__5_spec__6___redArg___closed__2), core::ptr::addr_of_mut!(l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00mkRecOn_spec__5_spec__6___redArg___closed__2_once), _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00mkRecOn_spec__5_spec__6___redArg___closed__2);
                if v_isShared_1451_ == 0 {
                    leanh::lean_ctor_set(v___x_1450_, 5, v___x_1455_);
                    leanh::lean_ctor_set(v___x_1450_, 0, v___x_1454_);
                    v___x_1457_ = v___x_1450_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1476_ = leanh::lean_alloc_ctor(0, 9, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1476_, 0, v___x_1454_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1476_, 1, v_nextMacroScope_1442_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1476_, 2, v_ngen_1443_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1476_, 3, v_auxDeclNGen_1444_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1476_, 4, v_traceState_1445_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1476_, 5, v___x_1455_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1476_, 6, v_messages_1446_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1476_, 7, v_infoState_1447_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1476_, 8, v_snapshotTasks_1448_);
                    v___x_1457_ = v_reuseFailAlloc_1476_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1458_ = lean_st_ref_set(v___y_1438_, v___x_1457_);
                v___x_1459_ = lean_st_ref_take(v___y_1437_);
                v_mctx_1460_ = leanh::lean_ctor_get(v___x_1459_, 0);
                v_zetaDeltaFVarIds_1461_ = leanh::lean_ctor_get(v___x_1459_, 2);
                v_postponed_1462_ = leanh::lean_ctor_get(v___x_1459_, 3);
                v_diag_1463_ = leanh::lean_ctor_get(v___x_1459_, 4);
                v_isSharedCheck_1474_ = (!leanh::lean_is_exclusive(v___x_1459_)) as u8;
                if v_isSharedCheck_1474_ == 0 {
                    v_unused_1475_ = leanh::lean_ctor_get(v___x_1459_, 1);
                    leanh::lean_dec(v_unused_1475_);
                    v___x_1465_ = v___x_1459_;
                    v_isShared_1466_ = v_isSharedCheck_1474_;
                    state = 3;
                    continue;
                } else {
                    leanh::lean_inc(v_diag_1463_);
                    leanh::lean_inc(v_postponed_1462_);
                    leanh::lean_inc(v_zetaDeltaFVarIds_1461_);
                    leanh::lean_inc(v_mctx_1460_);
                    leanh::lean_dec(v___x_1459_);
                    v___x_1465_ = leanh::lean_box(0);
                    v_isShared_1466_ = v_isSharedCheck_1474_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_1467_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00mkRecOn_spec__5_spec__6___redArg___closed__3), core::ptr::addr_of_mut!(l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00mkRecOn_spec__5_spec__6___redArg___closed__3_once), _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00mkRecOn_spec__5_spec__6___redArg___closed__3);
                if v_isShared_1466_ == 0 {
                    leanh::lean_ctor_set(v___x_1465_, 1, v___x_1467_);
                    v___x_1469_ = v___x_1465_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1473_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1473_, 0, v_mctx_1460_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1473_, 1, v___x_1467_);
                    leanh::lean_ctor_set(
                        v_reuseFailAlloc_1473_,
                        2,
                        v_zetaDeltaFVarIds_1461_,
                    );
                    leanh::lean_ctor_set(v_reuseFailAlloc_1473_, 3, v_postponed_1462_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1473_, 4, v_diag_1463_);
                    v___x_1469_ = v_reuseFailAlloc_1473_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_1470_ = lean_st_ref_set(v___y_1437_, v___x_1469_);
                v___x_1471_ = leanh::lean_box(0);
                v___x_1472_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_1472_, 0, v___x_1471_);
                return v___x_1472_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00mkRecOn_spec__5_spec__6___redArg___boxed(
    mut v_declName_1479_: *mut leanh::LeanObject,
    mut v_s_1480_: *mut leanh::LeanObject,
    mut v___y_1481_: *mut leanh::LeanObject,
    mut v___y_1482_: *mut leanh::LeanObject,
    mut v___y_1483_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_s_boxed_1484_: u8 = 0;
    let mut v_res_1485_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_s_boxed_1484_ = (leanh::lean_unbox(v_s_1480_) as u8);
    v_res_1485_ = l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00mkRecOn_spec__5_spec__6___redArg(v_declName_1479_, v_s_boxed_1484_, v___y_1481_, v___y_1482_);
    leanh::lean_dec(v___y_1482_);
    leanh::lean_dec(v___y_1481_);
    return v_res_1485_;
}
pub unsafe fn l_Lean_setReducibleAttribute___at___00mkRecOn_spec__5(
    mut v_declName_1486_: *mut leanh::LeanObject,
    mut v___y_1487_: *mut leanh::LeanObject,
    mut v___y_1488_: *mut leanh::LeanObject,
    mut v___y_1489_: *mut leanh::LeanObject,
    mut v___y_1490_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1492_: u8 = 0;
    let mut v___x_1493_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1492_ = 0;
    v___x_1493_ = l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00mkRecOn_spec__5_spec__6___redArg(v_declName_1486_, v___x_1492_, v___y_1488_, v___y_1490_);
    return v___x_1493_;
}
pub unsafe fn l_Lean_setReducibleAttribute___at___00mkRecOn_spec__5___boxed(
    mut v_declName_1494_: *mut leanh::LeanObject,
    mut v___y_1495_: *mut leanh::LeanObject,
    mut v___y_1496_: *mut leanh::LeanObject,
    mut v___y_1497_: *mut leanh::LeanObject,
    mut v___y_1498_: *mut leanh::LeanObject,
    mut v___y_1499_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1500_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1500_ = l_Lean_setReducibleAttribute___at___00mkRecOn_spec__5(
        v_declName_1494_,
        v___y_1495_,
        v___y_1496_,
        v___y_1497_,
        v___y_1498_,
    );
    leanh::lean_dec(v___y_1498_);
    leanh::lean_dec_ref(v___y_1497_);
    leanh::lean_dec(v___y_1496_);
    leanh::lean_dec_ref(v___y_1495_);
    return v_res_1500_;
}
pub unsafe fn _init_l_mkRecOn___closed__1() -> *mut leanh::LeanObject {
    let mut v___x_1502_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1503_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1502_ = l_mkRecOn___closed__0;
    v___x_1503_ = l_Lean_stringToMessageData(v___x_1502_);
    return v___x_1503_;
}
pub unsafe fn l_mkRecOn(
    mut v_n_1504_: *mut leanh::LeanObject,
    mut v_a_1505_: *mut leanh::LeanObject,
    mut v_a_1506_: *mut leanh::LeanObject,
    mut v_a_1507_: *mut leanh::LeanObject,
    mut v_a_1508_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1510_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1511_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1512_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1513_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1515_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1516_: u8 = 0;
    let mut v_toConstantVal_1517_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_numIndices_1518_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_numMinors_1519_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_name_1520_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_levelParams_1521_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_type_1522_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1523_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1524_: u8 = 0;
    let mut v___x_1525_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1526_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1528_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1529_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toConstantVal_1530_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_name_1531_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1532_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1534_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1535_: u8 = 0;
    let mut v___x_1536_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_1537_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_1538_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ngen_1539_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_1540_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_traceState_1541_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_messages_1542_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_infoState_1543_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_1544_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1546_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1547_: u8 = 0;
    let mut v___x_1548_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1549_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1551_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1552_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1553_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_1554_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_zetaDeltaFVarIds_1555_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_postponed_1556_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_diag_1557_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1559_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1560_: u8 = 0;
    let mut v___x_1561_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1563_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1564_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1565_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_1566_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_1567_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ngen_1568_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_1569_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_traceState_1570_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_messages_1571_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_infoState_1572_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_1573_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1575_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1576_: u8 = 0;
    let mut v___x_1577_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1579_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1580_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1581_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_1582_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_zetaDeltaFVarIds_1583_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_postponed_1584_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_diag_1585_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1587_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1588_: u8 = 0;
    let mut v___x_1590_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1591_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1592_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1594_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1595_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1596_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1597_: u8 = 0;
    let mut v_unused_1598_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1599_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1600_: u8 = 0;
    let mut v_unused_1601_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1602_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1603_: u8 = 0;
    let mut v_unused_1604_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1605_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1606_: u8 = 0;
    let mut v_unused_1607_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1608_: u8 = 0;
    let mut v_unused_1609_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1610_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1611_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1613_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1614_: u8 = 0;
    let mut v___x_1616_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1617_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1618_: u8 = 0;
    let mut v_isSharedCheck_1619_: u8 = 0;
    let mut v___x_1620_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1621_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1622_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1623_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1624_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1626_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1627_: u8 = 0;
    let mut v___x_1629_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1630_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1631_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                leanh::lean_inc(v_n_1504_);
                v___x_1510_ = l_Lean_mkRecName(v_n_1504_);
                leanh::lean_inc(v___x_1510_);
                v___x_1511_ = l_Lean_getConstInfo___at___00mkRecOn_spec__0(
                    v___x_1510_,
                    v_a_1505_,
                    v_a_1506_,
                    v_a_1507_,
                    v_a_1508_,
                );
                if leanh::lean_obj_tag(v___x_1511_) == 0 {
                    v_a_1512_ = leanh::lean_ctor_get(v___x_1511_, 0);
                    leanh::lean_inc(v_a_1512_);
                    leanh::lean_dec_ref_known(v___x_1511_, 1);
                    if leanh::lean_obj_tag(v_a_1512_) == 7 {
                        leanh::lean_dec(v___x_1510_);
                        v_val_1513_ = leanh::lean_ctor_get(v_a_1512_, 0);
                        v_isSharedCheck_1619_ = (!leanh::lean_is_exclusive(v_a_1512_)) as u8;
                        if v_isSharedCheck_1619_ == 0 {
                            v___x_1515_ = v_a_1512_;
                            v_isShared_1516_ = v_isSharedCheck_1619_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_inc(v_val_1513_);
                            leanh::lean_dec(v_a_1512_);
                            v___x_1515_ = leanh::lean_box(0);
                            v_isShared_1516_ = v_isSharedCheck_1619_;
                            state = 1;
                            continue;
                        }
                    } else {
                        leanh::lean_dec(v_a_1512_);
                        leanh::lean_dec(v_n_1504_);
                        v___x_1620_ = l_Lean_MessageData_ofName(v___x_1510_);
                        v___x_1621_ = leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(l_mkRecOn___closed__1),
                            core::ptr::addr_of_mut!(l_mkRecOn___closed__1_once),
                            _init_l_mkRecOn___closed__1,
                        );
                        v___x_1622_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                        leanh::lean_ctor_set(v___x_1622_, 0, v___x_1620_);
                        leanh::lean_ctor_set(v___x_1622_, 1, v___x_1621_);
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
                    leanh::lean_dec(v___x_1510_);
                    leanh::lean_dec(v_n_1504_);
                    v_a_1624_ = leanh::lean_ctor_get(v___x_1511_, 0);
                    v_isSharedCheck_1631_ = (!leanh::lean_is_exclusive(v___x_1511_)) as u8;
                    if v_isSharedCheck_1631_ == 0 {
                        v___x_1626_ = v___x_1511_;
                        v_isShared_1627_ = v_isSharedCheck_1631_;
                        state = 15;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_1624_);
                        leanh::lean_dec(v___x_1511_);
                        v___x_1626_ = leanh::lean_box(0);
                        v_isShared_1627_ = v_isSharedCheck_1631_;
                        state = 15;
                        continue;
                    }
                }
            }
            1 => {
                v_toConstantVal_1517_ = leanh::lean_ctor_get(v_val_1513_, 0);
                leanh::lean_inc_ref(v_toConstantVal_1517_);
                v_numIndices_1518_ = leanh::lean_ctor_get(v_val_1513_, 3);
                leanh::lean_inc(v_numIndices_1518_);
                v_numMinors_1519_ = leanh::lean_ctor_get(v_val_1513_, 5);
                leanh::lean_inc(v_numMinors_1519_);
                leanh::lean_dec_ref(v_val_1513_);
                v_name_1520_ = leanh::lean_ctor_get(v_toConstantVal_1517_, 0);
                leanh::lean_inc(v_name_1520_);
                v_levelParams_1521_ = leanh::lean_ctor_get(v_toConstantVal_1517_, 1);
                leanh::lean_inc(v_levelParams_1521_);
                v_type_1522_ = leanh::lean_ctor_get(v_toConstantVal_1517_, 2);
                leanh::lean_inc_ref(v_type_1522_);
                leanh::lean_dec_ref(v_toConstantVal_1517_);
                v___f_1523_ = leanh::lean_alloc_closure(
                    l_mkRecOn___lam__0___boxed as *mut core::ffi::c_void,
                    12,
                    5,
                );
                leanh::lean_closure_set(v___f_1523_, 0, v_levelParams_1521_);
                leanh::lean_closure_set(v___f_1523_, 1, v_name_1520_);
                leanh::lean_closure_set(v___f_1523_, 2, v_numMinors_1519_);
                leanh::lean_closure_set(v___f_1523_, 3, v_numIndices_1518_);
                leanh::lean_closure_set(v___f_1523_, 4, v_n_1504_);
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
                if leanh::lean_obj_tag(v___x_1525_) == 0 {
                    v_a_1526_ = leanh::lean_ctor_get(v___x_1525_, 0);
                    leanh::lean_inc_n(v_a_1526_, 2);
                    leanh::lean_dec_ref_known(v___x_1525_, 1);
                    if v_isShared_1516_ == 0 {
                        leanh::lean_ctor_set_tag(v___x_1515_, 1);
                        leanh::lean_ctor_set(v___x_1515_, 0, v_a_1526_);
                        v___x_1528_ = v___x_1515_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_1610_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1610_, 0, v_a_1526_);
                        v___x_1528_ = v_reuseFailAlloc_1610_;
                        state = 2;
                        continue;
                    }
                } else {
                    leanh::lean_del_object(v___x_1515_);
                    v_a_1611_ = leanh::lean_ctor_get(v___x_1525_, 0);
                    v_isSharedCheck_1618_ = (!leanh::lean_is_exclusive(v___x_1525_)) as u8;
                    if v_isSharedCheck_1618_ == 0 {
                        v___x_1613_ = v___x_1525_;
                        v_isShared_1614_ = v_isSharedCheck_1618_;
                        state = 13;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_1611_);
                        leanh::lean_dec(v___x_1525_);
                        v___x_1613_ = leanh::lean_box(0);
                        v_isShared_1614_ = v_isSharedCheck_1618_;
                        state = 13;
                        continue;
                    }
                }
            }
            2 => {
                v___x_1529_ = l_Lean_addDecl(v___x_1528_, v___x_1524_, v_a_1507_, v_a_1508_);
                if leanh::lean_obj_tag(v___x_1529_) == 0 {
                    leanh::lean_dec_ref_known(v___x_1529_, 1);
                    v_toConstantVal_1530_ = leanh::lean_ctor_get(v_a_1526_, 0);
                    leanh::lean_inc_ref(v_toConstantVal_1530_);
                    leanh::lean_dec(v_a_1526_);
                    v_name_1531_ = leanh::lean_ctor_get(v_toConstantVal_1530_, 0);
                    leanh::lean_inc_n(v_name_1531_, 2);
                    leanh::lean_dec_ref(v_toConstantVal_1530_);
                    v___x_1532_ = l_Lean_setReducibleAttribute___at___00mkRecOn_spec__5(
                        v_name_1531_,
                        v_a_1505_,
                        v_a_1506_,
                        v_a_1507_,
                        v_a_1508_,
                    );
                    v_isSharedCheck_1608_ = (!leanh::lean_is_exclusive(v___x_1532_)) as u8;
                    if v_isSharedCheck_1608_ == 0 {
                        v_unused_1609_ = leanh::lean_ctor_get(v___x_1532_, 0);
                        leanh::lean_dec(v_unused_1609_);
                        v___x_1534_ = v___x_1532_;
                        v_isShared_1535_ = v_isSharedCheck_1608_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_dec(v___x_1532_);
                        v___x_1534_ = leanh::lean_box(0);
                        v_isShared_1535_ = v_isSharedCheck_1608_;
                        state = 3;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v_a_1526_);
                    return v___x_1529_;
                }
            }
            3 => {
                v___x_1536_ = lean_st_ref_take(v_a_1508_);
                v_env_1537_ = leanh::lean_ctor_get(v___x_1536_, 0);
                v_nextMacroScope_1538_ = leanh::lean_ctor_get(v___x_1536_, 1);
                v_ngen_1539_ = leanh::lean_ctor_get(v___x_1536_, 2);
                v_auxDeclNGen_1540_ = leanh::lean_ctor_get(v___x_1536_, 3);
                v_traceState_1541_ = leanh::lean_ctor_get(v___x_1536_, 4);
                v_messages_1542_ = leanh::lean_ctor_get(v___x_1536_, 6);
                v_infoState_1543_ = leanh::lean_ctor_get(v___x_1536_, 7);
                v_snapshotTasks_1544_ = leanh::lean_ctor_get(v___x_1536_, 8);
                v_isSharedCheck_1606_ = (!leanh::lean_is_exclusive(v___x_1536_)) as u8;
                if v_isSharedCheck_1606_ == 0 {
                    v_unused_1607_ = leanh::lean_ctor_get(v___x_1536_, 5);
                    leanh::lean_dec(v_unused_1607_);
                    v___x_1546_ = v___x_1536_;
                    v_isShared_1547_ = v_isSharedCheck_1606_;
                    state = 4;
                    continue;
                } else {
                    leanh::lean_inc(v_snapshotTasks_1544_);
                    leanh::lean_inc(v_infoState_1543_);
                    leanh::lean_inc(v_messages_1542_);
                    leanh::lean_inc(v_traceState_1541_);
                    leanh::lean_inc(v_auxDeclNGen_1540_);
                    leanh::lean_inc(v_ngen_1539_);
                    leanh::lean_inc(v_nextMacroScope_1538_);
                    leanh::lean_inc(v_env_1537_);
                    leanh::lean_dec(v___x_1536_);
                    v___x_1546_ = leanh::lean_box(0);
                    v_isShared_1547_ = v_isSharedCheck_1606_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                leanh::lean_inc(v_name_1531_);
                v___x_1548_ = l_Lean_markAuxRecursor(v_env_1537_, v_name_1531_);
                v___x_1549_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00mkRecOn_spec__5_spec__6___redArg___closed__2), core::ptr::addr_of_mut!(l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00mkRecOn_spec__5_spec__6___redArg___closed__2_once), _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00mkRecOn_spec__5_spec__6___redArg___closed__2);
                if v_isShared_1547_ == 0 {
                    leanh::lean_ctor_set(v___x_1546_, 5, v___x_1549_);
                    leanh::lean_ctor_set(v___x_1546_, 0, v___x_1548_);
                    v___x_1551_ = v___x_1546_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_1605_ = leanh::lean_alloc_ctor(0, 9, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1605_, 0, v___x_1548_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1605_, 1, v_nextMacroScope_1538_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1605_, 2, v_ngen_1539_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1605_, 3, v_auxDeclNGen_1540_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1605_, 4, v_traceState_1541_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1605_, 5, v___x_1549_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1605_, 6, v_messages_1542_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1605_, 7, v_infoState_1543_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1605_, 8, v_snapshotTasks_1544_);
                    v___x_1551_ = v_reuseFailAlloc_1605_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v___x_1552_ = lean_st_ref_set(v_a_1508_, v___x_1551_);
                v___x_1553_ = lean_st_ref_take(v_a_1506_);
                v_mctx_1554_ = leanh::lean_ctor_get(v___x_1553_, 0);
                v_zetaDeltaFVarIds_1555_ = leanh::lean_ctor_get(v___x_1553_, 2);
                v_postponed_1556_ = leanh::lean_ctor_get(v___x_1553_, 3);
                v_diag_1557_ = leanh::lean_ctor_get(v___x_1553_, 4);
                v_isSharedCheck_1603_ = (!leanh::lean_is_exclusive(v___x_1553_)) as u8;
                if v_isSharedCheck_1603_ == 0 {
                    v_unused_1604_ = leanh::lean_ctor_get(v___x_1553_, 1);
                    leanh::lean_dec(v_unused_1604_);
                    v___x_1559_ = v___x_1553_;
                    v_isShared_1560_ = v_isSharedCheck_1603_;
                    state = 6;
                    continue;
                } else {
                    leanh::lean_inc(v_diag_1557_);
                    leanh::lean_inc(v_postponed_1556_);
                    leanh::lean_inc(v_zetaDeltaFVarIds_1555_);
                    leanh::lean_inc(v_mctx_1554_);
                    leanh::lean_dec(v___x_1553_);
                    v___x_1559_ = leanh::lean_box(0);
                    v_isShared_1560_ = v_isSharedCheck_1603_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                v___x_1561_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00mkRecOn_spec__5_spec__6___redArg___closed__3), core::ptr::addr_of_mut!(l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00mkRecOn_spec__5_spec__6___redArg___closed__3_once), _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00mkRecOn_spec__5_spec__6___redArg___closed__3);
                if v_isShared_1560_ == 0 {
                    leanh::lean_ctor_set(v___x_1559_, 1, v___x_1561_);
                    v___x_1563_ = v___x_1559_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_1602_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1602_, 0, v_mctx_1554_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1602_, 1, v___x_1561_);
                    leanh::lean_ctor_set(
                        v_reuseFailAlloc_1602_,
                        2,
                        v_zetaDeltaFVarIds_1555_,
                    );
                    leanh::lean_ctor_set(v_reuseFailAlloc_1602_, 3, v_postponed_1556_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1602_, 4, v_diag_1557_);
                    v___x_1563_ = v_reuseFailAlloc_1602_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                v___x_1564_ = lean_st_ref_set(v_a_1506_, v___x_1563_);
                v___x_1565_ = lean_st_ref_take(v_a_1508_);
                v_env_1566_ = leanh::lean_ctor_get(v___x_1565_, 0);
                v_nextMacroScope_1567_ = leanh::lean_ctor_get(v___x_1565_, 1);
                v_ngen_1568_ = leanh::lean_ctor_get(v___x_1565_, 2);
                v_auxDeclNGen_1569_ = leanh::lean_ctor_get(v___x_1565_, 3);
                v_traceState_1570_ = leanh::lean_ctor_get(v___x_1565_, 4);
                v_messages_1571_ = leanh::lean_ctor_get(v___x_1565_, 6);
                v_infoState_1572_ = leanh::lean_ctor_get(v___x_1565_, 7);
                v_snapshotTasks_1573_ = leanh::lean_ctor_get(v___x_1565_, 8);
                v_isSharedCheck_1600_ = (!leanh::lean_is_exclusive(v___x_1565_)) as u8;
                if v_isSharedCheck_1600_ == 0 {
                    v_unused_1601_ = leanh::lean_ctor_get(v___x_1565_, 5);
                    leanh::lean_dec(v_unused_1601_);
                    v___x_1575_ = v___x_1565_;
                    v_isShared_1576_ = v_isSharedCheck_1600_;
                    state = 8;
                    continue;
                } else {
                    leanh::lean_inc(v_snapshotTasks_1573_);
                    leanh::lean_inc(v_infoState_1572_);
                    leanh::lean_inc(v_messages_1571_);
                    leanh::lean_inc(v_traceState_1570_);
                    leanh::lean_inc(v_auxDeclNGen_1569_);
                    leanh::lean_inc(v_ngen_1568_);
                    leanh::lean_inc(v_nextMacroScope_1567_);
                    leanh::lean_inc(v_env_1566_);
                    leanh::lean_dec(v___x_1565_);
                    v___x_1575_ = leanh::lean_box(0);
                    v_isShared_1576_ = v_isSharedCheck_1600_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                v___x_1577_ = l_Lean_addProtected(v_env_1566_, v_name_1531_);
                if v_isShared_1576_ == 0 {
                    leanh::lean_ctor_set(v___x_1575_, 5, v___x_1549_);
                    leanh::lean_ctor_set(v___x_1575_, 0, v___x_1577_);
                    v___x_1579_ = v___x_1575_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_1599_ = leanh::lean_alloc_ctor(0, 9, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1599_, 0, v___x_1577_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1599_, 1, v_nextMacroScope_1567_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1599_, 2, v_ngen_1568_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1599_, 3, v_auxDeclNGen_1569_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1599_, 4, v_traceState_1570_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1599_, 5, v___x_1549_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1599_, 6, v_messages_1571_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1599_, 7, v_infoState_1572_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1599_, 8, v_snapshotTasks_1573_);
                    v___x_1579_ = v_reuseFailAlloc_1599_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                v___x_1580_ = lean_st_ref_set(v_a_1508_, v___x_1579_);
                v___x_1581_ = lean_st_ref_take(v_a_1506_);
                v_mctx_1582_ = leanh::lean_ctor_get(v___x_1581_, 0);
                v_zetaDeltaFVarIds_1583_ = leanh::lean_ctor_get(v___x_1581_, 2);
                v_postponed_1584_ = leanh::lean_ctor_get(v___x_1581_, 3);
                v_diag_1585_ = leanh::lean_ctor_get(v___x_1581_, 4);
                v_isSharedCheck_1597_ = (!leanh::lean_is_exclusive(v___x_1581_)) as u8;
                if v_isSharedCheck_1597_ == 0 {
                    v_unused_1598_ = leanh::lean_ctor_get(v___x_1581_, 1);
                    leanh::lean_dec(v_unused_1598_);
                    v___x_1587_ = v___x_1581_;
                    v_isShared_1588_ = v_isSharedCheck_1597_;
                    state = 10;
                    continue;
                } else {
                    leanh::lean_inc(v_diag_1585_);
                    leanh::lean_inc(v_postponed_1584_);
                    leanh::lean_inc(v_zetaDeltaFVarIds_1583_);
                    leanh::lean_inc(v_mctx_1582_);
                    leanh::lean_dec(v___x_1581_);
                    v___x_1587_ = leanh::lean_box(0);
                    v_isShared_1588_ = v_isSharedCheck_1597_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                if v_isShared_1588_ == 0 {
                    leanh::lean_ctor_set(v___x_1587_, 1, v___x_1561_);
                    v___x_1590_ = v___x_1587_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_1596_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1596_, 0, v_mctx_1582_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1596_, 1, v___x_1561_);
                    leanh::lean_ctor_set(
                        v_reuseFailAlloc_1596_,
                        2,
                        v_zetaDeltaFVarIds_1583_,
                    );
                    leanh::lean_ctor_set(v_reuseFailAlloc_1596_, 3, v_postponed_1584_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1596_, 4, v_diag_1585_);
                    v___x_1590_ = v_reuseFailAlloc_1596_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                v___x_1591_ = lean_st_ref_set(v_a_1506_, v___x_1590_);
                v___x_1592_ = leanh::lean_box(0);
                if v_isShared_1535_ == 0 {
                    leanh::lean_ctor_set(v___x_1534_, 0, v___x_1592_);
                    v___x_1594_ = v___x_1534_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_1595_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1595_, 0, v___x_1592_);
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
                    v_reuseFailAlloc_1617_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1617_, 0, v_a_1611_);
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
                    v_reuseFailAlloc_1630_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1630_, 0, v_a_1624_);
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
    mut v_n_1632_: *mut leanh::LeanObject,
    mut v_a_1633_: *mut leanh::LeanObject,
    mut v_a_1634_: *mut leanh::LeanObject,
    mut v_a_1635_: *mut leanh::LeanObject,
    mut v_a_1636_: *mut leanh::LeanObject,
    mut v_a_1637_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1638_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1638_ = l_mkRecOn(v_n_1632_, v_a_1633_, v_a_1634_, v_a_1635_, v_a_1636_);
    leanh::lean_dec(v_a_1636_);
    leanh::lean_dec_ref(v_a_1635_);
    leanh::lean_dec(v_a_1634_);
    leanh::lean_dec_ref(v_a_1633_);
    return v_res_1638_;
}
pub unsafe fn l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00mkRecOn_spec__2(
    mut v_inst_1639_: *mut leanh::LeanObject,
    mut v_R_1640_: *mut leanh::LeanObject,
    mut v_a_1641_: *mut leanh::LeanObject,
    mut v_b_1642_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1643_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1643_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00mkRecOn_spec__2___redArg(v_a_1641_, v_b_1642_);
    return v___x_1643_;
}
pub unsafe fn l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00mkRecOn_spec__5_spec__6(
    mut v_declName_1644_: *mut leanh::LeanObject,
    mut v_s_1645_: u8,
    mut v___y_1646_: *mut leanh::LeanObject,
    mut v___y_1647_: *mut leanh::LeanObject,
    mut v___y_1648_: *mut leanh::LeanObject,
    mut v___y_1649_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1651_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1651_ = l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00mkRecOn_spec__5_spec__6___redArg(v_declName_1644_, v_s_1645_, v___y_1647_, v___y_1649_);
    return v___x_1651_;
}
pub unsafe fn l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00mkRecOn_spec__5_spec__6___boxed(
    mut v_declName_1652_: *mut leanh::LeanObject,
    mut v_s_1653_: *mut leanh::LeanObject,
    mut v___y_1654_: *mut leanh::LeanObject,
    mut v___y_1655_: *mut leanh::LeanObject,
    mut v___y_1656_: *mut leanh::LeanObject,
    mut v___y_1657_: *mut leanh::LeanObject,
    mut v___y_1658_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_s_boxed_1659_: u8 = 0;
    let mut v_res_1660_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_s_boxed_1659_ = (leanh::lean_unbox(v_s_1653_) as u8);
    v_res_1660_ = l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00mkRecOn_spec__5_spec__6(v_declName_1652_, v_s_boxed_1659_, v___y_1654_, v___y_1655_, v___y_1656_, v___y_1657_);
    leanh::lean_dec(v___y_1657_);
    leanh::lean_dec_ref(v___y_1656_);
    leanh::lean_dec(v___y_1655_);
    leanh::lean_dec_ref(v___y_1654_);
    return v_res_1660_;
}
pub unsafe fn l_Lean_throwError___at___00mkRecOn_spec__6(
    mut v_00_u03b1_1661_: *mut leanh::LeanObject,
    mut v_msg_1662_: *mut leanh::LeanObject,
    mut v___y_1663_: *mut leanh::LeanObject,
    mut v___y_1664_: *mut leanh::LeanObject,
    mut v___y_1665_: *mut leanh::LeanObject,
    mut v___y_1666_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1668_: *mut leanh::LeanObject = core::ptr::null_mut();
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
    mut v_00_u03b1_1669_: *mut leanh::LeanObject,
    mut v_msg_1670_: *mut leanh::LeanObject,
    mut v___y_1671_: *mut leanh::LeanObject,
    mut v___y_1672_: *mut leanh::LeanObject,
    mut v___y_1673_: *mut leanh::LeanObject,
    mut v___y_1674_: *mut leanh::LeanObject,
    mut v___y_1675_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1676_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1676_ = l_Lean_throwError___at___00mkRecOn_spec__6(
        v_00_u03b1_1669_,
        v_msg_1670_,
        v___y_1671_,
        v___y_1672_,
        v___y_1673_,
        v___y_1674_,
    );
    leanh::lean_dec(v___y_1674_);
    leanh::lean_dec_ref(v___y_1673_);
    leanh::lean_dec(v___y_1672_);
    leanh::lean_dec_ref(v___y_1671_);
    return v_res_1676_;
}
pub unsafe fn l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkRecOn_spec__0_spec__0(
    mut v_00_u03b1_1677_: *mut leanh::LeanObject,
    mut v_constName_1678_: *mut leanh::LeanObject,
    mut v___y_1679_: *mut leanh::LeanObject,
    mut v___y_1680_: *mut leanh::LeanObject,
    mut v___y_1681_: *mut leanh::LeanObject,
    mut v___y_1682_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1684_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1684_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkRecOn_spec__0_spec__0___redArg(v_constName_1678_, v___y_1679_, v___y_1680_, v___y_1681_, v___y_1682_);
    return v___x_1684_;
}
pub unsafe fn l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkRecOn_spec__0_spec__0___boxed(
    mut v_00_u03b1_1685_: *mut leanh::LeanObject,
    mut v_constName_1686_: *mut leanh::LeanObject,
    mut v___y_1687_: *mut leanh::LeanObject,
    mut v___y_1688_: *mut leanh::LeanObject,
    mut v___y_1689_: *mut leanh::LeanObject,
    mut v___y_1690_: *mut leanh::LeanObject,
    mut v___y_1691_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1692_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1692_ =
        l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkRecOn_spec__0_spec__0(
            v_00_u03b1_1685_,
            v_constName_1686_,
            v___y_1687_,
            v___y_1688_,
            v___y_1689_,
            v___y_1690_,
        );
    leanh::lean_dec(v___y_1690_);
    leanh::lean_dec_ref(v___y_1689_);
    leanh::lean_dec(v___y_1688_);
    leanh::lean_dec_ref(v___y_1687_);
    return v_res_1692_;
}
pub unsafe fn l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkRecOn_spec__0_spec__0_spec__3(
    mut v_00_u03b1_1693_: *mut leanh::LeanObject,
    mut v_ref_1694_: *mut leanh::LeanObject,
    mut v_constName_1695_: *mut leanh::LeanObject,
    mut v___y_1696_: *mut leanh::LeanObject,
    mut v___y_1697_: *mut leanh::LeanObject,
    mut v___y_1698_: *mut leanh::LeanObject,
    mut v___y_1699_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1701_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1701_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkRecOn_spec__0_spec__0_spec__3___redArg(v_ref_1694_, v_constName_1695_, v___y_1696_, v___y_1697_, v___y_1698_, v___y_1699_);
    return v___x_1701_;
}
pub unsafe fn l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkRecOn_spec__0_spec__0_spec__3___boxed(
    mut v_00_u03b1_1702_: *mut leanh::LeanObject,
    mut v_ref_1703_: *mut leanh::LeanObject,
    mut v_constName_1704_: *mut leanh::LeanObject,
    mut v___y_1705_: *mut leanh::LeanObject,
    mut v___y_1706_: *mut leanh::LeanObject,
    mut v___y_1707_: *mut leanh::LeanObject,
    mut v___y_1708_: *mut leanh::LeanObject,
    mut v___y_1709_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1710_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1710_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkRecOn_spec__0_spec__0_spec__3(v_00_u03b1_1702_, v_ref_1703_, v_constName_1704_, v___y_1705_, v___y_1706_, v___y_1707_, v___y_1708_);
    leanh::lean_dec(v___y_1708_);
    leanh::lean_dec_ref(v___y_1707_);
    leanh::lean_dec(v___y_1706_);
    leanh::lean_dec_ref(v___y_1705_);
    leanh::lean_dec(v_ref_1703_);
    return v_res_1710_;
}
pub unsafe fn l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkRecOn_spec__0_spec__0_spec__3_spec__10(
    mut v_00_u03b1_1711_: *mut leanh::LeanObject,
    mut v_ref_1712_: *mut leanh::LeanObject,
    mut v_msg_1713_: *mut leanh::LeanObject,
    mut v_declHint_1714_: *mut leanh::LeanObject,
    mut v___y_1715_: *mut leanh::LeanObject,
    mut v___y_1716_: *mut leanh::LeanObject,
    mut v___y_1717_: *mut leanh::LeanObject,
    mut v___y_1718_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1720_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1720_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkRecOn_spec__0_spec__0_spec__3_spec__10___redArg(v_ref_1712_, v_msg_1713_, v_declHint_1714_, v___y_1715_, v___y_1716_, v___y_1717_, v___y_1718_);
    return v___x_1720_;
}
pub unsafe fn l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkRecOn_spec__0_spec__0_spec__3_spec__10___boxed(
    mut v_00_u03b1_1721_: *mut leanh::LeanObject,
    mut v_ref_1722_: *mut leanh::LeanObject,
    mut v_msg_1723_: *mut leanh::LeanObject,
    mut v_declHint_1724_: *mut leanh::LeanObject,
    mut v___y_1725_: *mut leanh::LeanObject,
    mut v___y_1726_: *mut leanh::LeanObject,
    mut v___y_1727_: *mut leanh::LeanObject,
    mut v___y_1728_: *mut leanh::LeanObject,
    mut v___y_1729_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1730_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1730_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkRecOn_spec__0_spec__0_spec__3_spec__10(v_00_u03b1_1721_, v_ref_1722_, v_msg_1723_, v_declHint_1724_, v___y_1725_, v___y_1726_, v___y_1727_, v___y_1728_);
    leanh::lean_dec(v___y_1728_);
    leanh::lean_dec_ref(v___y_1727_);
    leanh::lean_dec(v___y_1726_);
    leanh::lean_dec_ref(v___y_1725_);
    leanh::lean_dec(v_ref_1722_);
    return v_res_1730_;
}
pub unsafe fn l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkRecOn_spec__0_spec__0_spec__3_spec__10_spec__11_spec__12(
    mut v_msg_1731_: *mut leanh::LeanObject,
    mut v_declHint_1732_: *mut leanh::LeanObject,
    mut v___y_1733_: *mut leanh::LeanObject,
    mut v___y_1734_: *mut leanh::LeanObject,
    mut v___y_1735_: *mut leanh::LeanObject,
    mut v___y_1736_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1738_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1738_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkRecOn_spec__0_spec__0_spec__3_spec__10_spec__11_spec__12___redArg(v_msg_1731_, v_declHint_1732_, v___y_1736_);
    return v___x_1738_;
}
pub unsafe fn l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkRecOn_spec__0_spec__0_spec__3_spec__10_spec__11_spec__12___boxed(
    mut v_msg_1739_: *mut leanh::LeanObject,
    mut v_declHint_1740_: *mut leanh::LeanObject,
    mut v___y_1741_: *mut leanh::LeanObject,
    mut v___y_1742_: *mut leanh::LeanObject,
    mut v___y_1743_: *mut leanh::LeanObject,
    mut v___y_1744_: *mut leanh::LeanObject,
    mut v___y_1745_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1746_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1746_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkRecOn_spec__0_spec__0_spec__3_spec__10_spec__11_spec__12(v_msg_1739_, v_declHint_1740_, v___y_1741_, v___y_1742_, v___y_1743_, v___y_1744_);
    leanh::lean_dec(v___y_1744_);
    leanh::lean_dec_ref(v___y_1743_);
    leanh::lean_dec(v___y_1742_);
    leanh::lean_dec_ref(v___y_1741_);
    return v_res_1746_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkRecOn_spec__0_spec__0_spec__3_spec__10_spec__12(
    mut v_00_u03b1_1747_: *mut leanh::LeanObject,
    mut v_ref_1748_: *mut leanh::LeanObject,
    mut v_msg_1749_: *mut leanh::LeanObject,
    mut v___y_1750_: *mut leanh::LeanObject,
    mut v___y_1751_: *mut leanh::LeanObject,
    mut v___y_1752_: *mut leanh::LeanObject,
    mut v___y_1753_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1755_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1755_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkRecOn_spec__0_spec__0_spec__3_spec__10_spec__12___redArg(v_ref_1748_, v_msg_1749_, v___y_1750_, v___y_1751_, v___y_1752_, v___y_1753_);
    return v___x_1755_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkRecOn_spec__0_spec__0_spec__3_spec__10_spec__12___boxed(
    mut v_00_u03b1_1756_: *mut leanh::LeanObject,
    mut v_ref_1757_: *mut leanh::LeanObject,
    mut v_msg_1758_: *mut leanh::LeanObject,
    mut v___y_1759_: *mut leanh::LeanObject,
    mut v___y_1760_: *mut leanh::LeanObject,
    mut v___y_1761_: *mut leanh::LeanObject,
    mut v___y_1762_: *mut leanh::LeanObject,
    mut v___y_1763_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1764_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1764_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00mkRecOn_spec__0_spec__0_spec__3_spec__10_spec__12(v_00_u03b1_1756_, v_ref_1757_, v_msg_1758_, v___y_1759_, v___y_1760_, v___y_1761_, v___y_1762_);
    leanh::lean_dec(v___y_1762_);
    leanh::lean_dec_ref(v___y_1761_);
    leanh::lean_dec(v___y_1760_);
    leanh::lean_dec_ref(v___y_1759_);
    leanh::lean_dec(v_ref_1757_);
    return v_res_1764_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Meta_Constructions_RecOn(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_AddDecl(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_CompletionName(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Meta_Constructions_RecOn(
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
pub unsafe fn initialize_Lean_Meta_Constructions_RecOn(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_AddDecl(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Lean_Meta_CompletionName(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Constructions_RecOn(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Meta_Constructions_RecOn(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return initialize_Lean_Meta_Constructions_RecOn(builtin);
}