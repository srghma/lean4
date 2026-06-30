// Lean compiler output
// Module: Lean.Meta.GetUnfoldableConst
// Imports: Lean.Meta.Basic
use crate::ffi::{lean_array_get, lean_mk_empty_array_with_capacity, lean_st_ref_get};
use crate::r#gen::Init::MetaTypes::l_Lean_Meta_instBEqTransparencyMode_beq;
use crate::r#gen::Init::Prelude::l_Lean_replaceRef;
use crate::r#gen::Lean::Data::Name::l_Lean_Name_isAnonymous;
use crate::r#gen::Lean::Data::Options::l_Lean_Options_empty;
use crate::r#gen::Lean::Data::PersistentHashMap::l_Lean_PersistentHashMap_mkEmptyEntriesArray;
use crate::r#gen::Lean::Declaration::l_Lean_ConstantInfo_name;
use crate::r#gen::Lean::Environment::{
    l_Lean_AsyncConstantInfo_toConstantInfo, l_Lean_Environment_contains,
    l_Lean_Environment_find_x3f, l_Lean_Environment_findAsync_x3f,
    l_Lean_Environment_getModuleIdxFor_x3f, l_Lean_Environment_header,
    l_Lean_Environment_setExporting, l_Lean_EnvironmentHeader_moduleNames,
};
use crate::r#gen::Lean::Exception::l_Lean_unknownIdentifierMessageTag;
use crate::r#gen::Lean::Message::{
    l_Lean_MessageData_note, l_Lean_MessageData_ofConstName, l_Lean_MessageData_ofName,
    l_Lean_stringToMessageData,
};
use crate::r#gen::Lean::Meta::Basic::{
    initialize_Lean_Meta_Basic, l_Lean_Meta_Context_config, l_Lean_Meta_recordUnfoldAxiom___redArg,
    runtime_initialize_Lean_Meta_Basic,
};
use crate::r#gen::Lean::PrivateName::l_Lean_isPrivateName;
use crate::r#gen::Lean::ReducibilityAttrs::{
    l_Lean_instBEqReducibilityStatus_beq, lean_get_reducibility_status,
};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0_spec__0_spec__1_spec__2___redArg___closed__0_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0_spec__0_spec__1_spec__2___redArg___closed__0: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0_spec__0_spec__1_spec__2___redArg___closed__1_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0_spec__0_spec__1_spec__2___redArg___closed__1: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0_spec__0_spec__1_spec__2___redArg___closed__2_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0_spec__0_spec__1_spec__2___redArg___closed__2: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0_spec__0_spec__1_spec__2___redArg___closed__3_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0_spec__0_spec__1_spec__2___redArg___closed__3: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0_spec__0_spec__1_spec__2___redArg___closed__4_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0_spec__0_spec__1_spec__2___redArg___closed__4: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0_spec__0_spec__1_spec__2___redArg___closed__5_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0_spec__0_spec__1_spec__2___redArg___closed__5: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0_spec__0_spec__1_spec__2___redArg___closed__6_value: leanh::LeanStringObject<24> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 24, m_capacity: 24, m_length: 23, m_data: [65, 32, 112, 114, 105, 118, 97, 116, 101, 32, 100, 101, 99, 108, 97, 114, 97, 116, 105, 111, 110, 32, 96, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0_spec__0_spec__1_spec__2___redArg___closed__6: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0_spec__0_spec__1_spec__2___redArg___closed__6_value) as *mut leanh::LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0_spec__0_spec__1_spec__2___redArg___closed__7_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0_spec__0_spec__1_spec__2___redArg___closed__7: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0_spec__0_spec__1_spec__2___redArg___closed__8_value: leanh::LeanStringObject<79> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 79, m_capacity: 79, m_length: 78, m_data: [96, 32, 40, 102, 114, 111, 109, 32, 116, 104, 101, 32, 99, 117, 114, 114, 101, 110, 116, 32, 109, 111, 100, 117, 108, 101, 41, 32, 101, 120, 105, 115, 116, 115, 32, 98, 117, 116, 32, 119, 111, 117, 108, 100, 32, 110, 101, 101, 100, 32, 116, 111, 32, 98, 101, 32, 112, 117, 98, 108, 105, 99, 32, 116, 111, 32, 97, 99, 99, 101, 115, 115, 32, 104, 101, 114, 101, 46, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0_spec__0_spec__1_spec__2___redArg___closed__8: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0_spec__0_spec__1_spec__2___redArg___closed__8_value) as *mut leanh::LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0_spec__0_spec__1_spec__2___redArg___closed__9_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0_spec__0_spec__1_spec__2___redArg___closed__9: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0_spec__0_spec__1_spec__2___redArg___closed__10_value: leanh::LeanStringObject<23> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 23, m_capacity: 23, m_length: 22, m_data: [65, 32, 112, 117, 98, 108, 105, 99, 32, 100, 101, 99, 108, 97, 114, 97, 116, 105, 111, 110, 32, 96, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0_spec__0_spec__1_spec__2___redArg___closed__10: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0_spec__0_spec__1_spec__2___redArg___closed__10_value) as *mut leanh::LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0_spec__0_spec__1_spec__2___redArg___closed__11_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0_spec__0_spec__1_spec__2___redArg___closed__11: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0_spec__0_spec__1_spec__2___redArg___closed__12_value: leanh::LeanStringObject<68> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 68, m_capacity: 68, m_length: 67, m_data: [96, 32, 101, 120, 105, 115, 116, 115, 32, 98, 117, 116, 32, 105, 115, 32, 105, 109, 112, 111, 114, 116, 101, 100, 32, 112, 114, 105, 118, 97, 116, 101, 108, 121, 59, 32, 99, 111, 110, 115, 105, 100, 101, 114, 32, 97, 100, 100, 105, 110, 103, 32, 96, 112, 117, 98, 108, 105, 99, 32, 105, 109, 112, 111, 114, 116, 32, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0_spec__0_spec__1_spec__2___redArg___closed__12: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0_spec__0_spec__1_spec__2___redArg___closed__12_value) as *mut leanh::LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0_spec__0_spec__1_spec__2___redArg___closed__13_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0_spec__0_spec__1_spec__2___redArg___closed__13: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0_spec__0_spec__1_spec__2___redArg___closed__14_value: leanh::LeanStringObject<3> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [96, 46, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0_spec__0_spec__1_spec__2___redArg___closed__14: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0_spec__0_spec__1_spec__2___redArg___closed__14_value) as *mut leanh::LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0_spec__0_spec__1_spec__2___redArg___closed__15_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0_spec__0_spec__1_spec__2___redArg___closed__15: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0_spec__0_spec__1_spec__2___redArg___closed__16_value: leanh::LeanStringObject<10> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [96, 32, 40, 102, 114, 111, 109, 32, 96, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0_spec__0_spec__1_spec__2___redArg___closed__16: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0_spec__0_spec__1_spec__2___redArg___closed__16_value) as *mut leanh::LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0_spec__0_spec__1_spec__2___redArg___closed__17_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0_spec__0_spec__1_spec__2___redArg___closed__17: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0_spec__0_spec__1_spec__2___redArg___closed__18_value: leanh::LeanStringObject<54> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 54, m_capacity: 54, m_length: 53, m_data: [96, 41, 32, 101, 120, 105, 115, 116, 115, 32, 98, 117, 116, 32, 119, 111, 117, 108, 100, 32, 110, 101, 101, 100, 32, 116, 111, 32, 98, 101, 32, 112, 117, 98, 108, 105, 99, 32, 116, 111, 32, 97, 99, 99, 101, 115, 115, 32, 104, 101, 114, 101, 46, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0_spec__0_spec__1_spec__2___redArg___closed__18: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0_spec__0_spec__1_spec__2___redArg___closed__18_value) as *mut leanh::LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0_spec__0_spec__1_spec__2___redArg___closed__19_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0_spec__0_spec__1_spec__2___redArg___closed__19: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0___redArg___closed__0_value: leanh::LeanStringObject<19> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 19, m_capacity: 19, m_length: 18, m_data: [85, 110, 107, 110, 111, 119, 110, 32, 99, 111, 110, 115, 116, 97, 110, 116, 32, 96, 0]};
static mut l_Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0___redArg___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0___redArg___closed__0_value) as *mut leanh::LeanObject;
static mut l_Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0___redArg___closed__1_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0___redArg___closed__1: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0___redArg___closed__2_value: leanh::LeanStringObject<2> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [96, 0]};
static mut l_Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0___redArg___closed__2: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0___redArg___closed__2_value) as *mut leanh::LeanObject;
static mut l_Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0___redArg___closed__3_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0___redArg___closed__3: *mut leanh::LeanObject = core::ptr::null_mut();
pub unsafe fn l_Lean_getReducibilityStatus___at___00Lean_Meta_canUnfoldDefault_spec__1___redArg(
    mut v_declName_618_: *mut leanh::LeanObject,
    mut v___y_619_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_621_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_622_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_623_: u8 = 0;
    let mut v___x_624_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_625_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_621_ = lean_st_ref_get(v___y_619_);
    v_env_622_ = leanh::lean_ctor_get(v___x_621_, 0);
    leanh::lean_inc_ref(v_env_622_);
    leanh::lean_dec(v___x_621_);
    v___x_623_ = lean_get_reducibility_status(v_env_622_, v_declName_618_);
    v___x_624_ = leanh::lean_box((v___x_623_) as usize);
    v___x_625_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_625_, 0, v___x_624_);
    return v___x_625_;
}
pub unsafe fn l_Lean_getReducibilityStatus___at___00Lean_Meta_canUnfoldDefault_spec__1___redArg___boxed(
    mut v_declName_626_: *mut leanh::LeanObject,
    mut v___y_627_: *mut leanh::LeanObject,
    mut v___y_628_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_629_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_629_ = l_Lean_getReducibilityStatus___at___00Lean_Meta_canUnfoldDefault_spec__1___redArg(
        v_declName_626_,
        v___y_627_,
    );
    leanh::lean_dec(v___y_627_);
    return v_res_629_;
}
pub unsafe fn l_Lean_getReducibilityStatus___at___00Lean_Meta_canUnfoldDefault_spec__1(
    mut v_declName_630_: *mut leanh::LeanObject,
    mut v___y_631_: *mut leanh::LeanObject,
    mut v___y_632_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_634_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_634_ = l_Lean_getReducibilityStatus___at___00Lean_Meta_canUnfoldDefault_spec__1___redArg(
        v_declName_630_,
        v___y_632_,
    );
    return v___x_634_;
}
pub unsafe fn l_Lean_getReducibilityStatus___at___00Lean_Meta_canUnfoldDefault_spec__1___boxed(
    mut v_declName_635_: *mut leanh::LeanObject,
    mut v___y_636_: *mut leanh::LeanObject,
    mut v___y_637_: *mut leanh::LeanObject,
    mut v___y_638_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_639_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_639_ = l_Lean_getReducibilityStatus___at___00Lean_Meta_canUnfoldDefault_spec__1(
        v_declName_635_,
        v___y_636_,
        v___y_637_,
    );
    leanh::lean_dec(v___y_637_);
    leanh::lean_dec_ref(v___y_636_);
    return v_res_639_;
}
pub unsafe fn l_Lean_isIrreducible___at___00Lean_Meta_canUnfoldDefault_spec__0(
    mut v_declName_640_: *mut leanh::LeanObject,
    mut v___y_641_: *mut leanh::LeanObject,
    mut v___y_642_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_644_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_645_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_647_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_648_: u8 = 0;
    let mut v___x_649_: u8 = 0;
    let mut v___x_650_: u8 = 0;
    let mut v___x_651_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_653_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_654_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_655_: u8 = 0;
    let mut v___x_656_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_658_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_659_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_660_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_644_ = l_Lean_getReducibilityStatus___at___00Lean_Meta_canUnfoldDefault_spec__1___redArg(v_declName_640_, v___y_642_);
                v_a_645_ = leanh::lean_ctor_get(v___x_644_, 0);
                v_isSharedCheck_660_ = (!leanh::lean_is_exclusive(v___x_644_)) as u8;
                if v_isSharedCheck_660_ == 0 {
                    v___x_647_ = v___x_644_;
                    v_isShared_648_ = v_isSharedCheck_660_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_a_645_);
                    leanh::lean_dec(v___x_644_);
                    v___x_647_ = leanh::lean_box(0);
                    v_isShared_648_ = v_isSharedCheck_660_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_649_ = (leanh::lean_unbox(v_a_645_) as u8);
                leanh::lean_dec(v_a_645_);
                if v___x_649_ == 2 {
                    v___x_650_ = 1;
                    v___x_651_ = leanh::lean_box((v___x_650_) as usize);
                    if v_isShared_648_ == 0 {
                        leanh::lean_ctor_set(v___x_647_, 0, v___x_651_);
                        v___x_653_ = v___x_647_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_654_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_654_, 0, v___x_651_);
                        v___x_653_ = v_reuseFailAlloc_654_;
                        state = 2;
                        continue;
                    }
                } else {
                    v___x_655_ = 0;
                    v___x_656_ = leanh::lean_box((v___x_655_) as usize);
                    if v_isShared_648_ == 0 {
                        leanh::lean_ctor_set(v___x_647_, 0, v___x_656_);
                        v___x_658_ = v___x_647_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_659_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_659_, 0, v___x_656_);
                        v___x_658_ = v_reuseFailAlloc_659_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_653_;
            }
            3 => {
                return v___x_658_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_isIrreducible___at___00Lean_Meta_canUnfoldDefault_spec__0___boxed(
    mut v_declName_661_: *mut leanh::LeanObject,
    mut v___y_662_: *mut leanh::LeanObject,
    mut v___y_663_: *mut leanh::LeanObject,
    mut v___y_664_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_665_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_665_ = l_Lean_isIrreducible___at___00Lean_Meta_canUnfoldDefault_spec__0(
        v_declName_661_,
        v___y_662_,
        v___y_663_,
    );
    leanh::lean_dec(v___y_663_);
    leanh::lean_dec_ref(v___y_662_);
    return v_res_665_;
}
pub unsafe fn l_Lean_Meta_canUnfoldDefault(
    mut v_cfg_666_: *mut leanh::LeanObject,
    mut v_info_667_: *mut leanh::LeanObject,
    mut v_a_668_: *mut leanh::LeanObject,
    mut v_a_669_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_transparency_671_: u8 = 0;
    let mut v___x_672_: u8 = 0;
    let mut v___x_673_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_674_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_675_: u8 = 0;
    let mut v___x_676_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_677_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_678_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_679_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_680_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_682_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_683_: u8 = 0;
    let mut v___x_684_: u8 = 0;
    let mut v___x_685_: u8 = 0;
    let mut v___x_686_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_688_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_689_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_690_: u8 = 0;
    let mut v___x_691_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_693_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_694_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_695_: u8 = 0;
    let mut v___x_696_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_697_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_698_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_700_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_701_: u8 = 0;
    let mut v___x_702_: u8 = 0;
    let mut v___x_703_: u8 = 0;
    let mut v___x_704_: u8 = 0;
    let mut v___x_705_: u8 = 0;
    let mut v___y_707_: u8 = 0;
    let mut v___x_708_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_710_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_711_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_712_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_714_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_715_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_716_: u8 = 0;
    let mut v___x_717_: u8 = 0;
    let mut v___x_718_: u8 = 0;
    let mut v___x_719_: u8 = 0;
    let mut v___x_720_: u8 = 0;
    let mut v___x_721_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_722_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_723_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_transparency_671_ = leanh::lean_ctor_get_uint8(v_cfg_666_, 9 as u32);
                match v_transparency_671_ {
                    4 => {
                        v___x_672_ = 0;
                        v___x_673_ = leanh::lean_box((v___x_672_) as usize);
                        v___x_674_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v___x_674_, 0, v___x_673_);
                        return v___x_674_;
                    }
                    0 => {
                        v___x_675_ = 1;
                        v___x_676_ = leanh::lean_box((v___x_675_) as usize);
                        v___x_677_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v___x_677_, 0, v___x_676_);
                        return v___x_677_;
                    }
                    1 => {
                        v___x_678_ = l_Lean_ConstantInfo_name(v_info_667_);
                        v___x_679_ =
                            l_Lean_isIrreducible___at___00Lean_Meta_canUnfoldDefault_spec__0(
                                v___x_678_, v_a_668_, v_a_669_,
                            );
                        if leanh::lean_obj_tag(v___x_679_) == 0 {
                            v_a_680_ = leanh::lean_ctor_get(v___x_679_, 0);
                            v_isSharedCheck_695_ =
                                (!leanh::lean_is_exclusive(v___x_679_)) as u8;
                            if v_isSharedCheck_695_ == 0 {
                                v___x_682_ = v___x_679_;
                                v_isShared_683_ = v_isSharedCheck_695_;
                                state = 1;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_680_);
                                leanh::lean_dec(v___x_679_);
                                v___x_682_ = leanh::lean_box(0);
                                v_isShared_683_ = v_isSharedCheck_695_;
                                state = 1;
                                continue;
                            }
                        } else {
                            return v___x_679_;
                        }
                    }
                    _ => {
                        v___x_696_ = l_Lean_ConstantInfo_name(v_info_667_);
                        v___x_697_ = l_Lean_getReducibilityStatus___at___00Lean_Meta_canUnfoldDefault_spec__1___redArg(v___x_696_, v_a_669_);
                        v_a_698_ = leanh::lean_ctor_get(v___x_697_, 0);
                        v_isSharedCheck_723_ = (!leanh::lean_is_exclusive(v___x_697_)) as u8;
                        if v_isSharedCheck_723_ == 0 {
                            v___x_700_ = v___x_697_;
                            v_isShared_701_ = v_isSharedCheck_723_;
                            state = 4;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_698_);
                            leanh::lean_dec(v___x_697_);
                            v___x_700_ = leanh::lean_box(0);
                            v_isShared_701_ = v_isSharedCheck_723_;
                            state = 4;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v___x_684_ = (leanh::lean_unbox(v_a_680_) as u8);
                leanh::lean_dec(v_a_680_);
                if v___x_684_ == 0 {
                    v___x_685_ = 1;
                    v___x_686_ = leanh::lean_box((v___x_685_) as usize);
                    if v_isShared_683_ == 0 {
                        leanh::lean_ctor_set(v___x_682_, 0, v___x_686_);
                        v___x_688_ = v___x_682_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_689_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_689_, 0, v___x_686_);
                        v___x_688_ = v_reuseFailAlloc_689_;
                        state = 2;
                        continue;
                    }
                } else {
                    v___x_690_ = 0;
                    v___x_691_ = leanh::lean_box((v___x_690_) as usize);
                    if v_isShared_683_ == 0 {
                        leanh::lean_ctor_set(v___x_682_, 0, v___x_691_);
                        v___x_693_ = v___x_682_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_694_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_694_, 0, v___x_691_);
                        v___x_693_ = v_reuseFailAlloc_694_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_688_;
            }
            3 => {
                return v___x_693_;
            }
            4 => {
                v___x_702_ = 0;
                v___x_703_ = (leanh::lean_unbox(v_a_698_) as u8);
                v___x_704_ = l_Lean_instBEqReducibilityStatus_beq(v___x_703_, v___x_702_);
                v___x_705_ = 1;
                if v___x_704_ == 0 {
                    v___x_716_ = 3;
                    v___x_717_ =
                        l_Lean_Meta_instBEqTransparencyMode_beq(v_transparency_671_, v___x_716_);
                    if v___x_717_ == 0 {
                        leanh::lean_dec(v_a_698_);
                        v___y_707_ = v___x_717_;
                        state = 5;
                        continue;
                    } else {
                        v___x_718_ = 3;
                        v___x_719_ = (leanh::lean_unbox(v_a_698_) as u8);
                        leanh::lean_dec(v_a_698_);
                        v___x_720_ = l_Lean_instBEqReducibilityStatus_beq(v___x_719_, v___x_718_);
                        v___y_707_ = v___x_720_;
                        state = 5;
                        continue;
                    }
                } else {
                    leanh::lean_del_object(v___x_700_);
                    leanh::lean_dec(v_a_698_);
                    v___x_721_ = leanh::lean_box((v___x_705_) as usize);
                    v___x_722_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_722_, 0, v___x_721_);
                    return v___x_722_;
                }
            }
            5 => {
                if v___y_707_ == 0 {
                    v___x_708_ = leanh::lean_box((v___y_707_) as usize);
                    if v_isShared_701_ == 0 {
                        leanh::lean_ctor_set(v___x_700_, 0, v___x_708_);
                        v___x_710_ = v___x_700_;
                        state = 6;
                        continue;
                    } else {
                        v_reuseFailAlloc_711_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_711_, 0, v___x_708_);
                        v___x_710_ = v_reuseFailAlloc_711_;
                        state = 6;
                        continue;
                    }
                } else {
                    v___x_712_ = leanh::lean_box((v___x_705_) as usize);
                    if v_isShared_701_ == 0 {
                        leanh::lean_ctor_set(v___x_700_, 0, v___x_712_);
                        v___x_714_ = v___x_700_;
                        state = 7;
                        continue;
                    } else {
                        v_reuseFailAlloc_715_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_715_, 0, v___x_712_);
                        v___x_714_ = v_reuseFailAlloc_715_;
                        state = 7;
                        continue;
                    }
                }
            }
            6 => {
                return v___x_710_;
            }
            7 => {
                return v___x_714_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_canUnfoldDefault___boxed(
    mut v_cfg_724_: *mut leanh::LeanObject,
    mut v_info_725_: *mut leanh::LeanObject,
    mut v_a_726_: *mut leanh::LeanObject,
    mut v_a_727_: *mut leanh::LeanObject,
    mut v_a_728_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_729_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_729_ = l_Lean_Meta_canUnfoldDefault(v_cfg_724_, v_info_725_, v_a_726_, v_a_727_);
    leanh::lean_dec(v_a_727_);
    leanh::lean_dec_ref(v_a_726_);
    leanh::lean_dec_ref(v_info_725_);
    leanh::lean_dec_ref(v_cfg_724_);
    return v_res_729_;
}
pub unsafe fn l_Lean_Meta_canUnfold___redArg(
    mut v_info_730_: *mut leanh::LeanObject,
    mut v_a_731_: *mut leanh::LeanObject,
    mut v_a_732_: *mut leanh::LeanObject,
    mut v_a_733_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_canUnfold_x3f_735_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_736_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_canUnfold_x3f_735_ = leanh::lean_ctor_get(v_a_731_, 6);
    v___x_736_ = l_Lean_Meta_Context_config(v_a_731_);
    if leanh::lean_obj_tag(v_canUnfold_x3f_735_) == 1 {
        let mut v_val_737_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_738_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_val_737_ = leanh::lean_ctor_get(v_canUnfold_x3f_735_, 0);
        leanh::lean_inc(v_val_737_);
        leanh::lean_inc(v_a_733_);
        leanh::lean_inc_ref(v_a_732_);
        v___x_738_ = leanh::lean_apply_5(
            v_val_737_,
            v___x_736_,
            v_info_730_,
            v_a_732_,
            v_a_733_,
            leanh::lean_box(0),
        );
        return v___x_738_;
    } else {
        let mut v___x_739_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_739_ = l_Lean_Meta_canUnfoldDefault(v___x_736_, v_info_730_, v_a_732_, v_a_733_);
        leanh::lean_dec_ref(v_info_730_);
        leanh::lean_dec_ref(v___x_736_);
        return v___x_739_;
    }
}
pub unsafe fn l_Lean_Meta_canUnfold___redArg___boxed(
    mut v_info_740_: *mut leanh::LeanObject,
    mut v_a_741_: *mut leanh::LeanObject,
    mut v_a_742_: *mut leanh::LeanObject,
    mut v_a_743_: *mut leanh::LeanObject,
    mut v_a_744_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_745_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_745_ = l_Lean_Meta_canUnfold___redArg(v_info_740_, v_a_741_, v_a_742_, v_a_743_);
    leanh::lean_dec(v_a_743_);
    leanh::lean_dec_ref(v_a_742_);
    leanh::lean_dec_ref(v_a_741_);
    return v_res_745_;
}
pub unsafe fn l_Lean_Meta_canUnfold(
    mut v_info_746_: *mut leanh::LeanObject,
    mut v_a_747_: *mut leanh::LeanObject,
    mut v_a_748_: *mut leanh::LeanObject,
    mut v_a_749_: *mut leanh::LeanObject,
    mut v_a_750_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_752_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_752_ = l_Lean_Meta_canUnfold___redArg(v_info_746_, v_a_747_, v_a_749_, v_a_750_);
    return v___x_752_;
}
pub unsafe fn l_Lean_Meta_canUnfold___boxed(
    mut v_info_753_: *mut leanh::LeanObject,
    mut v_a_754_: *mut leanh::LeanObject,
    mut v_a_755_: *mut leanh::LeanObject,
    mut v_a_756_: *mut leanh::LeanObject,
    mut v_a_757_: *mut leanh::LeanObject,
    mut v_a_758_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_759_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_759_ = l_Lean_Meta_canUnfold(v_info_753_, v_a_754_, v_a_755_, v_a_756_, v_a_757_);
    leanh::lean_dec(v_a_757_);
    leanh::lean_dec_ref(v_a_756_);
    leanh::lean_dec(v_a_755_);
    leanh::lean_dec_ref(v_a_754_);
    return v_res_759_;
}
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0_spec__0_spec__2_spec__4_spec__5(
    mut v_msgData_760_: *mut leanh::LeanObject,
    mut v___y_761_: *mut leanh::LeanObject,
    mut v___y_762_: *mut leanh::LeanObject,
    mut v___y_763_: *mut leanh::LeanObject,
    mut v___y_764_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_766_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_767_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_768_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_769_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_lctx_770_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_771_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_772_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_773_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_774_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_766_ = lean_st_ref_get(v___y_764_);
    v_env_767_ = leanh::lean_ctor_get(v___x_766_, 0);
    leanh::lean_inc_ref(v_env_767_);
    leanh::lean_dec(v___x_766_);
    v___x_768_ = lean_st_ref_get(v___y_762_);
    v_mctx_769_ = leanh::lean_ctor_get(v___x_768_, 0);
    leanh::lean_inc_ref(v_mctx_769_);
    leanh::lean_dec(v___x_768_);
    v_lctx_770_ = leanh::lean_ctor_get(v___y_761_, 2);
    v_options_771_ = leanh::lean_ctor_get(v___y_763_, 2);
    leanh::lean_inc_ref(v_options_771_);
    leanh::lean_inc_ref(v_lctx_770_);
    v___x_772_ = leanh::lean_alloc_ctor(0, 4, (0) as u32);
    leanh::lean_ctor_set(v___x_772_, 0, v_env_767_);
    leanh::lean_ctor_set(v___x_772_, 1, v_mctx_769_);
    leanh::lean_ctor_set(v___x_772_, 2, v_lctx_770_);
    leanh::lean_ctor_set(v___x_772_, 3, v_options_771_);
    v___x_773_ = leanh::lean_alloc_ctor(3, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_773_, 0, v___x_772_);
    leanh::lean_ctor_set(v___x_773_, 1, v_msgData_760_);
    v___x_774_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_774_, 0, v___x_773_);
    return v___x_774_;
}
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0_spec__0_spec__2_spec__4_spec__5___boxed(
    mut v_msgData_775_: *mut leanh::LeanObject,
    mut v___y_776_: *mut leanh::LeanObject,
    mut v___y_777_: *mut leanh::LeanObject,
    mut v___y_778_: *mut leanh::LeanObject,
    mut v___y_779_: *mut leanh::LeanObject,
    mut v___y_780_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_781_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_781_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0_spec__0_spec__2_spec__4_spec__5(v_msgData_775_, v___y_776_, v___y_777_, v___y_778_, v___y_779_);
    leanh::lean_dec(v___y_779_);
    leanh::lean_dec_ref(v___y_778_);
    leanh::lean_dec(v___y_777_);
    leanh::lean_dec_ref(v___y_776_);
    return v_res_781_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0_spec__0_spec__2_spec__4___redArg(
    mut v_msg_782_: *mut leanh::LeanObject,
    mut v___y_783_: *mut leanh::LeanObject,
    mut v___y_784_: *mut leanh::LeanObject,
    mut v___y_785_: *mut leanh::LeanObject,
    mut v___y_786_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_ref_788_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_789_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_790_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_792_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_793_: u8 = 0;
    let mut v___x_794_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_796_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_797_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_798_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ref_788_ = leanh::lean_ctor_get(v___y_785_, 5);
                v___x_789_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0_spec__0_spec__2_spec__4_spec__5(v_msg_782_, v___y_783_, v___y_784_, v___y_785_, v___y_786_);
                v_a_790_ = leanh::lean_ctor_get(v___x_789_, 0);
                v_isSharedCheck_798_ = (!leanh::lean_is_exclusive(v___x_789_)) as u8;
                if v_isSharedCheck_798_ == 0 {
                    v___x_792_ = v___x_789_;
                    v_isShared_793_ = v_isSharedCheck_798_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_a_790_);
                    leanh::lean_dec(v___x_789_);
                    v___x_792_ = leanh::lean_box(0);
                    v_isShared_793_ = v_isSharedCheck_798_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                leanh::lean_inc(v_ref_788_);
                v___x_794_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_794_, 0, v_ref_788_);
                leanh::lean_ctor_set(v___x_794_, 1, v_a_790_);
                if v_isShared_793_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_792_, 1);
                    leanh::lean_ctor_set(v___x_792_, 0, v___x_794_);
                    v___x_796_ = v___x_792_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_797_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_797_, 0, v___x_794_);
                    v___x_796_ = v_reuseFailAlloc_797_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_796_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0_spec__0_spec__2_spec__4___redArg___boxed(
    mut v_msg_799_: *mut leanh::LeanObject,
    mut v___y_800_: *mut leanh::LeanObject,
    mut v___y_801_: *mut leanh::LeanObject,
    mut v___y_802_: *mut leanh::LeanObject,
    mut v___y_803_: *mut leanh::LeanObject,
    mut v___y_804_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_805_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_805_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0_spec__0_spec__2_spec__4___redArg(v_msg_799_, v___y_800_, v___y_801_, v___y_802_, v___y_803_);
    leanh::lean_dec(v___y_803_);
    leanh::lean_dec_ref(v___y_802_);
    leanh::lean_dec(v___y_801_);
    leanh::lean_dec_ref(v___y_800_);
    return v_res_805_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0_spec__0_spec__2___redArg(
    mut v_ref_806_: *mut leanh::LeanObject,
    mut v_msg_807_: *mut leanh::LeanObject,
    mut v___y_808_: *mut leanh::LeanObject,
    mut v___y_809_: *mut leanh::LeanObject,
    mut v___y_810_: *mut leanh::LeanObject,
    mut v___y_811_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_fileName_813_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fileMap_814_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_815_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_currRecDepth_816_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_maxRecDepth_817_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_818_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_currNamespace_819_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_openDecls_820_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_initHeartbeats_821_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_maxHeartbeats_822_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_quotContext_823_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_currMacroScope_824_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_diag_825_: u8 = 0;
    let mut v_cancelTk_x3f_826_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_suppressElabErrors_827_: u8 = 0;
    let mut v_inheritedTraceOptions_828_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_829_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_830_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_831_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_fileName_813_ = leanh::lean_ctor_get(v___y_810_, 0);
    v_fileMap_814_ = leanh::lean_ctor_get(v___y_810_, 1);
    v_options_815_ = leanh::lean_ctor_get(v___y_810_, 2);
    v_currRecDepth_816_ = leanh::lean_ctor_get(v___y_810_, 3);
    v_maxRecDepth_817_ = leanh::lean_ctor_get(v___y_810_, 4);
    v_ref_818_ = leanh::lean_ctor_get(v___y_810_, 5);
    v_currNamespace_819_ = leanh::lean_ctor_get(v___y_810_, 6);
    v_openDecls_820_ = leanh::lean_ctor_get(v___y_810_, 7);
    v_initHeartbeats_821_ = leanh::lean_ctor_get(v___y_810_, 8);
    v_maxHeartbeats_822_ = leanh::lean_ctor_get(v___y_810_, 9);
    v_quotContext_823_ = leanh::lean_ctor_get(v___y_810_, 10);
    v_currMacroScope_824_ = leanh::lean_ctor_get(v___y_810_, 11);
    v_diag_825_ = leanh::lean_ctor_get_uint8(
        v___y_810_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 14) as u32,
    );
    v_cancelTk_x3f_826_ = leanh::lean_ctor_get(v___y_810_, 12);
    v_suppressElabErrors_827_ = leanh::lean_ctor_get_uint8(
        v___y_810_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 14 + 1) as u32,
    );
    v_inheritedTraceOptions_828_ = leanh::lean_ctor_get(v___y_810_, 13);
    v_ref_829_ = l_Lean_replaceRef(v_ref_806_, v_ref_818_);
    leanh::lean_inc_ref(v_inheritedTraceOptions_828_);
    leanh::lean_inc(v_cancelTk_x3f_826_);
    leanh::lean_inc(v_currMacroScope_824_);
    leanh::lean_inc(v_quotContext_823_);
    leanh::lean_inc(v_maxHeartbeats_822_);
    leanh::lean_inc(v_initHeartbeats_821_);
    leanh::lean_inc(v_openDecls_820_);
    leanh::lean_inc(v_currNamespace_819_);
    leanh::lean_inc(v_maxRecDepth_817_);
    leanh::lean_inc(v_currRecDepth_816_);
    leanh::lean_inc_ref(v_options_815_);
    leanh::lean_inc_ref(v_fileMap_814_);
    leanh::lean_inc_ref(v_fileName_813_);
    v___x_830_ = leanh::lean_alloc_ctor(0, 14, (2) as u32);
    leanh::lean_ctor_set(v___x_830_, 0, v_fileName_813_);
    leanh::lean_ctor_set(v___x_830_, 1, v_fileMap_814_);
    leanh::lean_ctor_set(v___x_830_, 2, v_options_815_);
    leanh::lean_ctor_set(v___x_830_, 3, v_currRecDepth_816_);
    leanh::lean_ctor_set(v___x_830_, 4, v_maxRecDepth_817_);
    leanh::lean_ctor_set(v___x_830_, 5, v_ref_829_);
    leanh::lean_ctor_set(v___x_830_, 6, v_currNamespace_819_);
    leanh::lean_ctor_set(v___x_830_, 7, v_openDecls_820_);
    leanh::lean_ctor_set(v___x_830_, 8, v_initHeartbeats_821_);
    leanh::lean_ctor_set(v___x_830_, 9, v_maxHeartbeats_822_);
    leanh::lean_ctor_set(v___x_830_, 10, v_quotContext_823_);
    leanh::lean_ctor_set(v___x_830_, 11, v_currMacroScope_824_);
    leanh::lean_ctor_set(v___x_830_, 12, v_cancelTk_x3f_826_);
    leanh::lean_ctor_set(v___x_830_, 13, v_inheritedTraceOptions_828_);
    leanh::lean_ctor_set_uint8(
        v___x_830_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 14) as u32,
        v_diag_825_,
    );
    leanh::lean_ctor_set_uint8(
        v___x_830_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 14 + 1) as u32,
        v_suppressElabErrors_827_,
    );
    v___x_831_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0_spec__0_spec__2_spec__4___redArg(v_msg_807_, v___y_808_, v___y_809_, v___x_830_, v___y_811_);
    leanh::lean_dec_ref_known(v___x_830_, 14);
    return v___x_831_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0_spec__0_spec__2___redArg___boxed(
    mut v_ref_832_: *mut leanh::LeanObject,
    mut v_msg_833_: *mut leanh::LeanObject,
    mut v___y_834_: *mut leanh::LeanObject,
    mut v___y_835_: *mut leanh::LeanObject,
    mut v___y_836_: *mut leanh::LeanObject,
    mut v___y_837_: *mut leanh::LeanObject,
    mut v___y_838_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_839_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_839_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0_spec__0_spec__2___redArg(v_ref_832_, v_msg_833_, v___y_834_, v___y_835_, v___y_836_, v___y_837_);
    leanh::lean_dec(v___y_837_);
    leanh::lean_dec_ref(v___y_836_);
    leanh::lean_dec(v___y_835_);
    leanh::lean_dec_ref(v___y_834_);
    leanh::lean_dec(v_ref_832_);
    return v_res_839_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0_spec__0_spec__1_spec__2___redArg___closed__0()
-> *mut leanh::LeanObject {
    let mut v___x_840_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_840_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(
        leanh::lean_box(0),
        leanh::lean_box(0),
    );
    return v___x_840_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0_spec__0_spec__1_spec__2___redArg___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_841_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_842_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_841_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0_spec__0_spec__1_spec__2___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0_spec__0_spec__1_spec__2___redArg___closed__0_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0_spec__0_spec__1_spec__2___redArg___closed__0);
    v___x_842_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_842_, 0, v___x_841_);
    return v___x_842_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0_spec__0_spec__1_spec__2___redArg___closed__2()
-> *mut leanh::LeanObject {
    let mut v___x_843_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_844_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_845_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_843_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0_spec__0_spec__1_spec__2___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0_spec__0_spec__1_spec__2___redArg___closed__1_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0_spec__0_spec__1_spec__2___redArg___closed__1);
    v___x_844_ = leanh::lean_unsigned_to_nat(0);
    v___x_845_ = leanh::lean_alloc_ctor(0, 10, (0) as u32);
    leanh::lean_ctor_set(v___x_845_, 0, v___x_844_);
    leanh::lean_ctor_set(v___x_845_, 1, v___x_844_);
    leanh::lean_ctor_set(v___x_845_, 2, v___x_844_);
    leanh::lean_ctor_set(v___x_845_, 3, v___x_844_);
    leanh::lean_ctor_set(v___x_845_, 4, v___x_843_);
    leanh::lean_ctor_set(v___x_845_, 5, v___x_843_);
    leanh::lean_ctor_set(v___x_845_, 6, v___x_843_);
    leanh::lean_ctor_set(v___x_845_, 7, v___x_843_);
    leanh::lean_ctor_set(v___x_845_, 8, v___x_843_);
    leanh::lean_ctor_set(v___x_845_, 9, v___x_843_);
    return v___x_845_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0_spec__0_spec__1_spec__2___redArg___closed__3()
-> *mut leanh::LeanObject {
    let mut v___x_846_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_847_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_848_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_846_ = leanh::lean_unsigned_to_nat(32);
    v___x_847_ = lean_mk_empty_array_with_capacity(v___x_846_);
    v___x_848_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_848_, 0, v___x_847_);
    return v___x_848_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0_spec__0_spec__1_spec__2___redArg___closed__4()
-> *mut leanh::LeanObject {
    let mut v___x_849_: usize = 0;
    let mut v___x_850_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_851_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_852_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_853_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_854_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_849_ = 5usize;
    v___x_850_ = leanh::lean_unsigned_to_nat(0);
    v___x_851_ = leanh::lean_unsigned_to_nat(32);
    v___x_852_ = lean_mk_empty_array_with_capacity(v___x_851_);
    v___x_853_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0_spec__0_spec__1_spec__2___redArg___closed__3), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0_spec__0_spec__1_spec__2___redArg___closed__3_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0_spec__0_spec__1_spec__2___redArg___closed__3);
    v___x_854_ = leanh::lean_alloc_ctor(0, 4, (core::mem::size_of::<usize>() * 1) as u32);
    leanh::lean_ctor_set(v___x_854_, 0, v___x_853_);
    leanh::lean_ctor_set(v___x_854_, 1, v___x_852_);
    leanh::lean_ctor_set(v___x_854_, 2, v___x_850_);
    leanh::lean_ctor_set(v___x_854_, 3, v___x_850_);
    leanh::lean_ctor_set_usize(v___x_854_, 4, v___x_849_);
    return v___x_854_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0_spec__0_spec__1_spec__2___redArg___closed__5()
-> *mut leanh::LeanObject {
    let mut v___x_855_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_856_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_857_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_858_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_855_ = leanh::lean_box(1);
    v___x_856_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0_spec__0_spec__1_spec__2___redArg___closed__4), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0_spec__0_spec__1_spec__2___redArg___closed__4_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0_spec__0_spec__1_spec__2___redArg___closed__4);
    v___x_857_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0_spec__0_spec__1_spec__2___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0_spec__0_spec__1_spec__2___redArg___closed__1_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0_spec__0_spec__1_spec__2___redArg___closed__1);
    v___x_858_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_858_, 0, v___x_857_);
    leanh::lean_ctor_set(v___x_858_, 1, v___x_856_);
    leanh::lean_ctor_set(v___x_858_, 2, v___x_855_);
    return v___x_858_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0_spec__0_spec__1_spec__2___redArg___closed__7()
-> *mut leanh::LeanObject {
    let mut v___x_860_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_861_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_860_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0_spec__0_spec__1_spec__2___redArg___closed__6;
    v___x_861_ = l_Lean_stringToMessageData(v___x_860_);
    return v___x_861_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0_spec__0_spec__1_spec__2___redArg___closed__9()
-> *mut leanh::LeanObject {
    let mut v___x_863_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_864_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_863_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0_spec__0_spec__1_spec__2___redArg___closed__8;
    v___x_864_ = l_Lean_stringToMessageData(v___x_863_);
    return v___x_864_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0_spec__0_spec__1_spec__2___redArg___closed__11()
-> *mut leanh::LeanObject {
    let mut v___x_866_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_867_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_866_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0_spec__0_spec__1_spec__2___redArg___closed__10;
    v___x_867_ = l_Lean_stringToMessageData(v___x_866_);
    return v___x_867_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0_spec__0_spec__1_spec__2___redArg___closed__13()
-> *mut leanh::LeanObject {
    let mut v___x_869_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_870_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_869_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0_spec__0_spec__1_spec__2___redArg___closed__12;
    v___x_870_ = l_Lean_stringToMessageData(v___x_869_);
    return v___x_870_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0_spec__0_spec__1_spec__2___redArg___closed__15()
-> *mut leanh::LeanObject {
    let mut v___x_872_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_873_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_872_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0_spec__0_spec__1_spec__2___redArg___closed__14;
    v___x_873_ = l_Lean_stringToMessageData(v___x_872_);
    return v___x_873_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0_spec__0_spec__1_spec__2___redArg___closed__17()
-> *mut leanh::LeanObject {
    let mut v___x_875_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_876_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_875_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0_spec__0_spec__1_spec__2___redArg___closed__16;
    v___x_876_ = l_Lean_stringToMessageData(v___x_875_);
    return v___x_876_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0_spec__0_spec__1_spec__2___redArg___closed__19()
-> *mut leanh::LeanObject {
    let mut v___x_878_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_879_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_878_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0_spec__0_spec__1_spec__2___redArg___closed__18;
    v___x_879_ = l_Lean_stringToMessageData(v___x_878_);
    return v___x_879_;
}
pub unsafe fn l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0_spec__0_spec__1_spec__2___redArg(
    mut v_msg_880_: *mut leanh::LeanObject,
    mut v_declHint_881_: *mut leanh::LeanObject,
    mut v___y_882_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_884_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_885_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_886_: u8 = 0;
    let mut v_isExporting_887_: u8 = 0;
    let mut v___x_888_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_889_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_890_: u8 = 0;
    let mut v___x_891_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_892_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_893_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_894_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_895_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_896_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_c_897_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_898_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_899_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_900_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_901_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_902_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_903_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_904_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_905_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_906_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_908_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_909_: u8 = 0;
    let mut v___x_910_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_911_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_912_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_mod_913_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_914_: u8 = 0;
    let mut v___x_915_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_916_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_917_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_918_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_919_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_920_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_921_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_922_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_923_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_924_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_926_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_927_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_928_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_929_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_930_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_931_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_932_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_933_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_934_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_935_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_936_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_937_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_939_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_940_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_941_: u8 = 0;
    let mut v___x_942_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_884_ = lean_st_ref_get(v___y_882_);
                v_env_885_ = leanh::lean_ctor_get(v___x_884_, 0);
                leanh::lean_inc_ref(v_env_885_);
                leanh::lean_dec(v___x_884_);
                v___x_886_ = l_Lean_Name_isAnonymous(v_declHint_881_);
                if v___x_886_ == 0 {
                    v_isExporting_887_ = leanh::lean_ctor_get_uint8(
                        v_env_885_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 8) as u32,
                    );
                    if v_isExporting_887_ == 0 {
                        leanh::lean_dec_ref(v_env_885_);
                        leanh::lean_dec(v_declHint_881_);
                        v___x_888_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v___x_888_, 0, v_msg_880_);
                        return v___x_888_;
                    } else {
                        leanh::lean_inc_ref(v_env_885_);
                        v___x_889_ = l_Lean_Environment_setExporting(v_env_885_, v___x_886_);
                        leanh::lean_inc(v_declHint_881_);
                        leanh::lean_inc_ref(v___x_889_);
                        v___x_890_ = l_Lean_Environment_contains(
                            v___x_889_,
                            v_declHint_881_,
                            v_isExporting_887_,
                        );
                        if v___x_890_ == 0 {
                            leanh::lean_dec_ref(v___x_889_);
                            leanh::lean_dec_ref(v_env_885_);
                            leanh::lean_dec(v_declHint_881_);
                            v___x_891_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                            leanh::lean_ctor_set(v___x_891_, 0, v_msg_880_);
                            return v___x_891_;
                        } else {
                            v___x_892_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0_spec__0_spec__1_spec__2___redArg___closed__2), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0_spec__0_spec__1_spec__2___redArg___closed__2_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0_spec__0_spec__1_spec__2___redArg___closed__2);
                            v___x_893_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0_spec__0_spec__1_spec__2___redArg___closed__5), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0_spec__0_spec__1_spec__2___redArg___closed__5_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0_spec__0_spec__1_spec__2___redArg___closed__5);
                            v___x_894_ = l_Lean_Options_empty;
                            v___x_895_ = leanh::lean_alloc_ctor(0, 4, (0) as u32);
                            leanh::lean_ctor_set(v___x_895_, 0, v___x_889_);
                            leanh::lean_ctor_set(v___x_895_, 1, v___x_892_);
                            leanh::lean_ctor_set(v___x_895_, 2, v___x_893_);
                            leanh::lean_ctor_set(v___x_895_, 3, v___x_894_);
                            leanh::lean_inc(v_declHint_881_);
                            v___x_896_ =
                                l_Lean_MessageData_ofConstName(v_declHint_881_, v___x_886_);
                            v_c_897_ = leanh::lean_alloc_ctor(3, 2, (0) as u32);
                            leanh::lean_ctor_set(v_c_897_, 0, v___x_895_);
                            leanh::lean_ctor_set(v_c_897_, 1, v___x_896_);
                            v___x_898_ =
                                l_Lean_Environment_getModuleIdxFor_x3f(v_env_885_, v_declHint_881_);
                            if leanh::lean_obj_tag(v___x_898_) == 0 {
                                leanh::lean_dec_ref(v_env_885_);
                                leanh::lean_dec(v_declHint_881_);
                                v___x_899_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0_spec__0_spec__1_spec__2___redArg___closed__7), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0_spec__0_spec__1_spec__2___redArg___closed__7_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0_spec__0_spec__1_spec__2___redArg___closed__7);
                                v___x_900_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                                leanh::lean_ctor_set(v___x_900_, 0, v___x_899_);
                                leanh::lean_ctor_set(v___x_900_, 1, v_c_897_);
                                v___x_901_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0_spec__0_spec__1_spec__2___redArg___closed__9), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0_spec__0_spec__1_spec__2___redArg___closed__9_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0_spec__0_spec__1_spec__2___redArg___closed__9);
                                v___x_902_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                                leanh::lean_ctor_set(v___x_902_, 0, v___x_900_);
                                leanh::lean_ctor_set(v___x_902_, 1, v___x_901_);
                                v___x_903_ = l_Lean_MessageData_note(v___x_902_);
                                v___x_904_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                                leanh::lean_ctor_set(v___x_904_, 0, v_msg_880_);
                                leanh::lean_ctor_set(v___x_904_, 1, v___x_903_);
                                v___x_905_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                                leanh::lean_ctor_set(v___x_905_, 0, v___x_904_);
                                return v___x_905_;
                            } else {
                                v_val_906_ = leanh::lean_ctor_get(v___x_898_, 0);
                                v_isSharedCheck_941_ =
                                    (!leanh::lean_is_exclusive(v___x_898_)) as u8;
                                if v_isSharedCheck_941_ == 0 {
                                    v___x_908_ = v___x_898_;
                                    v_isShared_909_ = v_isSharedCheck_941_;
                                    state = 1;
                                    continue;
                                } else {
                                    leanh::lean_inc(v_val_906_);
                                    leanh::lean_dec(v___x_898_);
                                    v___x_908_ = leanh::lean_box(0);
                                    v_isShared_909_ = v_isSharedCheck_941_;
                                    state = 1;
                                    continue;
                                }
                            }
                        }
                    }
                } else {
                    leanh::lean_dec_ref(v_env_885_);
                    leanh::lean_dec(v_declHint_881_);
                    v___x_942_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_942_, 0, v_msg_880_);
                    return v___x_942_;
                }
            }
            1 => {
                v___x_910_ = leanh::lean_box(0);
                v___x_911_ = l_Lean_Environment_header(v_env_885_);
                leanh::lean_dec_ref(v_env_885_);
                v___x_912_ = l_Lean_EnvironmentHeader_moduleNames(v___x_911_);
                v_mod_913_ = lean_array_get(v___x_910_, v___x_912_, v_val_906_);
                leanh::lean_dec(v_val_906_);
                leanh::lean_dec_ref(v___x_912_);
                v___x_914_ = l_Lean_isPrivateName(v_declHint_881_);
                leanh::lean_dec(v_declHint_881_);
                if v___x_914_ == 0 {
                    v___x_915_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0_spec__0_spec__1_spec__2___redArg___closed__11), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0_spec__0_spec__1_spec__2___redArg___closed__11_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0_spec__0_spec__1_spec__2___redArg___closed__11);
                    v___x_916_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_916_, 0, v___x_915_);
                    leanh::lean_ctor_set(v___x_916_, 1, v_c_897_);
                    v___x_917_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0_spec__0_spec__1_spec__2___redArg___closed__13), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0_spec__0_spec__1_spec__2___redArg___closed__13_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0_spec__0_spec__1_spec__2___redArg___closed__13);
                    v___x_918_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_918_, 0, v___x_916_);
                    leanh::lean_ctor_set(v___x_918_, 1, v___x_917_);
                    v___x_919_ = l_Lean_MessageData_ofName(v_mod_913_);
                    v___x_920_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_920_, 0, v___x_918_);
                    leanh::lean_ctor_set(v___x_920_, 1, v___x_919_);
                    v___x_921_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0_spec__0_spec__1_spec__2___redArg___closed__15), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0_spec__0_spec__1_spec__2___redArg___closed__15_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0_spec__0_spec__1_spec__2___redArg___closed__15);
                    v___x_922_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_922_, 0, v___x_920_);
                    leanh::lean_ctor_set(v___x_922_, 1, v___x_921_);
                    v___x_923_ = l_Lean_MessageData_note(v___x_922_);
                    v___x_924_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_924_, 0, v_msg_880_);
                    leanh::lean_ctor_set(v___x_924_, 1, v___x_923_);
                    if v_isShared_909_ == 0 {
                        leanh::lean_ctor_set_tag(v___x_908_, 0);
                        leanh::lean_ctor_set(v___x_908_, 0, v___x_924_);
                        v___x_926_ = v___x_908_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_927_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_927_, 0, v___x_924_);
                        v___x_926_ = v_reuseFailAlloc_927_;
                        state = 2;
                        continue;
                    }
                } else {
                    v___x_928_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0_spec__0_spec__1_spec__2___redArg___closed__7), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0_spec__0_spec__1_spec__2___redArg___closed__7_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0_spec__0_spec__1_spec__2___redArg___closed__7);
                    v___x_929_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_929_, 0, v___x_928_);
                    leanh::lean_ctor_set(v___x_929_, 1, v_c_897_);
                    v___x_930_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0_spec__0_spec__1_spec__2___redArg___closed__17), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0_spec__0_spec__1_spec__2___redArg___closed__17_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0_spec__0_spec__1_spec__2___redArg___closed__17);
                    v___x_931_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_931_, 0, v___x_929_);
                    leanh::lean_ctor_set(v___x_931_, 1, v___x_930_);
                    v___x_932_ = l_Lean_MessageData_ofName(v_mod_913_);
                    v___x_933_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_933_, 0, v___x_931_);
                    leanh::lean_ctor_set(v___x_933_, 1, v___x_932_);
                    v___x_934_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0_spec__0_spec__1_spec__2___redArg___closed__19), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0_spec__0_spec__1_spec__2___redArg___closed__19_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0_spec__0_spec__1_spec__2___redArg___closed__19);
                    v___x_935_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_935_, 0, v___x_933_);
                    leanh::lean_ctor_set(v___x_935_, 1, v___x_934_);
                    v___x_936_ = l_Lean_MessageData_note(v___x_935_);
                    v___x_937_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_937_, 0, v_msg_880_);
                    leanh::lean_ctor_set(v___x_937_, 1, v___x_936_);
                    if v_isShared_909_ == 0 {
                        leanh::lean_ctor_set_tag(v___x_908_, 0);
                        leanh::lean_ctor_set(v___x_908_, 0, v___x_937_);
                        v___x_939_ = v___x_908_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_940_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_940_, 0, v___x_937_);
                        v___x_939_ = v_reuseFailAlloc_940_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_926_;
            }
            3 => {
                return v___x_939_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0_spec__0_spec__1_spec__2___redArg___boxed(
    mut v_msg_943_: *mut leanh::LeanObject,
    mut v_declHint_944_: *mut leanh::LeanObject,
    mut v___y_945_: *mut leanh::LeanObject,
    mut v___y_946_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_947_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_947_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0_spec__0_spec__1_spec__2___redArg(v_msg_943_, v_declHint_944_, v___y_945_);
    leanh::lean_dec(v___y_945_);
    return v_res_947_;
}
pub unsafe fn l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0_spec__0_spec__1(
    mut v_msg_948_: *mut leanh::LeanObject,
    mut v_declHint_949_: *mut leanh::LeanObject,
    mut v___y_950_: *mut leanh::LeanObject,
    mut v___y_951_: *mut leanh::LeanObject,
    mut v___y_952_: *mut leanh::LeanObject,
    mut v___y_953_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_955_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_956_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_958_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_959_: u8 = 0;
    let mut v___x_960_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_961_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_963_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_964_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_965_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_955_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0_spec__0_spec__1_spec__2___redArg(v_msg_948_, v_declHint_949_, v___y_953_);
                v_a_956_ = leanh::lean_ctor_get(v___x_955_, 0);
                v_isSharedCheck_965_ = (!leanh::lean_is_exclusive(v___x_955_)) as u8;
                if v_isSharedCheck_965_ == 0 {
                    v___x_958_ = v___x_955_;
                    v_isShared_959_ = v_isSharedCheck_965_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_a_956_);
                    leanh::lean_dec(v___x_955_);
                    v___x_958_ = leanh::lean_box(0);
                    v_isShared_959_ = v_isSharedCheck_965_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_960_ = l_Lean_unknownIdentifierMessageTag;
                v___x_961_ = leanh::lean_alloc_ctor(8, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_961_, 0, v___x_960_);
                leanh::lean_ctor_set(v___x_961_, 1, v_a_956_);
                if v_isShared_959_ == 0 {
                    leanh::lean_ctor_set(v___x_958_, 0, v___x_961_);
                    v___x_963_ = v___x_958_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_964_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_964_, 0, v___x_961_);
                    v___x_963_ = v_reuseFailAlloc_964_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_963_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0_spec__0_spec__1___boxed(
    mut v_msg_966_: *mut leanh::LeanObject,
    mut v_declHint_967_: *mut leanh::LeanObject,
    mut v___y_968_: *mut leanh::LeanObject,
    mut v___y_969_: *mut leanh::LeanObject,
    mut v___y_970_: *mut leanh::LeanObject,
    mut v___y_971_: *mut leanh::LeanObject,
    mut v___y_972_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_973_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_973_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0_spec__0_spec__1(v_msg_966_, v_declHint_967_, v___y_968_, v___y_969_, v___y_970_, v___y_971_);
    leanh::lean_dec(v___y_971_);
    leanh::lean_dec_ref(v___y_970_);
    leanh::lean_dec(v___y_969_);
    leanh::lean_dec_ref(v___y_968_);
    return v_res_973_;
}
pub unsafe fn l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0_spec__0___redArg(
    mut v_ref_974_: *mut leanh::LeanObject,
    mut v_msg_975_: *mut leanh::LeanObject,
    mut v_declHint_976_: *mut leanh::LeanObject,
    mut v___y_977_: *mut leanh::LeanObject,
    mut v___y_978_: *mut leanh::LeanObject,
    mut v___y_979_: *mut leanh::LeanObject,
    mut v___y_980_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_982_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_983_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_984_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_982_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0_spec__0_spec__1(v_msg_975_, v_declHint_976_, v___y_977_, v___y_978_, v___y_979_, v___y_980_);
    v_a_983_ = leanh::lean_ctor_get(v___x_982_, 0);
    leanh::lean_inc(v_a_983_);
    leanh::lean_dec_ref(v___x_982_);
    v___x_984_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0_spec__0_spec__2___redArg(v_ref_974_, v_a_983_, v___y_977_, v___y_978_, v___y_979_, v___y_980_);
    return v___x_984_;
}
pub unsafe fn l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0_spec__0___redArg___boxed(
    mut v_ref_985_: *mut leanh::LeanObject,
    mut v_msg_986_: *mut leanh::LeanObject,
    mut v_declHint_987_: *mut leanh::LeanObject,
    mut v___y_988_: *mut leanh::LeanObject,
    mut v___y_989_: *mut leanh::LeanObject,
    mut v___y_990_: *mut leanh::LeanObject,
    mut v___y_991_: *mut leanh::LeanObject,
    mut v___y_992_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_993_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_993_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0_spec__0___redArg(v_ref_985_, v_msg_986_, v_declHint_987_, v___y_988_, v___y_989_, v___y_990_, v___y_991_);
    leanh::lean_dec(v___y_991_);
    leanh::lean_dec_ref(v___y_990_);
    leanh::lean_dec(v___y_989_);
    leanh::lean_dec_ref(v___y_988_);
    leanh::lean_dec(v_ref_985_);
    return v_res_993_;
}
pub unsafe fn _init_l_Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0___redArg___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_995_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_996_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_995_ = l_Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0___redArg___closed__0;
    v___x_996_ = l_Lean_stringToMessageData(v___x_995_);
    return v___x_996_;
}
pub unsafe fn _init_l_Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0___redArg___closed__3()
-> *mut leanh::LeanObject {
    let mut v___x_998_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_999_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_998_ = l_Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0___redArg___closed__2;
    v___x_999_ = l_Lean_stringToMessageData(v___x_998_);
    return v___x_999_;
}
pub unsafe fn l_Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0___redArg(
    mut v_ref_1000_: *mut leanh::LeanObject,
    mut v_constName_1001_: *mut leanh::LeanObject,
    mut v___y_1002_: *mut leanh::LeanObject,
    mut v___y_1003_: *mut leanh::LeanObject,
    mut v___y_1004_: *mut leanh::LeanObject,
    mut v___y_1005_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1007_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1008_: u8 = 0;
    let mut v___x_1009_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1010_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1011_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1012_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1013_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1007_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0___redArg___closed__1_once), _init_l_Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0___redArg___closed__1);
    v___x_1008_ = 0;
    leanh::lean_inc(v_constName_1001_);
    v___x_1009_ = l_Lean_MessageData_ofConstName(v_constName_1001_, v___x_1008_);
    v___x_1010_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1010_, 0, v___x_1007_);
    leanh::lean_ctor_set(v___x_1010_, 1, v___x_1009_);
    v___x_1011_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0___redArg___closed__3), core::ptr::addr_of_mut!(l_Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0___redArg___closed__3_once), _init_l_Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0___redArg___closed__3);
    v___x_1012_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1012_, 0, v___x_1010_);
    leanh::lean_ctor_set(v___x_1012_, 1, v___x_1011_);
    v___x_1013_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0_spec__0___redArg(v_ref_1000_, v___x_1012_, v_constName_1001_, v___y_1002_, v___y_1003_, v___y_1004_, v___y_1005_);
    return v___x_1013_;
}
pub unsafe fn l_Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0___redArg___boxed(
    mut v_ref_1014_: *mut leanh::LeanObject,
    mut v_constName_1015_: *mut leanh::LeanObject,
    mut v___y_1016_: *mut leanh::LeanObject,
    mut v___y_1017_: *mut leanh::LeanObject,
    mut v___y_1018_: *mut leanh::LeanObject,
    mut v___y_1019_: *mut leanh::LeanObject,
    mut v___y_1020_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1021_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1021_ =
        l_Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0___redArg(
            v_ref_1014_,
            v_constName_1015_,
            v___y_1016_,
            v___y_1017_,
            v___y_1018_,
            v___y_1019_,
        );
    leanh::lean_dec(v___y_1019_);
    leanh::lean_dec_ref(v___y_1018_);
    leanh::lean_dec(v___y_1017_);
    leanh::lean_dec_ref(v___y_1016_);
    leanh::lean_dec(v_ref_1014_);
    return v_res_1021_;
}
pub unsafe fn l_Lean_Meta_getUnfoldableConst_x3f(
    mut v_constName_1022_: *mut leanh::LeanObject,
    mut v_a_1023_: *mut leanh::LeanObject,
    mut v_a_1024_: *mut leanh::LeanObject,
    mut v_a_1025_: *mut leanh::LeanObject,
    mut v_a_1026_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1028_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_1029_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1030_: u8 = 0;
    let mut v___x_1031_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1032_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1034_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1035_: u8 = 0;
    let mut v_kind_1036_: u8 = 0;
    let mut v___x_1037_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1038_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1039_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1040_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1041_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1043_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1044_: u8 = 0;
    let mut v___x_1045_: u8 = 0;
    let mut v___x_1046_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1048_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1049_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1051_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1053_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1054_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1055_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1056_: u8 = 0;
    let mut v_a_1057_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1059_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1060_: u8 = 0;
    let mut v___x_1062_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1063_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1064_: u8 = 0;
    let mut v___x_1065_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1066_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1067_: u8 = 0;
    let mut v_ref_1068_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1069_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1028_ = lean_st_ref_get(v_a_1026_);
                v_env_1029_ = leanh::lean_ctor_get(v___x_1028_, 0);
                leanh::lean_inc_ref(v_env_1029_);
                leanh::lean_dec(v___x_1028_);
                v___x_1030_ = 0;
                leanh::lean_inc(v_constName_1022_);
                v___x_1031_ =
                    l_Lean_Environment_findAsync_x3f(v_env_1029_, v_constName_1022_, v___x_1030_);
                if leanh::lean_obj_tag(v___x_1031_) == 1 {
                    leanh::lean_dec(v_constName_1022_);
                    v_val_1032_ = leanh::lean_ctor_get(v___x_1031_, 0);
                    v_isSharedCheck_1067_ = (!leanh::lean_is_exclusive(v___x_1031_)) as u8;
                    if v_isSharedCheck_1067_ == 0 {
                        v___x_1034_ = v___x_1031_;
                        v_isShared_1035_ = v_isSharedCheck_1067_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_val_1032_);
                        leanh::lean_dec(v___x_1031_);
                        v___x_1034_ = leanh::lean_box(0);
                        v_isShared_1035_ = v_isSharedCheck_1067_;
                        state = 1;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v___x_1031_);
                    v_ref_1068_ = leanh::lean_ctor_get(v_a_1025_, 5);
                    v___x_1069_ = l_Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0___redArg(v_ref_1068_, v_constName_1022_, v_a_1023_, v_a_1024_, v_a_1025_, v_a_1026_);
                    return v___x_1069_;
                }
            }
            1 => {
                v_kind_1036_ = leanh::lean_ctor_get_uint8(
                    v_val_1032_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 3) as u32,
                );
                match v_kind_1036_ {
                    1 => {
                        leanh::lean_del_object(v___x_1034_);
                        leanh::lean_dec(v_val_1032_);
                        v___x_1037_ = leanh::lean_box(0);
                        v___x_1038_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v___x_1038_, 0, v___x_1037_);
                        return v___x_1038_;
                    }
                    0 => {
                        v___x_1039_ = l_Lean_AsyncConstantInfo_toConstantInfo(v_val_1032_);
                        leanh::lean_inc_ref(v___x_1039_);
                        v___x_1040_ = l_Lean_Meta_canUnfold___redArg(
                            v___x_1039_,
                            v_a_1023_,
                            v_a_1025_,
                            v_a_1026_,
                        );
                        if leanh::lean_obj_tag(v___x_1040_) == 0 {
                            v_a_1041_ = leanh::lean_ctor_get(v___x_1040_, 0);
                            v_isSharedCheck_1056_ =
                                (!leanh::lean_is_exclusive(v___x_1040_)) as u8;
                            if v_isSharedCheck_1056_ == 0 {
                                v___x_1043_ = v___x_1040_;
                                v_isShared_1044_ = v_isSharedCheck_1056_;
                                state = 2;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_1041_);
                                leanh::lean_dec(v___x_1040_);
                                v___x_1043_ = leanh::lean_box(0);
                                v_isShared_1044_ = v_isSharedCheck_1056_;
                                state = 2;
                                continue;
                            }
                        } else {
                            leanh::lean_dec_ref(v___x_1039_);
                            leanh::lean_del_object(v___x_1034_);
                            v_a_1057_ = leanh::lean_ctor_get(v___x_1040_, 0);
                            v_isSharedCheck_1064_ =
                                (!leanh::lean_is_exclusive(v___x_1040_)) as u8;
                            if v_isSharedCheck_1064_ == 0 {
                                v___x_1059_ = v___x_1040_;
                                v_isShared_1060_ = v_isSharedCheck_1064_;
                                state = 6;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_1057_);
                                leanh::lean_dec(v___x_1040_);
                                v___x_1059_ = leanh::lean_box(0);
                                v_isShared_1060_ = v_isSharedCheck_1064_;
                                state = 6;
                                continue;
                            }
                        }
                    }
                    _ => {
                        leanh::lean_del_object(v___x_1034_);
                        leanh::lean_dec(v_val_1032_);
                        v___x_1065_ = leanh::lean_box(0);
                        v___x_1066_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v___x_1066_, 0, v___x_1065_);
                        return v___x_1066_;
                    }
                }
            }
            2 => {
                v___x_1045_ = (leanh::lean_unbox(v_a_1041_) as u8);
                leanh::lean_dec(v_a_1041_);
                if v___x_1045_ == 0 {
                    leanh::lean_dec_ref(v___x_1039_);
                    leanh::lean_del_object(v___x_1034_);
                    v___x_1046_ = leanh::lean_box(0);
                    if v_isShared_1044_ == 0 {
                        leanh::lean_ctor_set(v___x_1043_, 0, v___x_1046_);
                        v___x_1048_ = v___x_1043_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_1049_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1049_, 0, v___x_1046_);
                        v___x_1048_ = v_reuseFailAlloc_1049_;
                        state = 3;
                        continue;
                    }
                } else {
                    if v_isShared_1035_ == 0 {
                        leanh::lean_ctor_set(v___x_1034_, 0, v___x_1039_);
                        v___x_1051_ = v___x_1034_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_1055_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1055_, 0, v___x_1039_);
                        v___x_1051_ = v_reuseFailAlloc_1055_;
                        state = 4;
                        continue;
                    }
                }
            }
            3 => {
                return v___x_1048_;
            }
            4 => {
                if v_isShared_1044_ == 0 {
                    leanh::lean_ctor_set(v___x_1043_, 0, v___x_1051_);
                    v___x_1053_ = v___x_1043_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_1054_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1054_, 0, v___x_1051_);
                    v___x_1053_ = v_reuseFailAlloc_1054_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_1053_;
            }
            6 => {
                if v_isShared_1060_ == 0 {
                    v___x_1062_ = v___x_1059_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_1063_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1063_, 0, v_a_1057_);
                    v___x_1062_ = v_reuseFailAlloc_1063_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_1062_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_getUnfoldableConst_x3f___boxed(
    mut v_constName_1070_: *mut leanh::LeanObject,
    mut v_a_1071_: *mut leanh::LeanObject,
    mut v_a_1072_: *mut leanh::LeanObject,
    mut v_a_1073_: *mut leanh::LeanObject,
    mut v_a_1074_: *mut leanh::LeanObject,
    mut v_a_1075_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1076_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1076_ = l_Lean_Meta_getUnfoldableConst_x3f(
        v_constName_1070_,
        v_a_1071_,
        v_a_1072_,
        v_a_1073_,
        v_a_1074_,
    );
    leanh::lean_dec(v_a_1074_);
    leanh::lean_dec_ref(v_a_1073_);
    leanh::lean_dec(v_a_1072_);
    leanh::lean_dec_ref(v_a_1071_);
    return v_res_1076_;
}
pub unsafe fn l_Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0(
    mut v_00_u03b1_1077_: *mut leanh::LeanObject,
    mut v_ref_1078_: *mut leanh::LeanObject,
    mut v_constName_1079_: *mut leanh::LeanObject,
    mut v___y_1080_: *mut leanh::LeanObject,
    mut v___y_1081_: *mut leanh::LeanObject,
    mut v___y_1082_: *mut leanh::LeanObject,
    mut v___y_1083_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1085_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1085_ =
        l_Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0___redArg(
            v_ref_1078_,
            v_constName_1079_,
            v___y_1080_,
            v___y_1081_,
            v___y_1082_,
            v___y_1083_,
        );
    return v___x_1085_;
}
pub unsafe fn l_Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0___boxed(
    mut v_00_u03b1_1086_: *mut leanh::LeanObject,
    mut v_ref_1087_: *mut leanh::LeanObject,
    mut v_constName_1088_: *mut leanh::LeanObject,
    mut v___y_1089_: *mut leanh::LeanObject,
    mut v___y_1090_: *mut leanh::LeanObject,
    mut v___y_1091_: *mut leanh::LeanObject,
    mut v___y_1092_: *mut leanh::LeanObject,
    mut v___y_1093_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1094_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1094_ = l_Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0(
        v_00_u03b1_1086_,
        v_ref_1087_,
        v_constName_1088_,
        v___y_1089_,
        v___y_1090_,
        v___y_1091_,
        v___y_1092_,
    );
    leanh::lean_dec(v___y_1092_);
    leanh::lean_dec_ref(v___y_1091_);
    leanh::lean_dec(v___y_1090_);
    leanh::lean_dec_ref(v___y_1089_);
    leanh::lean_dec(v_ref_1087_);
    return v_res_1094_;
}
pub unsafe fn l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0_spec__0(
    mut v_00_u03b1_1095_: *mut leanh::LeanObject,
    mut v_ref_1096_: *mut leanh::LeanObject,
    mut v_msg_1097_: *mut leanh::LeanObject,
    mut v_declHint_1098_: *mut leanh::LeanObject,
    mut v___y_1099_: *mut leanh::LeanObject,
    mut v___y_1100_: *mut leanh::LeanObject,
    mut v___y_1101_: *mut leanh::LeanObject,
    mut v___y_1102_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1104_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1104_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0_spec__0___redArg(v_ref_1096_, v_msg_1097_, v_declHint_1098_, v___y_1099_, v___y_1100_, v___y_1101_, v___y_1102_);
    return v___x_1104_;
}
pub unsafe fn l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0_spec__0___boxed(
    mut v_00_u03b1_1105_: *mut leanh::LeanObject,
    mut v_ref_1106_: *mut leanh::LeanObject,
    mut v_msg_1107_: *mut leanh::LeanObject,
    mut v_declHint_1108_: *mut leanh::LeanObject,
    mut v___y_1109_: *mut leanh::LeanObject,
    mut v___y_1110_: *mut leanh::LeanObject,
    mut v___y_1111_: *mut leanh::LeanObject,
    mut v___y_1112_: *mut leanh::LeanObject,
    mut v___y_1113_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1114_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1114_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0_spec__0(v_00_u03b1_1105_, v_ref_1106_, v_msg_1107_, v_declHint_1108_, v___y_1109_, v___y_1110_, v___y_1111_, v___y_1112_);
    leanh::lean_dec(v___y_1112_);
    leanh::lean_dec_ref(v___y_1111_);
    leanh::lean_dec(v___y_1110_);
    leanh::lean_dec_ref(v___y_1109_);
    leanh::lean_dec(v_ref_1106_);
    return v_res_1114_;
}
pub unsafe fn l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0_spec__0_spec__1_spec__2(
    mut v_msg_1115_: *mut leanh::LeanObject,
    mut v_declHint_1116_: *mut leanh::LeanObject,
    mut v___y_1117_: *mut leanh::LeanObject,
    mut v___y_1118_: *mut leanh::LeanObject,
    mut v___y_1119_: *mut leanh::LeanObject,
    mut v___y_1120_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1122_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1122_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0_spec__0_spec__1_spec__2___redArg(v_msg_1115_, v_declHint_1116_, v___y_1120_);
    return v___x_1122_;
}
pub unsafe fn l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0_spec__0_spec__1_spec__2___boxed(
    mut v_msg_1123_: *mut leanh::LeanObject,
    mut v_declHint_1124_: *mut leanh::LeanObject,
    mut v___y_1125_: *mut leanh::LeanObject,
    mut v___y_1126_: *mut leanh::LeanObject,
    mut v___y_1127_: *mut leanh::LeanObject,
    mut v___y_1128_: *mut leanh::LeanObject,
    mut v___y_1129_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1130_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1130_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0_spec__0_spec__1_spec__2(v_msg_1123_, v_declHint_1124_, v___y_1125_, v___y_1126_, v___y_1127_, v___y_1128_);
    leanh::lean_dec(v___y_1128_);
    leanh::lean_dec_ref(v___y_1127_);
    leanh::lean_dec(v___y_1126_);
    leanh::lean_dec_ref(v___y_1125_);
    return v_res_1130_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0_spec__0_spec__2(
    mut v_00_u03b1_1131_: *mut leanh::LeanObject,
    mut v_ref_1132_: *mut leanh::LeanObject,
    mut v_msg_1133_: *mut leanh::LeanObject,
    mut v___y_1134_: *mut leanh::LeanObject,
    mut v___y_1135_: *mut leanh::LeanObject,
    mut v___y_1136_: *mut leanh::LeanObject,
    mut v___y_1137_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1139_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1139_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0_spec__0_spec__2___redArg(v_ref_1132_, v_msg_1133_, v___y_1134_, v___y_1135_, v___y_1136_, v___y_1137_);
    return v___x_1139_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0_spec__0_spec__2___boxed(
    mut v_00_u03b1_1140_: *mut leanh::LeanObject,
    mut v_ref_1141_: *mut leanh::LeanObject,
    mut v_msg_1142_: *mut leanh::LeanObject,
    mut v___y_1143_: *mut leanh::LeanObject,
    mut v___y_1144_: *mut leanh::LeanObject,
    mut v___y_1145_: *mut leanh::LeanObject,
    mut v___y_1146_: *mut leanh::LeanObject,
    mut v___y_1147_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1148_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1148_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0_spec__0_spec__2(v_00_u03b1_1140_, v_ref_1141_, v_msg_1142_, v___y_1143_, v___y_1144_, v___y_1145_, v___y_1146_);
    leanh::lean_dec(v___y_1146_);
    leanh::lean_dec_ref(v___y_1145_);
    leanh::lean_dec(v___y_1144_);
    leanh::lean_dec_ref(v___y_1143_);
    leanh::lean_dec(v_ref_1141_);
    return v_res_1148_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0_spec__0_spec__2_spec__4(
    mut v_00_u03b1_1149_: *mut leanh::LeanObject,
    mut v_msg_1150_: *mut leanh::LeanObject,
    mut v___y_1151_: *mut leanh::LeanObject,
    mut v___y_1152_: *mut leanh::LeanObject,
    mut v___y_1153_: *mut leanh::LeanObject,
    mut v___y_1154_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1156_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1156_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0_spec__0_spec__2_spec__4___redArg(v_msg_1150_, v___y_1151_, v___y_1152_, v___y_1153_, v___y_1154_);
    return v___x_1156_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0_spec__0_spec__2_spec__4___boxed(
    mut v_00_u03b1_1157_: *mut leanh::LeanObject,
    mut v_msg_1158_: *mut leanh::LeanObject,
    mut v___y_1159_: *mut leanh::LeanObject,
    mut v___y_1160_: *mut leanh::LeanObject,
    mut v___y_1161_: *mut leanh::LeanObject,
    mut v___y_1162_: *mut leanh::LeanObject,
    mut v___y_1163_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1164_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1164_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_Meta_getUnfoldableConst_x3f_spec__0_spec__0_spec__2_spec__4(v_00_u03b1_1157_, v_msg_1158_, v___y_1159_, v___y_1160_, v___y_1161_, v___y_1162_);
    leanh::lean_dec(v___y_1162_);
    leanh::lean_dec_ref(v___y_1161_);
    leanh::lean_dec(v___y_1160_);
    leanh::lean_dec_ref(v___y_1159_);
    return v_res_1164_;
}
pub unsafe fn l_Lean_Meta_getUnfoldableConstNoEx_x3f(
    mut v_constName_1165_: *mut leanh::LeanObject,
    mut v_a_1166_: *mut leanh::LeanObject,
    mut v_a_1167_: *mut leanh::LeanObject,
    mut v_a_1168_: *mut leanh::LeanObject,
    mut v_a_1169_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1172_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1173_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1174_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_1175_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1176_: u8 = 0;
    let mut v___x_1177_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1178_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1180_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1181_: u8 = 0;
    let mut v___x_1182_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1184_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1185_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1186_: u8 = 0;
    let mut v_unused_1187_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1188_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1189_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1191_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1192_: u8 = 0;
    let mut v___x_1193_: u8 = 0;
    let mut v___x_1194_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1196_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1197_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1199_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1200_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1201_: u8 = 0;
    let mut v_a_1202_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1204_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1205_: u8 = 0;
    let mut v___x_1207_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1208_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1209_: u8 = 0;
    let mut v___x_1210_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1212_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1213_: u8 = 0;
    let mut v___x_1214_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1216_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1217_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1218_: u8 = 0;
    let mut v_unused_1219_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1220_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1222_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1223_: u8 = 0;
    let mut v___x_1225_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1226_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1227_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1174_ = lean_st_ref_get(v_a_1169_);
                v_env_1175_ = leanh::lean_ctor_get(v___x_1174_, 0);
                leanh::lean_inc_ref(v_env_1175_);
                leanh::lean_dec(v___x_1174_);
                v___x_1176_ = 0;
                leanh::lean_inc(v_constName_1165_);
                v___x_1177_ =
                    l_Lean_Environment_find_x3f(v_env_1175_, v_constName_1165_, v___x_1176_);
                if leanh::lean_obj_tag(v___x_1177_) == 1 {
                    v_val_1178_ = leanh::lean_ctor_get(v___x_1177_, 0);
                    leanh::lean_inc(v_val_1178_);
                    match leanh::lean_obj_tag(v_val_1178_) {
                        2 => {
                            leanh::lean_dec_ref_known(v___x_1177_, 1);
                            leanh::lean_dec(v_constName_1165_);
                            v_isSharedCheck_1186_ =
                                (!leanh::lean_is_exclusive(v_val_1178_)) as u8;
                            if v_isSharedCheck_1186_ == 0 {
                                v_unused_1187_ = leanh::lean_ctor_get(v_val_1178_, 0);
                                leanh::lean_dec(v_unused_1187_);
                                v___x_1180_ = v_val_1178_;
                                v_isShared_1181_ = v_isSharedCheck_1186_;
                                state = 2;
                                continue;
                            } else {
                                leanh::lean_dec(v_val_1178_);
                                v___x_1180_ = leanh::lean_box(0);
                                v_isShared_1181_ = v_isSharedCheck_1186_;
                                state = 2;
                                continue;
                            }
                        }
                        1 => {
                            leanh::lean_dec(v_constName_1165_);
                            v___x_1188_ = l_Lean_Meta_canUnfold___redArg(
                                v_val_1178_,
                                v_a_1166_,
                                v_a_1168_,
                                v_a_1169_,
                            );
                            if leanh::lean_obj_tag(v___x_1188_) == 0 {
                                v_a_1189_ = leanh::lean_ctor_get(v___x_1188_, 0);
                                v_isSharedCheck_1201_ =
                                    (!leanh::lean_is_exclusive(v___x_1188_)) as u8;
                                if v_isSharedCheck_1201_ == 0 {
                                    v___x_1191_ = v___x_1188_;
                                    v_isShared_1192_ = v_isSharedCheck_1201_;
                                    state = 4;
                                    continue;
                                } else {
                                    leanh::lean_inc(v_a_1189_);
                                    leanh::lean_dec(v___x_1188_);
                                    v___x_1191_ = leanh::lean_box(0);
                                    v_isShared_1192_ = v_isSharedCheck_1201_;
                                    state = 4;
                                    continue;
                                }
                            } else {
                                leanh::lean_dec_ref_known(v___x_1177_, 1);
                                v_a_1202_ = leanh::lean_ctor_get(v___x_1188_, 0);
                                v_isSharedCheck_1209_ =
                                    (!leanh::lean_is_exclusive(v___x_1188_)) as u8;
                                if v_isSharedCheck_1209_ == 0 {
                                    v___x_1204_ = v___x_1188_;
                                    v_isShared_1205_ = v_isSharedCheck_1209_;
                                    state = 7;
                                    continue;
                                } else {
                                    leanh::lean_inc(v_a_1202_);
                                    leanh::lean_dec(v___x_1188_);
                                    v___x_1204_ = leanh::lean_box(0);
                                    v_isShared_1205_ = v_isSharedCheck_1209_;
                                    state = 7;
                                    continue;
                                }
                            }
                        }
                        0 => {
                            leanh::lean_dec_ref_known(v_val_1178_, 1);
                            leanh::lean_dec_ref_known(v___x_1177_, 1);
                            v___x_1210_ = l_Lean_Meta_recordUnfoldAxiom___redArg(
                                v_constName_1165_,
                                v_a_1167_,
                                v_a_1168_,
                            );
                            if leanh::lean_obj_tag(v___x_1210_) == 0 {
                                v_isSharedCheck_1218_ =
                                    (!leanh::lean_is_exclusive(v___x_1210_)) as u8;
                                if v_isSharedCheck_1218_ == 0 {
                                    v_unused_1219_ = leanh::lean_ctor_get(v___x_1210_, 0);
                                    leanh::lean_dec(v_unused_1219_);
                                    v___x_1212_ = v___x_1210_;
                                    v_isShared_1213_ = v_isSharedCheck_1218_;
                                    state = 9;
                                    continue;
                                } else {
                                    leanh::lean_dec(v___x_1210_);
                                    v___x_1212_ = leanh::lean_box(0);
                                    v_isShared_1213_ = v_isSharedCheck_1218_;
                                    state = 9;
                                    continue;
                                }
                            } else {
                                v_a_1220_ = leanh::lean_ctor_get(v___x_1210_, 0);
                                v_isSharedCheck_1227_ =
                                    (!leanh::lean_is_exclusive(v___x_1210_)) as u8;
                                if v_isSharedCheck_1227_ == 0 {
                                    v___x_1222_ = v___x_1210_;
                                    v_isShared_1223_ = v_isSharedCheck_1227_;
                                    state = 11;
                                    continue;
                                } else {
                                    leanh::lean_inc(v_a_1220_);
                                    leanh::lean_dec(v___x_1210_);
                                    v___x_1222_ = leanh::lean_box(0);
                                    v_isShared_1223_ = v_isSharedCheck_1227_;
                                    state = 11;
                                    continue;
                                }
                            }
                        }
                        _ => {
                            leanh::lean_dec(v_val_1178_);
                            leanh::lean_dec_ref_known(v___x_1177_, 1);
                            leanh::lean_dec(v_constName_1165_);
                            state = 1;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_dec(v___x_1177_);
                    leanh::lean_dec(v_constName_1165_);
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_1172_ = leanh::lean_box(0);
                v___x_1173_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_1173_, 0, v___x_1172_);
                return v___x_1173_;
            }
            2 => {
                v___x_1182_ = leanh::lean_box(0);
                if v_isShared_1181_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_1180_, 0);
                    leanh::lean_ctor_set(v___x_1180_, 0, v___x_1182_);
                    v___x_1184_ = v___x_1180_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_1185_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1185_, 0, v___x_1182_);
                    v___x_1184_ = v_reuseFailAlloc_1185_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_1184_;
            }
            4 => {
                v___x_1193_ = (leanh::lean_unbox(v_a_1189_) as u8);
                leanh::lean_dec(v_a_1189_);
                if v___x_1193_ == 0 {
                    leanh::lean_dec_ref_known(v___x_1177_, 1);
                    v___x_1194_ = leanh::lean_box(0);
                    if v_isShared_1192_ == 0 {
                        leanh::lean_ctor_set(v___x_1191_, 0, v___x_1194_);
                        v___x_1196_ = v___x_1191_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_1197_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1197_, 0, v___x_1194_);
                        v___x_1196_ = v_reuseFailAlloc_1197_;
                        state = 5;
                        continue;
                    }
                } else {
                    if v_isShared_1192_ == 0 {
                        leanh::lean_ctor_set(v___x_1191_, 0, v___x_1177_);
                        v___x_1199_ = v___x_1191_;
                        state = 6;
                        continue;
                    } else {
                        v_reuseFailAlloc_1200_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1200_, 0, v___x_1177_);
                        v___x_1199_ = v_reuseFailAlloc_1200_;
                        state = 6;
                        continue;
                    }
                }
            }
            5 => {
                return v___x_1196_;
            }
            6 => {
                return v___x_1199_;
            }
            7 => {
                if v_isShared_1205_ == 0 {
                    v___x_1207_ = v___x_1204_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_1208_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1208_, 0, v_a_1202_);
                    v___x_1207_ = v_reuseFailAlloc_1208_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_1207_;
            }
            9 => {
                v___x_1214_ = leanh::lean_box(0);
                if v_isShared_1213_ == 0 {
                    leanh::lean_ctor_set(v___x_1212_, 0, v___x_1214_);
                    v___x_1216_ = v___x_1212_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_1217_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1217_, 0, v___x_1214_);
                    v___x_1216_ = v_reuseFailAlloc_1217_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_1216_;
            }
            11 => {
                if v_isShared_1223_ == 0 {
                    v___x_1225_ = v___x_1222_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_1226_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1226_, 0, v_a_1220_);
                    v___x_1225_ = v_reuseFailAlloc_1226_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                return v___x_1225_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_getUnfoldableConstNoEx_x3f___boxed(
    mut v_constName_1228_: *mut leanh::LeanObject,
    mut v_a_1229_: *mut leanh::LeanObject,
    mut v_a_1230_: *mut leanh::LeanObject,
    mut v_a_1231_: *mut leanh::LeanObject,
    mut v_a_1232_: *mut leanh::LeanObject,
    mut v_a_1233_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1234_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1234_ = l_Lean_Meta_getUnfoldableConstNoEx_x3f(
        v_constName_1228_,
        v_a_1229_,
        v_a_1230_,
        v_a_1231_,
        v_a_1232_,
    );
    leanh::lean_dec(v_a_1232_);
    leanh::lean_dec_ref(v_a_1231_);
    leanh::lean_dec(v_a_1230_);
    leanh::lean_dec_ref(v_a_1229_);
    return v_res_1234_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Meta_GetUnfoldableConst(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Meta_Basic(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Meta_GetUnfoldableConst(
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
pub unsafe fn initialize_Lean_Meta_GetUnfoldableConst(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Meta_Basic(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_GetUnfoldableConst(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Meta_GetUnfoldableConst(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return initialize_Lean_Meta_GetUnfoldableConst(builtin);
}