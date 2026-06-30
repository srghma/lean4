// Lean compiler output
// Module: Lean.Meta.CtorRecognizer
// Imports: Lean.Meta.LitValues Lean.Meta.Offset
use crate::ffi::{
    lean_array_get, lean_array_push, lean_mk_array, lean_mk_empty_array_with_capacity,
    lean_nat_add, lean_nat_dec_eq, lean_nat_sub, lean_st_ref_get, lean_whnf,
};
use crate::r#gen::Init::Prelude::l_Lean_replaceRef;
use crate::r#gen::Lean::CoreM::l_Lean_Exception_isRuntime;
use crate::r#gen::Lean::Data::Name::l_Lean_Name_isAnonymous;
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
    l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux, l_Lean_Expr_getAppFn,
    l_Lean_Expr_getAppNumArgs, l_Lean_Expr_sort___override, l_Lean_mkNatAdd, l_Lean_mkNatLit,
};
use crate::r#gen::Lean::Message::{
    l_Lean_MessageData_note, l_Lean_MessageData_ofConstName, l_Lean_MessageData_ofName,
    l_Lean_stringToMessageData,
};
use crate::r#gen::Lean::Meta::LitValues::{
    initialize_Lean_Meta_LitValues, l_Lean_Meta_litToCtor, runtime_initialize_Lean_Meta_LitValues,
};
use crate::r#gen::Lean::Meta::Offset::{
    initialize_Lean_Meta_Offset, l_Lean_Meta_isOffset_x3f, runtime_initialize_Lean_Meta_Offset,
};
use crate::r#gen::Lean::PrivateName::l_Lean_isPrivateName;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_isConstructorApp_x27_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__0_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_isConstructorApp_x27_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__0: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_isConstructorApp_x27_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__1_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_isConstructorApp_x27_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__1: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_isConstructorApp_x27_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__2_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_isConstructorApp_x27_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__2: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_isConstructorApp_x27_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__3_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_isConstructorApp_x27_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__3: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_isConstructorApp_x27_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__4_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_isConstructorApp_x27_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__4: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_isConstructorApp_x27_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__5_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_isConstructorApp_x27_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__5: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_isConstructorApp_x27_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__6_value: leanh::LeanStringObject<24> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 24, m_capacity: 24, m_length: 23, m_data: [65, 32, 112, 114, 105, 118, 97, 116, 101, 32, 100, 101, 99, 108, 97, 114, 97, 116, 105, 111, 110, 32, 96, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_isConstructorApp_x27_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__6: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_isConstructorApp_x27_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__6_value) as *mut leanh::LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_isConstructorApp_x27_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__7_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_isConstructorApp_x27_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__7: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_isConstructorApp_x27_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__8_value: leanh::LeanStringObject<79> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 79, m_capacity: 79, m_length: 78, m_data: [96, 32, 40, 102, 114, 111, 109, 32, 116, 104, 101, 32, 99, 117, 114, 114, 101, 110, 116, 32, 109, 111, 100, 117, 108, 101, 41, 32, 101, 120, 105, 115, 116, 115, 32, 98, 117, 116, 32, 119, 111, 117, 108, 100, 32, 110, 101, 101, 100, 32, 116, 111, 32, 98, 101, 32, 112, 117, 98, 108, 105, 99, 32, 116, 111, 32, 97, 99, 99, 101, 115, 115, 32, 104, 101, 114, 101, 46, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_isConstructorApp_x27_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__8: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_isConstructorApp_x27_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__8_value) as *mut leanh::LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_isConstructorApp_x27_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__9_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_isConstructorApp_x27_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__9: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_isConstructorApp_x27_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__10_value: leanh::LeanStringObject<23> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 23, m_capacity: 23, m_length: 22, m_data: [65, 32, 112, 117, 98, 108, 105, 99, 32, 100, 101, 99, 108, 97, 114, 97, 116, 105, 111, 110, 32, 96, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_isConstructorApp_x27_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__10: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_isConstructorApp_x27_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__10_value) as *mut leanh::LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_isConstructorApp_x27_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__11_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_isConstructorApp_x27_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__11: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_isConstructorApp_x27_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__12_value: leanh::LeanStringObject<68> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 68, m_capacity: 68, m_length: 67, m_data: [96, 32, 101, 120, 105, 115, 116, 115, 32, 98, 117, 116, 32, 105, 115, 32, 105, 109, 112, 111, 114, 116, 101, 100, 32, 112, 114, 105, 118, 97, 116, 101, 108, 121, 59, 32, 99, 111, 110, 115, 105, 100, 101, 114, 32, 97, 100, 100, 105, 110, 103, 32, 96, 112, 117, 98, 108, 105, 99, 32, 105, 109, 112, 111, 114, 116, 32, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_isConstructorApp_x27_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__12: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_isConstructorApp_x27_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__12_value) as *mut leanh::LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_isConstructorApp_x27_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__13_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_isConstructorApp_x27_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__13: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_isConstructorApp_x27_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__14_value: leanh::LeanStringObject<3> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [96, 46, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_isConstructorApp_x27_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__14: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_isConstructorApp_x27_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__14_value) as *mut leanh::LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_isConstructorApp_x27_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__15_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_isConstructorApp_x27_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__15: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_isConstructorApp_x27_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__16_value: leanh::LeanStringObject<10> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [96, 32, 40, 102, 114, 111, 109, 32, 96, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_isConstructorApp_x27_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__16: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_isConstructorApp_x27_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__16_value) as *mut leanh::LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_isConstructorApp_x27_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__17_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_isConstructorApp_x27_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__17: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_isConstructorApp_x27_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__18_value: leanh::LeanStringObject<54> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 54, m_capacity: 54, m_length: 53, m_data: [96, 41, 32, 101, 120, 105, 115, 116, 115, 32, 98, 117, 116, 32, 119, 111, 117, 108, 100, 32, 110, 101, 101, 100, 32, 116, 111, 32, 98, 101, 32, 112, 117, 98, 108, 105, 99, 32, 116, 111, 32, 97, 99, 99, 101, 115, 115, 32, 104, 101, 114, 101, 46, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_isConstructorApp_x27_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__18: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_isConstructorApp_x27_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__18_value) as *mut leanh::LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_isConstructorApp_x27_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__19_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_isConstructorApp_x27_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__19: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_isConstructorApp_x27_x3f_spec__0_spec__0_spec__1___redArg___closed__0_value: leanh::LeanStringObject<19> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 19, m_capacity: 19, m_length: 18, m_data: [85, 110, 107, 110, 111, 119, 110, 32, 99, 111, 110, 115, 116, 97, 110, 116, 32, 96, 0]};
static mut l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_isConstructorApp_x27_x3f_spec__0_spec__0_spec__1___redArg___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_isConstructorApp_x27_x3f_spec__0_spec__0_spec__1___redArg___closed__0_value) as *mut leanh::LeanObject;
static mut l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_isConstructorApp_x27_x3f_spec__0_spec__0_spec__1___redArg___closed__1_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_isConstructorApp_x27_x3f_spec__0_spec__0_spec__1___redArg___closed__1: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_isConstructorApp_x27_x3f_spec__0_spec__0_spec__1___redArg___closed__2_value: leanh::LeanStringObject<2> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [96, 0]};
static mut l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_isConstructorApp_x27_x3f_spec__0_spec__0_spec__1___redArg___closed__2: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_isConstructorApp_x27_x3f_spec__0_spec__0_spec__1___redArg___closed__2_value) as *mut leanh::LeanObject;
static mut l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_isConstructorApp_x27_x3f_spec__0_spec__0_spec__1___redArg___closed__3_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_isConstructorApp_x27_x3f_spec__0_spec__0_spec__1___redArg___closed__3: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Meta_isConstructorApp_x27_x3f___closed__0_value: leanh::LeanStringObject<
    4,
> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 4,
    m_capacity: 4,
    m_length: 3,
    m_data: [78, 97, 116, 0],
};
static mut l_Lean_Meta_isConstructorApp_x27_x3f___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_isConstructorApp_x27_x3f___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Meta_isConstructorApp_x27_x3f___closed__1_value: leanh::LeanStringObject<
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
    m_data: [115, 117, 99, 99, 0],
};
static mut l_Lean_Meta_isConstructorApp_x27_x3f___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_isConstructorApp_x27_x3f___closed__1_value)
        as *mut leanh::LeanObject;
static l_Lean_Meta_isConstructorApp_x27_x3f___closed__2_value_aux_0: leanh::LeanCtorObject<
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
        core::ptr::addr_of!(l_Lean_Meta_isConstructorApp_x27_x3f___closed__0_value)
            as *mut leanh::LeanObject,
        11442535297760353691 as *mut leanh::LeanObject,
    ],
};
pub static l_Lean_Meta_isConstructorApp_x27_x3f___closed__2_value: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_isConstructorApp_x27_x3f___closed__2_value_aux_0)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_isConstructorApp_x27_x3f___closed__1_value)
                as *mut leanh::LeanObject,
            16112798088292836701 as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_Meta_isConstructorApp_x27_x3f___closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_isConstructorApp_x27_x3f___closed__2_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Meta_constructorApp_x3f___closed__0_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_constructorApp_x3f___closed__0: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub unsafe fn l___private_Lean_Meta_CtorRecognizer_0__Lean_Meta_getConstructorVal_x3f(
    mut v_env_820_: *mut leanh::LeanObject,
    mut v_ctorName_821_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_822_: u8 = 0;
    let mut v___x_823_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_824_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_826_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_827_: u8 = 0;
    let mut v_val_828_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_830_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_831_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_832_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_833_: u8 = 0;
    let mut v___x_834_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_822_ = 0;
                v___x_823_ = l_Lean_Environment_find_x3f(v_env_820_, v_ctorName_821_, v___x_822_);
                if leanh::lean_obj_tag(v___x_823_) == 1 {
                    v_val_824_ = leanh::lean_ctor_get(v___x_823_, 0);
                    v_isSharedCheck_833_ = (!leanh::lean_is_exclusive(v___x_823_)) as u8;
                    if v_isSharedCheck_833_ == 0 {
                        v___x_826_ = v___x_823_;
                        v_isShared_827_ = v_isSharedCheck_833_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_val_824_);
                        leanh::lean_dec(v___x_823_);
                        v___x_826_ = leanh::lean_box(0);
                        v_isShared_827_ = v_isSharedCheck_833_;
                        state = 1;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v___x_823_);
                    v___x_834_ = leanh::lean_box(0);
                    return v___x_834_;
                }
            }
            1 => {
                if leanh::lean_obj_tag(v_val_824_) == 6 {
                    v_val_828_ = leanh::lean_ctor_get(v_val_824_, 0);
                    leanh::lean_inc_ref(v_val_828_);
                    leanh::lean_dec_ref_known(v_val_824_, 1);
                    if v_isShared_827_ == 0 {
                        leanh::lean_ctor_set(v___x_826_, 0, v_val_828_);
                        v___x_830_ = v___x_826_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_831_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_831_, 0, v_val_828_);
                        v___x_830_ = v_reuseFailAlloc_831_;
                        state = 2;
                        continue;
                    }
                } else {
                    leanh::lean_del_object(v___x_826_);
                    leanh::lean_dec(v_val_824_);
                    v___x_832_ = leanh::lean_box(0);
                    return v___x_832_;
                }
            }
            2 => {
                return v___x_830_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_isConstructorAppCore_x3f___redArg(
    mut v_e_835_: *mut leanh::LeanObject,
    mut v_a_836_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_838_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_declName_839_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_840_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_841_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_842_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_843_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_numParams_844_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_numFields_845_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_846_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_847_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_848_: u8 = 0;
    let mut v___x_850_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_851_: u8 = 0;
    let mut v___x_852_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_854_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_855_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_856_: u8 = 0;
    let mut v_unused_857_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_858_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_859_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_860_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_861_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_862_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_838_ = l_Lean_Expr_getAppFn(v_e_835_);
                if leanh::lean_obj_tag(v___x_838_) == 4 {
                    v_declName_839_ = leanh::lean_ctor_get(v___x_838_, 0);
                    leanh::lean_inc(v_declName_839_);
                    leanh::lean_dec_ref_known(v___x_838_, 2);
                    v___x_840_ = lean_st_ref_get(v_a_836_);
                    v_env_841_ = leanh::lean_ctor_get(v___x_840_, 0);
                    leanh::lean_inc_ref(v_env_841_);
                    leanh::lean_dec(v___x_840_);
                    v___x_842_ =
                        l___private_Lean_Meta_CtorRecognizer_0__Lean_Meta_getConstructorVal_x3f(
                            v_env_841_,
                            v_declName_839_,
                        );
                    if leanh::lean_obj_tag(v___x_842_) == 1 {
                        v_val_843_ = leanh::lean_ctor_get(v___x_842_, 0);
                        leanh::lean_inc(v_val_843_);
                        v_numParams_844_ = leanh::lean_ctor_get(v_val_843_, 3);
                        leanh::lean_inc(v_numParams_844_);
                        v_numFields_845_ = leanh::lean_ctor_get(v_val_843_, 4);
                        leanh::lean_inc(v_numFields_845_);
                        leanh::lean_dec(v_val_843_);
                        v___x_846_ = lean_nat_add(v_numParams_844_, v_numFields_845_);
                        leanh::lean_dec(v_numFields_845_);
                        leanh::lean_dec(v_numParams_844_);
                        v___x_847_ = l_Lean_Expr_getAppNumArgs(v_e_835_);
                        v___x_848_ = lean_nat_dec_eq(v___x_846_, v___x_847_);
                        leanh::lean_dec(v___x_847_);
                        leanh::lean_dec(v___x_846_);
                        if v___x_848_ == 0 {
                            v_isSharedCheck_856_ =
                                (!leanh::lean_is_exclusive(v___x_842_)) as u8;
                            if v_isSharedCheck_856_ == 0 {
                                v_unused_857_ = leanh::lean_ctor_get(v___x_842_, 0);
                                leanh::lean_dec(v_unused_857_);
                                v___x_850_ = v___x_842_;
                                v_isShared_851_ = v_isSharedCheck_856_;
                                state = 1;
                                continue;
                            } else {
                                leanh::lean_dec(v___x_842_);
                                v___x_850_ = leanh::lean_box(0);
                                v_isShared_851_ = v_isSharedCheck_856_;
                                state = 1;
                                continue;
                            }
                        } else {
                            v___x_858_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                            leanh::lean_ctor_set(v___x_858_, 0, v___x_842_);
                            return v___x_858_;
                        }
                    } else {
                        leanh::lean_dec(v___x_842_);
                        v___x_859_ = leanh::lean_box(0);
                        v___x_860_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v___x_860_, 0, v___x_859_);
                        return v___x_860_;
                    }
                } else {
                    leanh::lean_dec_ref(v___x_838_);
                    v___x_861_ = leanh::lean_box(0);
                    v___x_862_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_862_, 0, v___x_861_);
                    return v___x_862_;
                }
            }
            1 => {
                v___x_852_ = leanh::lean_box(0);
                if v_isShared_851_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_850_, 0);
                    leanh::lean_ctor_set(v___x_850_, 0, v___x_852_);
                    v___x_854_ = v___x_850_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_855_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_855_, 0, v___x_852_);
                    v___x_854_ = v_reuseFailAlloc_855_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_854_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_isConstructorAppCore_x3f___redArg___boxed(
    mut v_e_863_: *mut leanh::LeanObject,
    mut v_a_864_: *mut leanh::LeanObject,
    mut v_a_865_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_866_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_866_ = l_Lean_Meta_isConstructorAppCore_x3f___redArg(v_e_863_, v_a_864_);
    leanh::lean_dec(v_a_864_);
    leanh::lean_dec_ref(v_e_863_);
    return v_res_866_;
}
pub unsafe fn l_Lean_Meta_isConstructorAppCore_x3f(
    mut v_e_867_: *mut leanh::LeanObject,
    mut v_a_868_: *mut leanh::LeanObject,
    mut v_a_869_: *mut leanh::LeanObject,
    mut v_a_870_: *mut leanh::LeanObject,
    mut v_a_871_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_873_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_873_ = l_Lean_Meta_isConstructorAppCore_x3f___redArg(v_e_867_, v_a_871_);
    return v___x_873_;
}
pub unsafe fn l_Lean_Meta_isConstructorAppCore_x3f___boxed(
    mut v_e_874_: *mut leanh::LeanObject,
    mut v_a_875_: *mut leanh::LeanObject,
    mut v_a_876_: *mut leanh::LeanObject,
    mut v_a_877_: *mut leanh::LeanObject,
    mut v_a_878_: *mut leanh::LeanObject,
    mut v_a_879_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_880_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_880_ =
        l_Lean_Meta_isConstructorAppCore_x3f(v_e_874_, v_a_875_, v_a_876_, v_a_877_, v_a_878_);
    leanh::lean_dec(v_a_878_);
    leanh::lean_dec_ref(v_a_877_);
    leanh::lean_dec(v_a_876_);
    leanh::lean_dec_ref(v_a_875_);
    leanh::lean_dec_ref(v_e_874_);
    return v_res_880_;
}
pub unsafe fn l_Lean_Meta_isConstructorApp_x3f(
    mut v_e_881_: *mut leanh::LeanObject,
    mut v_a_882_: *mut leanh::LeanObject,
    mut v_a_883_: *mut leanh::LeanObject,
    mut v_a_884_: *mut leanh::LeanObject,
    mut v_a_885_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_887_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_888_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_889_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_890_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_892_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_893_: u8 = 0;
    let mut v___x_895_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_896_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_897_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_887_ =
                    l_Lean_Meta_litToCtor(v_e_881_, v_a_882_, v_a_883_, v_a_884_, v_a_885_);
                if leanh::lean_obj_tag(v___x_887_) == 0 {
                    v_a_888_ = leanh::lean_ctor_get(v___x_887_, 0);
                    leanh::lean_inc(v_a_888_);
                    leanh::lean_dec_ref_known(v___x_887_, 1);
                    v___x_889_ = l_Lean_Meta_isConstructorAppCore_x3f___redArg(v_a_888_, v_a_885_);
                    leanh::lean_dec(v_a_888_);
                    return v___x_889_;
                } else {
                    v_a_890_ = leanh::lean_ctor_get(v___x_887_, 0);
                    v_isSharedCheck_897_ = (!leanh::lean_is_exclusive(v___x_887_)) as u8;
                    if v_isSharedCheck_897_ == 0 {
                        v___x_892_ = v___x_887_;
                        v_isShared_893_ = v_isSharedCheck_897_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_890_);
                        leanh::lean_dec(v___x_887_);
                        v___x_892_ = leanh::lean_box(0);
                        v_isShared_893_ = v_isSharedCheck_897_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_893_ == 0 {
                    v___x_895_ = v___x_892_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_896_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_896_, 0, v_a_890_);
                    v___x_895_ = v_reuseFailAlloc_896_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_895_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_isConstructorApp_x3f___boxed(
    mut v_e_898_: *mut leanh::LeanObject,
    mut v_a_899_: *mut leanh::LeanObject,
    mut v_a_900_: *mut leanh::LeanObject,
    mut v_a_901_: *mut leanh::LeanObject,
    mut v_a_902_: *mut leanh::LeanObject,
    mut v_a_903_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_904_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_904_ = l_Lean_Meta_isConstructorApp_x3f(v_e_898_, v_a_899_, v_a_900_, v_a_901_, v_a_902_);
    leanh::lean_dec(v_a_902_);
    leanh::lean_dec_ref(v_a_901_);
    leanh::lean_dec(v_a_900_);
    leanh::lean_dec_ref(v_a_899_);
    return v_res_904_;
}
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_isConstructorApp_x27_x3f_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6_spec__7(
    mut v_msgData_905_: *mut leanh::LeanObject,
    mut v___y_906_: *mut leanh::LeanObject,
    mut v___y_907_: *mut leanh::LeanObject,
    mut v___y_908_: *mut leanh::LeanObject,
    mut v___y_909_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_911_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_912_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_913_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_914_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_lctx_915_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_916_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_917_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_918_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_919_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_911_ = lean_st_ref_get(v___y_909_);
    v_env_912_ = leanh::lean_ctor_get(v___x_911_, 0);
    leanh::lean_inc_ref(v_env_912_);
    leanh::lean_dec(v___x_911_);
    v___x_913_ = lean_st_ref_get(v___y_907_);
    v_mctx_914_ = leanh::lean_ctor_get(v___x_913_, 0);
    leanh::lean_inc_ref(v_mctx_914_);
    leanh::lean_dec(v___x_913_);
    v_lctx_915_ = leanh::lean_ctor_get(v___y_906_, 2);
    v_options_916_ = leanh::lean_ctor_get(v___y_908_, 2);
    leanh::lean_inc_ref(v_options_916_);
    leanh::lean_inc_ref(v_lctx_915_);
    v___x_917_ = leanh::lean_alloc_ctor(0, 4, (0) as u32);
    leanh::lean_ctor_set(v___x_917_, 0, v_env_912_);
    leanh::lean_ctor_set(v___x_917_, 1, v_mctx_914_);
    leanh::lean_ctor_set(v___x_917_, 2, v_lctx_915_);
    leanh::lean_ctor_set(v___x_917_, 3, v_options_916_);
    v___x_918_ = leanh::lean_alloc_ctor(3, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_918_, 0, v___x_917_);
    leanh::lean_ctor_set(v___x_918_, 1, v_msgData_905_);
    v___x_919_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_919_, 0, v___x_918_);
    return v___x_919_;
}
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_isConstructorApp_x27_x3f_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6_spec__7___boxed(
    mut v_msgData_920_: *mut leanh::LeanObject,
    mut v___y_921_: *mut leanh::LeanObject,
    mut v___y_922_: *mut leanh::LeanObject,
    mut v___y_923_: *mut leanh::LeanObject,
    mut v___y_924_: *mut leanh::LeanObject,
    mut v___y_925_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_926_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_926_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_isConstructorApp_x27_x3f_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6_spec__7(v_msgData_920_, v___y_921_, v___y_922_, v___y_923_, v___y_924_);
    leanh::lean_dec(v___y_924_);
    leanh::lean_dec_ref(v___y_923_);
    leanh::lean_dec(v___y_922_);
    leanh::lean_dec_ref(v___y_921_);
    return v_res_926_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_isConstructorApp_x27_x3f_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6___redArg(
    mut v_msg_927_: *mut leanh::LeanObject,
    mut v___y_928_: *mut leanh::LeanObject,
    mut v___y_929_: *mut leanh::LeanObject,
    mut v___y_930_: *mut leanh::LeanObject,
    mut v___y_931_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_ref_933_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_934_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_935_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_937_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_938_: u8 = 0;
    let mut v___x_939_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_941_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_942_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_943_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ref_933_ = leanh::lean_ctor_get(v___y_930_, 5);
                v___x_934_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_isConstructorApp_x27_x3f_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6_spec__7(v_msg_927_, v___y_928_, v___y_929_, v___y_930_, v___y_931_);
                v_a_935_ = leanh::lean_ctor_get(v___x_934_, 0);
                v_isSharedCheck_943_ = (!leanh::lean_is_exclusive(v___x_934_)) as u8;
                if v_isSharedCheck_943_ == 0 {
                    v___x_937_ = v___x_934_;
                    v_isShared_938_ = v_isSharedCheck_943_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_a_935_);
                    leanh::lean_dec(v___x_934_);
                    v___x_937_ = leanh::lean_box(0);
                    v_isShared_938_ = v_isSharedCheck_943_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                leanh::lean_inc(v_ref_933_);
                v___x_939_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_939_, 0, v_ref_933_);
                leanh::lean_ctor_set(v___x_939_, 1, v_a_935_);
                if v_isShared_938_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_937_, 1);
                    leanh::lean_ctor_set(v___x_937_, 0, v___x_939_);
                    v___x_941_ = v___x_937_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_942_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_942_, 0, v___x_939_);
                    v___x_941_ = v_reuseFailAlloc_942_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_941_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_isConstructorApp_x27_x3f_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6___redArg___boxed(
    mut v_msg_944_: *mut leanh::LeanObject,
    mut v___y_945_: *mut leanh::LeanObject,
    mut v___y_946_: *mut leanh::LeanObject,
    mut v___y_947_: *mut leanh::LeanObject,
    mut v___y_948_: *mut leanh::LeanObject,
    mut v___y_949_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_950_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_950_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_isConstructorApp_x27_x3f_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6___redArg(v_msg_944_, v___y_945_, v___y_946_, v___y_947_, v___y_948_);
    leanh::lean_dec(v___y_948_);
    leanh::lean_dec_ref(v___y_947_);
    leanh::lean_dec(v___y_946_);
    leanh::lean_dec_ref(v___y_945_);
    return v_res_950_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_isConstructorApp_x27_x3f_spec__0_spec__0_spec__1_spec__2_spec__4___redArg(
    mut v_ref_951_: *mut leanh::LeanObject,
    mut v_msg_952_: *mut leanh::LeanObject,
    mut v___y_953_: *mut leanh::LeanObject,
    mut v___y_954_: *mut leanh::LeanObject,
    mut v___y_955_: *mut leanh::LeanObject,
    mut v___y_956_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_fileName_958_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fileMap_959_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_960_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_currRecDepth_961_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_maxRecDepth_962_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_963_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_currNamespace_964_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_openDecls_965_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_initHeartbeats_966_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_maxHeartbeats_967_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_quotContext_968_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_currMacroScope_969_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_diag_970_: u8 = 0;
    let mut v_cancelTk_x3f_971_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_suppressElabErrors_972_: u8 = 0;
    let mut v_inheritedTraceOptions_973_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_974_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_975_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_976_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_fileName_958_ = leanh::lean_ctor_get(v___y_955_, 0);
    v_fileMap_959_ = leanh::lean_ctor_get(v___y_955_, 1);
    v_options_960_ = leanh::lean_ctor_get(v___y_955_, 2);
    v_currRecDepth_961_ = leanh::lean_ctor_get(v___y_955_, 3);
    v_maxRecDepth_962_ = leanh::lean_ctor_get(v___y_955_, 4);
    v_ref_963_ = leanh::lean_ctor_get(v___y_955_, 5);
    v_currNamespace_964_ = leanh::lean_ctor_get(v___y_955_, 6);
    v_openDecls_965_ = leanh::lean_ctor_get(v___y_955_, 7);
    v_initHeartbeats_966_ = leanh::lean_ctor_get(v___y_955_, 8);
    v_maxHeartbeats_967_ = leanh::lean_ctor_get(v___y_955_, 9);
    v_quotContext_968_ = leanh::lean_ctor_get(v___y_955_, 10);
    v_currMacroScope_969_ = leanh::lean_ctor_get(v___y_955_, 11);
    v_diag_970_ = leanh::lean_ctor_get_uint8(
        v___y_955_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 14) as u32,
    );
    v_cancelTk_x3f_971_ = leanh::lean_ctor_get(v___y_955_, 12);
    v_suppressElabErrors_972_ = leanh::lean_ctor_get_uint8(
        v___y_955_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 14 + 1) as u32,
    );
    v_inheritedTraceOptions_973_ = leanh::lean_ctor_get(v___y_955_, 13);
    v_ref_974_ = l_Lean_replaceRef(v_ref_951_, v_ref_963_);
    leanh::lean_inc_ref(v_inheritedTraceOptions_973_);
    leanh::lean_inc(v_cancelTk_x3f_971_);
    leanh::lean_inc(v_currMacroScope_969_);
    leanh::lean_inc(v_quotContext_968_);
    leanh::lean_inc(v_maxHeartbeats_967_);
    leanh::lean_inc(v_initHeartbeats_966_);
    leanh::lean_inc(v_openDecls_965_);
    leanh::lean_inc(v_currNamespace_964_);
    leanh::lean_inc(v_maxRecDepth_962_);
    leanh::lean_inc(v_currRecDepth_961_);
    leanh::lean_inc_ref(v_options_960_);
    leanh::lean_inc_ref(v_fileMap_959_);
    leanh::lean_inc_ref(v_fileName_958_);
    v___x_975_ = leanh::lean_alloc_ctor(0, 14, (2) as u32);
    leanh::lean_ctor_set(v___x_975_, 0, v_fileName_958_);
    leanh::lean_ctor_set(v___x_975_, 1, v_fileMap_959_);
    leanh::lean_ctor_set(v___x_975_, 2, v_options_960_);
    leanh::lean_ctor_set(v___x_975_, 3, v_currRecDepth_961_);
    leanh::lean_ctor_set(v___x_975_, 4, v_maxRecDepth_962_);
    leanh::lean_ctor_set(v___x_975_, 5, v_ref_974_);
    leanh::lean_ctor_set(v___x_975_, 6, v_currNamespace_964_);
    leanh::lean_ctor_set(v___x_975_, 7, v_openDecls_965_);
    leanh::lean_ctor_set(v___x_975_, 8, v_initHeartbeats_966_);
    leanh::lean_ctor_set(v___x_975_, 9, v_maxHeartbeats_967_);
    leanh::lean_ctor_set(v___x_975_, 10, v_quotContext_968_);
    leanh::lean_ctor_set(v___x_975_, 11, v_currMacroScope_969_);
    leanh::lean_ctor_set(v___x_975_, 12, v_cancelTk_x3f_971_);
    leanh::lean_ctor_set(v___x_975_, 13, v_inheritedTraceOptions_973_);
    leanh::lean_ctor_set_uint8(
        v___x_975_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 14) as u32,
        v_diag_970_,
    );
    leanh::lean_ctor_set_uint8(
        v___x_975_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 14 + 1) as u32,
        v_suppressElabErrors_972_,
    );
    v___x_976_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_isConstructorApp_x27_x3f_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6___redArg(v_msg_952_, v___y_953_, v___y_954_, v___x_975_, v___y_956_);
    leanh::lean_dec_ref_known(v___x_975_, 14);
    return v___x_976_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_isConstructorApp_x27_x3f_spec__0_spec__0_spec__1_spec__2_spec__4___redArg___boxed(
    mut v_ref_977_: *mut leanh::LeanObject,
    mut v_msg_978_: *mut leanh::LeanObject,
    mut v___y_979_: *mut leanh::LeanObject,
    mut v___y_980_: *mut leanh::LeanObject,
    mut v___y_981_: *mut leanh::LeanObject,
    mut v___y_982_: *mut leanh::LeanObject,
    mut v___y_983_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_984_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_984_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_isConstructorApp_x27_x3f_spec__0_spec__0_spec__1_spec__2_spec__4___redArg(v_ref_977_, v_msg_978_, v___y_979_, v___y_980_, v___y_981_, v___y_982_);
    leanh::lean_dec(v___y_982_);
    leanh::lean_dec_ref(v___y_981_);
    leanh::lean_dec(v___y_980_);
    leanh::lean_dec_ref(v___y_979_);
    leanh::lean_dec(v_ref_977_);
    return v_res_984_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_isConstructorApp_x27_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__0()
-> *mut leanh::LeanObject {
    let mut v___x_985_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_985_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(
        leanh::lean_box(0),
        leanh::lean_box(0),
    );
    return v___x_985_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_isConstructorApp_x27_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_986_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_987_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_986_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_isConstructorApp_x27_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_isConstructorApp_x27_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__0_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_isConstructorApp_x27_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__0);
    v___x_987_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_987_, 0, v___x_986_);
    return v___x_987_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_isConstructorApp_x27_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__2()
-> *mut leanh::LeanObject {
    let mut v___x_988_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_989_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_990_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_988_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_isConstructorApp_x27_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_isConstructorApp_x27_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__1_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_isConstructorApp_x27_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__1);
    v___x_989_ = leanh::lean_unsigned_to_nat(0);
    v___x_990_ = leanh::lean_alloc_ctor(0, 10, (0) as u32);
    leanh::lean_ctor_set(v___x_990_, 0, v___x_989_);
    leanh::lean_ctor_set(v___x_990_, 1, v___x_989_);
    leanh::lean_ctor_set(v___x_990_, 2, v___x_989_);
    leanh::lean_ctor_set(v___x_990_, 3, v___x_989_);
    leanh::lean_ctor_set(v___x_990_, 4, v___x_988_);
    leanh::lean_ctor_set(v___x_990_, 5, v___x_988_);
    leanh::lean_ctor_set(v___x_990_, 6, v___x_988_);
    leanh::lean_ctor_set(v___x_990_, 7, v___x_988_);
    leanh::lean_ctor_set(v___x_990_, 8, v___x_988_);
    leanh::lean_ctor_set(v___x_990_, 9, v___x_988_);
    return v___x_990_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_isConstructorApp_x27_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__3()
-> *mut leanh::LeanObject {
    let mut v___x_991_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_992_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_993_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_991_ = leanh::lean_unsigned_to_nat(32);
    v___x_992_ = lean_mk_empty_array_with_capacity(v___x_991_);
    v___x_993_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_993_, 0, v___x_992_);
    return v___x_993_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_isConstructorApp_x27_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__4()
-> *mut leanh::LeanObject {
    let mut v___x_994_: usize = 0;
    let mut v___x_995_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_996_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_997_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_998_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_999_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_994_ = 5usize;
    v___x_995_ = leanh::lean_unsigned_to_nat(0);
    v___x_996_ = leanh::lean_unsigned_to_nat(32);
    v___x_997_ = lean_mk_empty_array_with_capacity(v___x_996_);
    v___x_998_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_isConstructorApp_x27_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__3), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_isConstructorApp_x27_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__3_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_isConstructorApp_x27_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__3);
    v___x_999_ = leanh::lean_alloc_ctor(0, 4, (core::mem::size_of::<usize>() * 1) as u32);
    leanh::lean_ctor_set(v___x_999_, 0, v___x_998_);
    leanh::lean_ctor_set(v___x_999_, 1, v___x_997_);
    leanh::lean_ctor_set(v___x_999_, 2, v___x_995_);
    leanh::lean_ctor_set(v___x_999_, 3, v___x_995_);
    leanh::lean_ctor_set_usize(v___x_999_, 4, v___x_994_);
    return v___x_999_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_isConstructorApp_x27_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__5()
-> *mut leanh::LeanObject {
    let mut v___x_1000_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1001_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1002_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1003_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1000_ = leanh::lean_box(1);
    v___x_1001_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_isConstructorApp_x27_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__4), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_isConstructorApp_x27_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__4_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_isConstructorApp_x27_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__4);
    v___x_1002_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_isConstructorApp_x27_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_isConstructorApp_x27_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__1_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_isConstructorApp_x27_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__1);
    v___x_1003_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_1003_, 0, v___x_1002_);
    leanh::lean_ctor_set(v___x_1003_, 1, v___x_1001_);
    leanh::lean_ctor_set(v___x_1003_, 2, v___x_1000_);
    return v___x_1003_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_isConstructorApp_x27_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__7()
-> *mut leanh::LeanObject {
    let mut v___x_1005_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1006_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1005_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_isConstructorApp_x27_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__6;
    v___x_1006_ = l_Lean_stringToMessageData(v___x_1005_);
    return v___x_1006_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_isConstructorApp_x27_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__9()
-> *mut leanh::LeanObject {
    let mut v___x_1008_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1009_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1008_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_isConstructorApp_x27_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__8;
    v___x_1009_ = l_Lean_stringToMessageData(v___x_1008_);
    return v___x_1009_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_isConstructorApp_x27_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__11()
-> *mut leanh::LeanObject {
    let mut v___x_1011_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1012_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1011_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_isConstructorApp_x27_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__10;
    v___x_1012_ = l_Lean_stringToMessageData(v___x_1011_);
    return v___x_1012_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_isConstructorApp_x27_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__13()
-> *mut leanh::LeanObject {
    let mut v___x_1014_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1015_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1014_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_isConstructorApp_x27_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__12;
    v___x_1015_ = l_Lean_stringToMessageData(v___x_1014_);
    return v___x_1015_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_isConstructorApp_x27_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__15()
-> *mut leanh::LeanObject {
    let mut v___x_1017_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1018_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1017_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_isConstructorApp_x27_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__14;
    v___x_1018_ = l_Lean_stringToMessageData(v___x_1017_);
    return v___x_1018_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_isConstructorApp_x27_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__17()
-> *mut leanh::LeanObject {
    let mut v___x_1020_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1021_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1020_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_isConstructorApp_x27_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__16;
    v___x_1021_ = l_Lean_stringToMessageData(v___x_1020_);
    return v___x_1021_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_isConstructorApp_x27_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__19()
-> *mut leanh::LeanObject {
    let mut v___x_1023_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1024_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1023_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_isConstructorApp_x27_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__18;
    v___x_1024_ = l_Lean_stringToMessageData(v___x_1023_);
    return v___x_1024_;
}
pub unsafe fn l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_isConstructorApp_x27_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg(
    mut v_msg_1025_: *mut leanh::LeanObject,
    mut v_declHint_1026_: *mut leanh::LeanObject,
    mut v___y_1027_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1029_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_1030_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1031_: u8 = 0;
    let mut v_isExporting_1032_: u8 = 0;
    let mut v___x_1033_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1034_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1035_: u8 = 0;
    let mut v___x_1036_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1037_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1038_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1039_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1040_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1041_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_c_1042_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1043_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1044_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1045_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1046_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1047_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1048_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1049_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1050_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1051_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1053_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1054_: u8 = 0;
    let mut v___x_1055_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1056_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1057_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_mod_1058_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1059_: u8 = 0;
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
    let mut v___x_1071_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1072_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1073_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1074_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1075_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1076_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1077_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1078_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1079_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1080_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1081_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1082_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1084_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1085_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1086_: u8 = 0;
    let mut v___x_1087_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1029_ = lean_st_ref_get(v___y_1027_);
                v_env_1030_ = leanh::lean_ctor_get(v___x_1029_, 0);
                leanh::lean_inc_ref(v_env_1030_);
                leanh::lean_dec(v___x_1029_);
                v___x_1031_ = l_Lean_Name_isAnonymous(v_declHint_1026_);
                if v___x_1031_ == 0 {
                    v_isExporting_1032_ = leanh::lean_ctor_get_uint8(
                        v_env_1030_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 8) as u32,
                    );
                    if v_isExporting_1032_ == 0 {
                        leanh::lean_dec_ref(v_env_1030_);
                        leanh::lean_dec(v_declHint_1026_);
                        v___x_1033_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v___x_1033_, 0, v_msg_1025_);
                        return v___x_1033_;
                    } else {
                        leanh::lean_inc_ref(v_env_1030_);
                        v___x_1034_ = l_Lean_Environment_setExporting(v_env_1030_, v___x_1031_);
                        leanh::lean_inc(v_declHint_1026_);
                        leanh::lean_inc_ref(v___x_1034_);
                        v___x_1035_ = l_Lean_Environment_contains(
                            v___x_1034_,
                            v_declHint_1026_,
                            v_isExporting_1032_,
                        );
                        if v___x_1035_ == 0 {
                            leanh::lean_dec_ref(v___x_1034_);
                            leanh::lean_dec_ref(v_env_1030_);
                            leanh::lean_dec(v_declHint_1026_);
                            v___x_1036_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                            leanh::lean_ctor_set(v___x_1036_, 0, v_msg_1025_);
                            return v___x_1036_;
                        } else {
                            v___x_1037_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_isConstructorApp_x27_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__2), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_isConstructorApp_x27_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__2_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_isConstructorApp_x27_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__2);
                            v___x_1038_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_isConstructorApp_x27_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__5), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_isConstructorApp_x27_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__5_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_isConstructorApp_x27_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__5);
                            v___x_1039_ = l_Lean_Options_empty;
                            v___x_1040_ = leanh::lean_alloc_ctor(0, 4, (0) as u32);
                            leanh::lean_ctor_set(v___x_1040_, 0, v___x_1034_);
                            leanh::lean_ctor_set(v___x_1040_, 1, v___x_1037_);
                            leanh::lean_ctor_set(v___x_1040_, 2, v___x_1038_);
                            leanh::lean_ctor_set(v___x_1040_, 3, v___x_1039_);
                            leanh::lean_inc(v_declHint_1026_);
                            v___x_1041_ =
                                l_Lean_MessageData_ofConstName(v_declHint_1026_, v___x_1031_);
                            v_c_1042_ = leanh::lean_alloc_ctor(3, 2, (0) as u32);
                            leanh::lean_ctor_set(v_c_1042_, 0, v___x_1040_);
                            leanh::lean_ctor_set(v_c_1042_, 1, v___x_1041_);
                            v___x_1043_ = l_Lean_Environment_getModuleIdxFor_x3f(
                                v_env_1030_,
                                v_declHint_1026_,
                            );
                            if leanh::lean_obj_tag(v___x_1043_) == 0 {
                                leanh::lean_dec_ref(v_env_1030_);
                                leanh::lean_dec(v_declHint_1026_);
                                v___x_1044_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_isConstructorApp_x27_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__7), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_isConstructorApp_x27_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__7_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_isConstructorApp_x27_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__7);
                                v___x_1045_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                                leanh::lean_ctor_set(v___x_1045_, 0, v___x_1044_);
                                leanh::lean_ctor_set(v___x_1045_, 1, v_c_1042_);
                                v___x_1046_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_isConstructorApp_x27_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__9), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_isConstructorApp_x27_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__9_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_isConstructorApp_x27_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__9);
                                v___x_1047_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                                leanh::lean_ctor_set(v___x_1047_, 0, v___x_1045_);
                                leanh::lean_ctor_set(v___x_1047_, 1, v___x_1046_);
                                v___x_1048_ = l_Lean_MessageData_note(v___x_1047_);
                                v___x_1049_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                                leanh::lean_ctor_set(v___x_1049_, 0, v_msg_1025_);
                                leanh::lean_ctor_set(v___x_1049_, 1, v___x_1048_);
                                v___x_1050_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                                leanh::lean_ctor_set(v___x_1050_, 0, v___x_1049_);
                                return v___x_1050_;
                            } else {
                                v_val_1051_ = leanh::lean_ctor_get(v___x_1043_, 0);
                                v_isSharedCheck_1086_ =
                                    (!leanh::lean_is_exclusive(v___x_1043_)) as u8;
                                if v_isSharedCheck_1086_ == 0 {
                                    v___x_1053_ = v___x_1043_;
                                    v_isShared_1054_ = v_isSharedCheck_1086_;
                                    state = 1;
                                    continue;
                                } else {
                                    leanh::lean_inc(v_val_1051_);
                                    leanh::lean_dec(v___x_1043_);
                                    v___x_1053_ = leanh::lean_box(0);
                                    v_isShared_1054_ = v_isSharedCheck_1086_;
                                    state = 1;
                                    continue;
                                }
                            }
                        }
                    }
                } else {
                    leanh::lean_dec_ref(v_env_1030_);
                    leanh::lean_dec(v_declHint_1026_);
                    v___x_1087_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_1087_, 0, v_msg_1025_);
                    return v___x_1087_;
                }
            }
            1 => {
                v___x_1055_ = leanh::lean_box(0);
                v___x_1056_ = l_Lean_Environment_header(v_env_1030_);
                leanh::lean_dec_ref(v_env_1030_);
                v___x_1057_ = l_Lean_EnvironmentHeader_moduleNames(v___x_1056_);
                v_mod_1058_ = lean_array_get(v___x_1055_, v___x_1057_, v_val_1051_);
                leanh::lean_dec(v_val_1051_);
                leanh::lean_dec_ref(v___x_1057_);
                v___x_1059_ = l_Lean_isPrivateName(v_declHint_1026_);
                leanh::lean_dec(v_declHint_1026_);
                if v___x_1059_ == 0 {
                    v___x_1060_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_isConstructorApp_x27_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__11), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_isConstructorApp_x27_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__11_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_isConstructorApp_x27_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__11);
                    v___x_1061_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_1061_, 0, v___x_1060_);
                    leanh::lean_ctor_set(v___x_1061_, 1, v_c_1042_);
                    v___x_1062_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_isConstructorApp_x27_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__13), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_isConstructorApp_x27_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__13_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_isConstructorApp_x27_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__13);
                    v___x_1063_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_1063_, 0, v___x_1061_);
                    leanh::lean_ctor_set(v___x_1063_, 1, v___x_1062_);
                    v___x_1064_ = l_Lean_MessageData_ofName(v_mod_1058_);
                    v___x_1065_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_1065_, 0, v___x_1063_);
                    leanh::lean_ctor_set(v___x_1065_, 1, v___x_1064_);
                    v___x_1066_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_isConstructorApp_x27_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__15), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_isConstructorApp_x27_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__15_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_isConstructorApp_x27_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__15);
                    v___x_1067_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_1067_, 0, v___x_1065_);
                    leanh::lean_ctor_set(v___x_1067_, 1, v___x_1066_);
                    v___x_1068_ = l_Lean_MessageData_note(v___x_1067_);
                    v___x_1069_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_1069_, 0, v_msg_1025_);
                    leanh::lean_ctor_set(v___x_1069_, 1, v___x_1068_);
                    if v_isShared_1054_ == 0 {
                        leanh::lean_ctor_set_tag(v___x_1053_, 0);
                        leanh::lean_ctor_set(v___x_1053_, 0, v___x_1069_);
                        v___x_1071_ = v___x_1053_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_1072_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1072_, 0, v___x_1069_);
                        v___x_1071_ = v_reuseFailAlloc_1072_;
                        state = 2;
                        continue;
                    }
                } else {
                    v___x_1073_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_isConstructorApp_x27_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__7), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_isConstructorApp_x27_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__7_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_isConstructorApp_x27_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__7);
                    v___x_1074_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_1074_, 0, v___x_1073_);
                    leanh::lean_ctor_set(v___x_1074_, 1, v_c_1042_);
                    v___x_1075_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_isConstructorApp_x27_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__17), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_isConstructorApp_x27_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__17_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_isConstructorApp_x27_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__17);
                    v___x_1076_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_1076_, 0, v___x_1074_);
                    leanh::lean_ctor_set(v___x_1076_, 1, v___x_1075_);
                    v___x_1077_ = l_Lean_MessageData_ofName(v_mod_1058_);
                    v___x_1078_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_1078_, 0, v___x_1076_);
                    leanh::lean_ctor_set(v___x_1078_, 1, v___x_1077_);
                    v___x_1079_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_isConstructorApp_x27_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__19), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_isConstructorApp_x27_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__19_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_isConstructorApp_x27_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__19);
                    v___x_1080_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_1080_, 0, v___x_1078_);
                    leanh::lean_ctor_set(v___x_1080_, 1, v___x_1079_);
                    v___x_1081_ = l_Lean_MessageData_note(v___x_1080_);
                    v___x_1082_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_1082_, 0, v_msg_1025_);
                    leanh::lean_ctor_set(v___x_1082_, 1, v___x_1081_);
                    if v_isShared_1054_ == 0 {
                        leanh::lean_ctor_set_tag(v___x_1053_, 0);
                        leanh::lean_ctor_set(v___x_1053_, 0, v___x_1082_);
                        v___x_1084_ = v___x_1053_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_1085_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1085_, 0, v___x_1082_);
                        v___x_1084_ = v_reuseFailAlloc_1085_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_1071_;
            }
            3 => {
                return v___x_1084_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_isConstructorApp_x27_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___boxed(
    mut v_msg_1088_: *mut leanh::LeanObject,
    mut v_declHint_1089_: *mut leanh::LeanObject,
    mut v___y_1090_: *mut leanh::LeanObject,
    mut v___y_1091_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1092_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1092_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_isConstructorApp_x27_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg(v_msg_1088_, v_declHint_1089_, v___y_1090_);
    leanh::lean_dec(v___y_1090_);
    return v_res_1092_;
}
pub unsafe fn l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_isConstructorApp_x27_x3f_spec__0_spec__0_spec__1_spec__2_spec__3(
    mut v_msg_1093_: *mut leanh::LeanObject,
    mut v_declHint_1094_: *mut leanh::LeanObject,
    mut v___y_1095_: *mut leanh::LeanObject,
    mut v___y_1096_: *mut leanh::LeanObject,
    mut v___y_1097_: *mut leanh::LeanObject,
    mut v___y_1098_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1100_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1101_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1103_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1104_: u8 = 0;
    let mut v___x_1105_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1106_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1108_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1109_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1110_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1100_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_isConstructorApp_x27_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg(v_msg_1093_, v_declHint_1094_, v___y_1098_);
                v_a_1101_ = leanh::lean_ctor_get(v___x_1100_, 0);
                v_isSharedCheck_1110_ = (!leanh::lean_is_exclusive(v___x_1100_)) as u8;
                if v_isSharedCheck_1110_ == 0 {
                    v___x_1103_ = v___x_1100_;
                    v_isShared_1104_ = v_isSharedCheck_1110_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_a_1101_);
                    leanh::lean_dec(v___x_1100_);
                    v___x_1103_ = leanh::lean_box(0);
                    v_isShared_1104_ = v_isSharedCheck_1110_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_1105_ = l_Lean_unknownIdentifierMessageTag;
                v___x_1106_ = leanh::lean_alloc_ctor(8, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_1106_, 0, v___x_1105_);
                leanh::lean_ctor_set(v___x_1106_, 1, v_a_1101_);
                if v_isShared_1104_ == 0 {
                    leanh::lean_ctor_set(v___x_1103_, 0, v___x_1106_);
                    v___x_1108_ = v___x_1103_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1109_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1109_, 0, v___x_1106_);
                    v___x_1108_ = v_reuseFailAlloc_1109_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1108_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_isConstructorApp_x27_x3f_spec__0_spec__0_spec__1_spec__2_spec__3___boxed(
    mut v_msg_1111_: *mut leanh::LeanObject,
    mut v_declHint_1112_: *mut leanh::LeanObject,
    mut v___y_1113_: *mut leanh::LeanObject,
    mut v___y_1114_: *mut leanh::LeanObject,
    mut v___y_1115_: *mut leanh::LeanObject,
    mut v___y_1116_: *mut leanh::LeanObject,
    mut v___y_1117_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1118_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1118_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_isConstructorApp_x27_x3f_spec__0_spec__0_spec__1_spec__2_spec__3(v_msg_1111_, v_declHint_1112_, v___y_1113_, v___y_1114_, v___y_1115_, v___y_1116_);
    leanh::lean_dec(v___y_1116_);
    leanh::lean_dec_ref(v___y_1115_);
    leanh::lean_dec(v___y_1114_);
    leanh::lean_dec_ref(v___y_1113_);
    return v_res_1118_;
}
pub unsafe fn l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_isConstructorApp_x27_x3f_spec__0_spec__0_spec__1_spec__2___redArg(
    mut v_ref_1119_: *mut leanh::LeanObject,
    mut v_msg_1120_: *mut leanh::LeanObject,
    mut v_declHint_1121_: *mut leanh::LeanObject,
    mut v___y_1122_: *mut leanh::LeanObject,
    mut v___y_1123_: *mut leanh::LeanObject,
    mut v___y_1124_: *mut leanh::LeanObject,
    mut v___y_1125_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1127_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1128_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1129_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1127_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_isConstructorApp_x27_x3f_spec__0_spec__0_spec__1_spec__2_spec__3(v_msg_1120_, v_declHint_1121_, v___y_1122_, v___y_1123_, v___y_1124_, v___y_1125_);
    v_a_1128_ = leanh::lean_ctor_get(v___x_1127_, 0);
    leanh::lean_inc(v_a_1128_);
    leanh::lean_dec_ref(v___x_1127_);
    v___x_1129_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_isConstructorApp_x27_x3f_spec__0_spec__0_spec__1_spec__2_spec__4___redArg(v_ref_1119_, v_a_1128_, v___y_1122_, v___y_1123_, v___y_1124_, v___y_1125_);
    return v___x_1129_;
}
pub unsafe fn l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_isConstructorApp_x27_x3f_spec__0_spec__0_spec__1_spec__2___redArg___boxed(
    mut v_ref_1130_: *mut leanh::LeanObject,
    mut v_msg_1131_: *mut leanh::LeanObject,
    mut v_declHint_1132_: *mut leanh::LeanObject,
    mut v___y_1133_: *mut leanh::LeanObject,
    mut v___y_1134_: *mut leanh::LeanObject,
    mut v___y_1135_: *mut leanh::LeanObject,
    mut v___y_1136_: *mut leanh::LeanObject,
    mut v___y_1137_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1138_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1138_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_isConstructorApp_x27_x3f_spec__0_spec__0_spec__1_spec__2___redArg(v_ref_1130_, v_msg_1131_, v_declHint_1132_, v___y_1133_, v___y_1134_, v___y_1135_, v___y_1136_);
    leanh::lean_dec(v___y_1136_);
    leanh::lean_dec_ref(v___y_1135_);
    leanh::lean_dec(v___y_1134_);
    leanh::lean_dec_ref(v___y_1133_);
    leanh::lean_dec(v_ref_1130_);
    return v_res_1138_;
}
pub unsafe fn _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_isConstructorApp_x27_x3f_spec__0_spec__0_spec__1___redArg___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_1140_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1141_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1140_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_isConstructorApp_x27_x3f_spec__0_spec__0_spec__1___redArg___closed__0;
    v___x_1141_ = l_Lean_stringToMessageData(v___x_1140_);
    return v___x_1141_;
}
pub unsafe fn _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_isConstructorApp_x27_x3f_spec__0_spec__0_spec__1___redArg___closed__3()
-> *mut leanh::LeanObject {
    let mut v___x_1143_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1144_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1143_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_isConstructorApp_x27_x3f_spec__0_spec__0_spec__1___redArg___closed__2;
    v___x_1144_ = l_Lean_stringToMessageData(v___x_1143_);
    return v___x_1144_;
}
pub unsafe fn l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_isConstructorApp_x27_x3f_spec__0_spec__0_spec__1___redArg(
    mut v_ref_1145_: *mut leanh::LeanObject,
    mut v_constName_1146_: *mut leanh::LeanObject,
    mut v___y_1147_: *mut leanh::LeanObject,
    mut v___y_1148_: *mut leanh::LeanObject,
    mut v___y_1149_: *mut leanh::LeanObject,
    mut v___y_1150_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1152_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1153_: u8 = 0;
    let mut v___x_1154_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1155_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1156_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1157_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1158_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1152_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_isConstructorApp_x27_x3f_spec__0_spec__0_spec__1___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_isConstructorApp_x27_x3f_spec__0_spec__0_spec__1___redArg___closed__1_once), _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_isConstructorApp_x27_x3f_spec__0_spec__0_spec__1___redArg___closed__1);
    v___x_1153_ = 0;
    leanh::lean_inc(v_constName_1146_);
    v___x_1154_ = l_Lean_MessageData_ofConstName(v_constName_1146_, v___x_1153_);
    v___x_1155_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1155_, 0, v___x_1152_);
    leanh::lean_ctor_set(v___x_1155_, 1, v___x_1154_);
    v___x_1156_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_isConstructorApp_x27_x3f_spec__0_spec__0_spec__1___redArg___closed__3), core::ptr::addr_of_mut!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_isConstructorApp_x27_x3f_spec__0_spec__0_spec__1___redArg___closed__3_once), _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_isConstructorApp_x27_x3f_spec__0_spec__0_spec__1___redArg___closed__3);
    v___x_1157_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1157_, 0, v___x_1155_);
    leanh::lean_ctor_set(v___x_1157_, 1, v___x_1156_);
    v___x_1158_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_isConstructorApp_x27_x3f_spec__0_spec__0_spec__1_spec__2___redArg(v_ref_1145_, v___x_1157_, v_constName_1146_, v___y_1147_, v___y_1148_, v___y_1149_, v___y_1150_);
    return v___x_1158_;
}
pub unsafe fn l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_isConstructorApp_x27_x3f_spec__0_spec__0_spec__1___redArg___boxed(
    mut v_ref_1159_: *mut leanh::LeanObject,
    mut v_constName_1160_: *mut leanh::LeanObject,
    mut v___y_1161_: *mut leanh::LeanObject,
    mut v___y_1162_: *mut leanh::LeanObject,
    mut v___y_1163_: *mut leanh::LeanObject,
    mut v___y_1164_: *mut leanh::LeanObject,
    mut v___y_1165_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1166_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1166_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_isConstructorApp_x27_x3f_spec__0_spec__0_spec__1___redArg(v_ref_1159_, v_constName_1160_, v___y_1161_, v___y_1162_, v___y_1163_, v___y_1164_);
    leanh::lean_dec(v___y_1164_);
    leanh::lean_dec_ref(v___y_1163_);
    leanh::lean_dec(v___y_1162_);
    leanh::lean_dec_ref(v___y_1161_);
    leanh::lean_dec(v_ref_1159_);
    return v_res_1166_;
}
pub unsafe fn l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_isConstructorApp_x27_x3f_spec__0_spec__0___redArg(
    mut v_constName_1167_: *mut leanh::LeanObject,
    mut v___y_1168_: *mut leanh::LeanObject,
    mut v___y_1169_: *mut leanh::LeanObject,
    mut v___y_1170_: *mut leanh::LeanObject,
    mut v___y_1171_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_ref_1173_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1174_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_ref_1173_ = leanh::lean_ctor_get(v___y_1170_, 5);
    v___x_1174_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_isConstructorApp_x27_x3f_spec__0_spec__0_spec__1___redArg(v_ref_1173_, v_constName_1167_, v___y_1168_, v___y_1169_, v___y_1170_, v___y_1171_);
    return v___x_1174_;
}
pub unsafe fn l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_isConstructorApp_x27_x3f_spec__0_spec__0___redArg___boxed(
    mut v_constName_1175_: *mut leanh::LeanObject,
    mut v___y_1176_: *mut leanh::LeanObject,
    mut v___y_1177_: *mut leanh::LeanObject,
    mut v___y_1178_: *mut leanh::LeanObject,
    mut v___y_1179_: *mut leanh::LeanObject,
    mut v___y_1180_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1181_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1181_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_isConstructorApp_x27_x3f_spec__0_spec__0___redArg(v_constName_1175_, v___y_1176_, v___y_1177_, v___y_1178_, v___y_1179_);
    leanh::lean_dec(v___y_1179_);
    leanh::lean_dec_ref(v___y_1178_);
    leanh::lean_dec(v___y_1177_);
    leanh::lean_dec_ref(v___y_1176_);
    return v_res_1181_;
}
pub unsafe fn l_Lean_getConstInfo___at___00Lean_Meta_isConstructorApp_x27_x3f_spec__0(
    mut v_constName_1182_: *mut leanh::LeanObject,
    mut v___y_1183_: *mut leanh::LeanObject,
    mut v___y_1184_: *mut leanh::LeanObject,
    mut v___y_1185_: *mut leanh::LeanObject,
    mut v___y_1186_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1188_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_1189_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1190_: u8 = 0;
    let mut v___x_1191_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1192_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1193_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1195_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1196_: u8 = 0;
    let mut v___x_1198_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1199_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1200_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1188_ = lean_st_ref_get(v___y_1186_);
                v_env_1189_ = leanh::lean_ctor_get(v___x_1188_, 0);
                leanh::lean_inc_ref(v_env_1189_);
                leanh::lean_dec(v___x_1188_);
                v___x_1190_ = 0;
                leanh::lean_inc(v_constName_1182_);
                v___x_1191_ =
                    l_Lean_Environment_find_x3f(v_env_1189_, v_constName_1182_, v___x_1190_);
                if leanh::lean_obj_tag(v___x_1191_) == 0 {
                    v___x_1192_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_isConstructorApp_x27_x3f_spec__0_spec__0___redArg(v_constName_1182_, v___y_1183_, v___y_1184_, v___y_1185_, v___y_1186_);
                    return v___x_1192_;
                } else {
                    leanh::lean_dec(v_constName_1182_);
                    v_val_1193_ = leanh::lean_ctor_get(v___x_1191_, 0);
                    v_isSharedCheck_1200_ = (!leanh::lean_is_exclusive(v___x_1191_)) as u8;
                    if v_isSharedCheck_1200_ == 0 {
                        v___x_1195_ = v___x_1191_;
                        v_isShared_1196_ = v_isSharedCheck_1200_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_val_1193_);
                        leanh::lean_dec(v___x_1191_);
                        v___x_1195_ = leanh::lean_box(0);
                        v_isShared_1196_ = v_isSharedCheck_1200_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_1196_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_1195_, 0);
                    v___x_1198_ = v___x_1195_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1199_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1199_, 0, v_val_1193_);
                    v___x_1198_ = v_reuseFailAlloc_1199_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1198_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_getConstInfo___at___00Lean_Meta_isConstructorApp_x27_x3f_spec__0___boxed(
    mut v_constName_1201_: *mut leanh::LeanObject,
    mut v___y_1202_: *mut leanh::LeanObject,
    mut v___y_1203_: *mut leanh::LeanObject,
    mut v___y_1204_: *mut leanh::LeanObject,
    mut v___y_1205_: *mut leanh::LeanObject,
    mut v___y_1206_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1207_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1207_ = l_Lean_getConstInfo___at___00Lean_Meta_isConstructorApp_x27_x3f_spec__0(
        v_constName_1201_,
        v___y_1202_,
        v___y_1203_,
        v___y_1204_,
        v___y_1205_,
    );
    leanh::lean_dec(v___y_1205_);
    leanh::lean_dec_ref(v___y_1204_);
    leanh::lean_dec(v___y_1203_);
    leanh::lean_dec_ref(v___y_1202_);
    return v_res_1207_;
}
pub unsafe fn l_Lean_Meta_isConstructorApp_x27_x3f(
    mut v_e_1213_: *mut leanh::LeanObject,
    mut v_a_1214_: *mut leanh::LeanObject,
    mut v_a_1215_: *mut leanh::LeanObject,
    mut v_a_1216_: *mut leanh::LeanObject,
    mut v_a_1217_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___y_1220_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1221_: u8 = 0;
    let mut v___x_1222_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1223_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1224_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1226_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1227_: u8 = 0;
    let mut v___x_1228_: u8 = 0;
    let mut v___x_1229_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1230_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1232_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1233_: u8 = 0;
    let mut v_val_1234_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1236_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1237_: u8 = 0;
    let mut v_snd_1238_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1239_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1240_: u8 = 0;
    let mut v___x_1241_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1242_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1243_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1245_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1246_: u8 = 0;
    let mut v_val_1247_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1249_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1251_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1252_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1253_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1254_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1256_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1257_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1258_: u8 = 0;
    let mut v_a_1259_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1261_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1262_: u8 = 0;
    let mut v___x_1264_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1265_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1266_: u8 = 0;
    let mut v___x_1267_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1269_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1270_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1271_: u8 = 0;
    let mut v___x_1272_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1273_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1274_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1275_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1276_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1277_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1278_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1279_: u8 = 0;
    let mut v_a_1280_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1282_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1283_: u8 = 0;
    let mut v___x_1285_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1286_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1287_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                leanh::lean_inc_ref(v_e_1213_);
                v___x_1229_ =
                    l_Lean_Meta_isOffset_x3f(v_e_1213_, v_a_1214_, v_a_1215_, v_a_1216_, v_a_1217_);
                if leanh::lean_obj_tag(v___x_1229_) == 0 {
                    v_a_1230_ = leanh::lean_ctor_get(v___x_1229_, 0);
                    v_isSharedCheck_1279_ = (!leanh::lean_is_exclusive(v___x_1229_)) as u8;
                    if v_isSharedCheck_1279_ == 0 {
                        v___x_1232_ = v___x_1229_;
                        v_isShared_1233_ = v_isSharedCheck_1279_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_1230_);
                        leanh::lean_dec(v___x_1229_);
                        v___x_1232_ = leanh::lean_box(0);
                        v_isShared_1233_ = v_isSharedCheck_1279_;
                        state = 3;
                        continue;
                    }
                } else {
                    leanh::lean_dec_ref(v_e_1213_);
                    v_a_1280_ = leanh::lean_ctor_get(v___x_1229_, 0);
                    v_isSharedCheck_1287_ = (!leanh::lean_is_exclusive(v___x_1229_)) as u8;
                    if v_isSharedCheck_1287_ == 0 {
                        v___x_1282_ = v___x_1229_;
                        v_isShared_1283_ = v_isSharedCheck_1287_;
                        state = 12;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_1280_);
                        leanh::lean_dec(v___x_1229_);
                        v___x_1282_ = leanh::lean_box(0);
                        v_isShared_1283_ = v_isSharedCheck_1287_;
                        state = 12;
                        continue;
                    }
                }
            }
            1 => {
                if v___y_1221_ == 0 {
                    leanh::lean_dec_ref(v___y_1220_);
                    v___x_1222_ = leanh::lean_box(0);
                    v___x_1223_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_1223_, 0, v___x_1222_);
                    return v___x_1223_;
                } else {
                    v___x_1224_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_1224_, 0, v___y_1220_);
                    return v___x_1224_;
                }
            }
            2 => {
                v___x_1227_ = l_Lean_Exception_isInterrupt(v_a_1226_);
                if v___x_1227_ == 0 {
                    leanh::lean_inc_ref(v_a_1226_);
                    v___x_1228_ = l_Lean_Exception_isRuntime(v_a_1226_);
                    v___y_1220_ = v_a_1226_;
                    v___y_1221_ = v___x_1228_;
                    state = 1;
                    continue;
                } else {
                    v___y_1220_ = v_a_1226_;
                    v___y_1221_ = v___x_1227_;
                    state = 1;
                    continue;
                }
            }
            3 => {
                if leanh::lean_obj_tag(v_a_1230_) == 1 {
                    leanh::lean_dec_ref(v_e_1213_);
                    v_val_1234_ = leanh::lean_ctor_get(v_a_1230_, 0);
                    v_isSharedCheck_1271_ = (!leanh::lean_is_exclusive(v_a_1230_)) as u8;
                    if v_isSharedCheck_1271_ == 0 {
                        v___x_1236_ = v_a_1230_;
                        v_isShared_1237_ = v_isSharedCheck_1271_;
                        state = 4;
                        continue;
                    } else {
                        leanh::lean_inc(v_val_1234_);
                        leanh::lean_dec(v_a_1230_);
                        v___x_1236_ = leanh::lean_box(0);
                        v_isShared_1237_ = v_isSharedCheck_1271_;
                        state = 4;
                        continue;
                    }
                } else {
                    leanh::lean_del_object(v___x_1232_);
                    leanh::lean_dec(v_a_1230_);
                    leanh::lean_inc_ref(v_e_1213_);
                    v___x_1272_ = l_Lean_Meta_isConstructorApp_x3f(
                        v_e_1213_, v_a_1214_, v_a_1215_, v_a_1216_, v_a_1217_,
                    );
                    if leanh::lean_obj_tag(v___x_1272_) == 0 {
                        v_a_1273_ = leanh::lean_ctor_get(v___x_1272_, 0);
                        leanh::lean_inc(v_a_1273_);
                        if leanh::lean_obj_tag(v_a_1273_) == 1 {
                            leanh::lean_dec_ref_known(v_a_1273_, 1);
                            leanh::lean_dec_ref(v_e_1213_);
                            return v___x_1272_;
                        } else {
                            leanh::lean_dec(v_a_1273_);
                            leanh::lean_dec_ref_known(v___x_1272_, 1);
                            leanh::lean_inc(v_a_1217_);
                            leanh::lean_inc_ref(v_a_1216_);
                            leanh::lean_inc(v_a_1215_);
                            leanh::lean_inc_ref(v_a_1214_);
                            v___x_1274_ =
                                lean_whnf(v_e_1213_, v_a_1214_, v_a_1215_, v_a_1216_, v_a_1217_);
                            if leanh::lean_obj_tag(v___x_1274_) == 0 {
                                v_a_1275_ = leanh::lean_ctor_get(v___x_1274_, 0);
                                leanh::lean_inc(v_a_1275_);
                                leanh::lean_dec_ref_known(v___x_1274_, 1);
                                v___x_1276_ = l_Lean_Meta_isConstructorApp_x3f(
                                    v_a_1275_, v_a_1214_, v_a_1215_, v_a_1216_, v_a_1217_,
                                );
                                if leanh::lean_obj_tag(v___x_1276_) == 0 {
                                    return v___x_1276_;
                                } else {
                                    v_a_1277_ = leanh::lean_ctor_get(v___x_1276_, 0);
                                    leanh::lean_inc(v_a_1277_);
                                    leanh::lean_dec_ref_known(v___x_1276_, 1);
                                    v_a_1226_ = v_a_1277_;
                                    state = 2;
                                    continue;
                                }
                            } else {
                                v_a_1278_ = leanh::lean_ctor_get(v___x_1274_, 0);
                                leanh::lean_inc(v_a_1278_);
                                leanh::lean_dec_ref_known(v___x_1274_, 1);
                                v_a_1226_ = v_a_1278_;
                                state = 2;
                                continue;
                            }
                        }
                    } else {
                        leanh::lean_dec_ref(v_e_1213_);
                        return v___x_1272_;
                    }
                }
            }
            4 => {
                v_snd_1238_ = leanh::lean_ctor_get(v_val_1234_, 1);
                leanh::lean_inc(v_snd_1238_);
                leanh::lean_dec(v_val_1234_);
                v___x_1239_ = leanh::lean_unsigned_to_nat(0);
                v___x_1240_ = lean_nat_dec_eq(v_snd_1238_, v___x_1239_);
                leanh::lean_dec(v_snd_1238_);
                if v___x_1240_ == 0 {
                    leanh::lean_del_object(v___x_1232_);
                    v___x_1241_ = l_Lean_Meta_isConstructorApp_x27_x3f___closed__2;
                    v___x_1242_ =
                        l_Lean_getConstInfo___at___00Lean_Meta_isConstructorApp_x27_x3f_spec__0(
                            v___x_1241_,
                            v_a_1214_,
                            v_a_1215_,
                            v_a_1216_,
                            v_a_1217_,
                        );
                    if leanh::lean_obj_tag(v___x_1242_) == 0 {
                        v_a_1243_ = leanh::lean_ctor_get(v___x_1242_, 0);
                        v_isSharedCheck_1258_ =
                            (!leanh::lean_is_exclusive(v___x_1242_)) as u8;
                        if v_isSharedCheck_1258_ == 0 {
                            v___x_1245_ = v___x_1242_;
                            v_isShared_1246_ = v_isSharedCheck_1258_;
                            state = 5;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_1243_);
                            leanh::lean_dec(v___x_1242_);
                            v___x_1245_ = leanh::lean_box(0);
                            v_isShared_1246_ = v_isSharedCheck_1258_;
                            state = 5;
                            continue;
                        }
                    } else {
                        leanh::lean_del_object(v___x_1236_);
                        v_a_1259_ = leanh::lean_ctor_get(v___x_1242_, 0);
                        v_isSharedCheck_1266_ =
                            (!leanh::lean_is_exclusive(v___x_1242_)) as u8;
                        if v_isSharedCheck_1266_ == 0 {
                            v___x_1261_ = v___x_1242_;
                            v_isShared_1262_ = v_isSharedCheck_1266_;
                            state = 9;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_1259_);
                            leanh::lean_dec(v___x_1242_);
                            v___x_1261_ = leanh::lean_box(0);
                            v_isShared_1262_ = v_isSharedCheck_1266_;
                            state = 9;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_del_object(v___x_1236_);
                    v___x_1267_ = leanh::lean_box(0);
                    if v_isShared_1233_ == 0 {
                        leanh::lean_ctor_set(v___x_1232_, 0, v___x_1267_);
                        v___x_1269_ = v___x_1232_;
                        state = 11;
                        continue;
                    } else {
                        v_reuseFailAlloc_1270_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1270_, 0, v___x_1267_);
                        v___x_1269_ = v_reuseFailAlloc_1270_;
                        state = 11;
                        continue;
                    }
                }
            }
            5 => {
                if leanh::lean_obj_tag(v_a_1243_) == 6 {
                    v_val_1247_ = leanh::lean_ctor_get(v_a_1243_, 0);
                    leanh::lean_inc_ref(v_val_1247_);
                    leanh::lean_dec_ref_known(v_a_1243_, 1);
                    if v_isShared_1237_ == 0 {
                        leanh::lean_ctor_set(v___x_1236_, 0, v_val_1247_);
                        v___x_1249_ = v___x_1236_;
                        state = 6;
                        continue;
                    } else {
                        v_reuseFailAlloc_1253_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1253_, 0, v_val_1247_);
                        v___x_1249_ = v_reuseFailAlloc_1253_;
                        state = 6;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v_a_1243_);
                    leanh::lean_del_object(v___x_1236_);
                    v___x_1254_ = leanh::lean_box(0);
                    if v_isShared_1246_ == 0 {
                        leanh::lean_ctor_set(v___x_1245_, 0, v___x_1254_);
                        v___x_1256_ = v___x_1245_;
                        state = 8;
                        continue;
                    } else {
                        v_reuseFailAlloc_1257_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1257_, 0, v___x_1254_);
                        v___x_1256_ = v_reuseFailAlloc_1257_;
                        state = 8;
                        continue;
                    }
                }
            }
            6 => {
                if v_isShared_1246_ == 0 {
                    leanh::lean_ctor_set(v___x_1245_, 0, v___x_1249_);
                    v___x_1251_ = v___x_1245_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_1252_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1252_, 0, v___x_1249_);
                    v___x_1251_ = v_reuseFailAlloc_1252_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_1251_;
            }
            8 => {
                return v___x_1256_;
            }
            9 => {
                if v_isShared_1262_ == 0 {
                    v___x_1264_ = v___x_1261_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_1265_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1265_, 0, v_a_1259_);
                    v___x_1264_ = v_reuseFailAlloc_1265_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_1264_;
            }
            11 => {
                return v___x_1269_;
            }
            12 => {
                if v_isShared_1283_ == 0 {
                    v___x_1285_ = v___x_1282_;
                    state = 13;
                    continue;
                } else {
                    v_reuseFailAlloc_1286_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1286_, 0, v_a_1280_);
                    v___x_1285_ = v_reuseFailAlloc_1286_;
                    state = 13;
                    continue;
                }
            }
            13 => {
                return v___x_1285_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_isConstructorApp_x27_x3f___boxed(
    mut v_e_1288_: *mut leanh::LeanObject,
    mut v_a_1289_: *mut leanh::LeanObject,
    mut v_a_1290_: *mut leanh::LeanObject,
    mut v_a_1291_: *mut leanh::LeanObject,
    mut v_a_1292_: *mut leanh::LeanObject,
    mut v_a_1293_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1294_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1294_ =
        l_Lean_Meta_isConstructorApp_x27_x3f(v_e_1288_, v_a_1289_, v_a_1290_, v_a_1291_, v_a_1292_);
    leanh::lean_dec(v_a_1292_);
    leanh::lean_dec_ref(v_a_1291_);
    leanh::lean_dec(v_a_1290_);
    leanh::lean_dec_ref(v_a_1289_);
    return v_res_1294_;
}
pub unsafe fn l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_isConstructorApp_x27_x3f_spec__0_spec__0(
    mut v_00_u03b1_1295_: *mut leanh::LeanObject,
    mut v_constName_1296_: *mut leanh::LeanObject,
    mut v___y_1297_: *mut leanh::LeanObject,
    mut v___y_1298_: *mut leanh::LeanObject,
    mut v___y_1299_: *mut leanh::LeanObject,
    mut v___y_1300_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1302_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1302_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_isConstructorApp_x27_x3f_spec__0_spec__0___redArg(v_constName_1296_, v___y_1297_, v___y_1298_, v___y_1299_, v___y_1300_);
    return v___x_1302_;
}
pub unsafe fn l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_isConstructorApp_x27_x3f_spec__0_spec__0___boxed(
    mut v_00_u03b1_1303_: *mut leanh::LeanObject,
    mut v_constName_1304_: *mut leanh::LeanObject,
    mut v___y_1305_: *mut leanh::LeanObject,
    mut v___y_1306_: *mut leanh::LeanObject,
    mut v___y_1307_: *mut leanh::LeanObject,
    mut v___y_1308_: *mut leanh::LeanObject,
    mut v___y_1309_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1310_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1310_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_isConstructorApp_x27_x3f_spec__0_spec__0(v_00_u03b1_1303_, v_constName_1304_, v___y_1305_, v___y_1306_, v___y_1307_, v___y_1308_);
    leanh::lean_dec(v___y_1308_);
    leanh::lean_dec_ref(v___y_1307_);
    leanh::lean_dec(v___y_1306_);
    leanh::lean_dec_ref(v___y_1305_);
    return v_res_1310_;
}
pub unsafe fn l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_isConstructorApp_x27_x3f_spec__0_spec__0_spec__1(
    mut v_00_u03b1_1311_: *mut leanh::LeanObject,
    mut v_ref_1312_: *mut leanh::LeanObject,
    mut v_constName_1313_: *mut leanh::LeanObject,
    mut v___y_1314_: *mut leanh::LeanObject,
    mut v___y_1315_: *mut leanh::LeanObject,
    mut v___y_1316_: *mut leanh::LeanObject,
    mut v___y_1317_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1319_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1319_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_isConstructorApp_x27_x3f_spec__0_spec__0_spec__1___redArg(v_ref_1312_, v_constName_1313_, v___y_1314_, v___y_1315_, v___y_1316_, v___y_1317_);
    return v___x_1319_;
}
pub unsafe fn l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_isConstructorApp_x27_x3f_spec__0_spec__0_spec__1___boxed(
    mut v_00_u03b1_1320_: *mut leanh::LeanObject,
    mut v_ref_1321_: *mut leanh::LeanObject,
    mut v_constName_1322_: *mut leanh::LeanObject,
    mut v___y_1323_: *mut leanh::LeanObject,
    mut v___y_1324_: *mut leanh::LeanObject,
    mut v___y_1325_: *mut leanh::LeanObject,
    mut v___y_1326_: *mut leanh::LeanObject,
    mut v___y_1327_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1328_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1328_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_isConstructorApp_x27_x3f_spec__0_spec__0_spec__1(v_00_u03b1_1320_, v_ref_1321_, v_constName_1322_, v___y_1323_, v___y_1324_, v___y_1325_, v___y_1326_);
    leanh::lean_dec(v___y_1326_);
    leanh::lean_dec_ref(v___y_1325_);
    leanh::lean_dec(v___y_1324_);
    leanh::lean_dec_ref(v___y_1323_);
    leanh::lean_dec(v_ref_1321_);
    return v_res_1328_;
}
pub unsafe fn l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_isConstructorApp_x27_x3f_spec__0_spec__0_spec__1_spec__2(
    mut v_00_u03b1_1329_: *mut leanh::LeanObject,
    mut v_ref_1330_: *mut leanh::LeanObject,
    mut v_msg_1331_: *mut leanh::LeanObject,
    mut v_declHint_1332_: *mut leanh::LeanObject,
    mut v___y_1333_: *mut leanh::LeanObject,
    mut v___y_1334_: *mut leanh::LeanObject,
    mut v___y_1335_: *mut leanh::LeanObject,
    mut v___y_1336_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1338_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1338_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_isConstructorApp_x27_x3f_spec__0_spec__0_spec__1_spec__2___redArg(v_ref_1330_, v_msg_1331_, v_declHint_1332_, v___y_1333_, v___y_1334_, v___y_1335_, v___y_1336_);
    return v___x_1338_;
}
pub unsafe fn l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_isConstructorApp_x27_x3f_spec__0_spec__0_spec__1_spec__2___boxed(
    mut v_00_u03b1_1339_: *mut leanh::LeanObject,
    mut v_ref_1340_: *mut leanh::LeanObject,
    mut v_msg_1341_: *mut leanh::LeanObject,
    mut v_declHint_1342_: *mut leanh::LeanObject,
    mut v___y_1343_: *mut leanh::LeanObject,
    mut v___y_1344_: *mut leanh::LeanObject,
    mut v___y_1345_: *mut leanh::LeanObject,
    mut v___y_1346_: *mut leanh::LeanObject,
    mut v___y_1347_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1348_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1348_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_isConstructorApp_x27_x3f_spec__0_spec__0_spec__1_spec__2(v_00_u03b1_1339_, v_ref_1340_, v_msg_1341_, v_declHint_1342_, v___y_1343_, v___y_1344_, v___y_1345_, v___y_1346_);
    leanh::lean_dec(v___y_1346_);
    leanh::lean_dec_ref(v___y_1345_);
    leanh::lean_dec(v___y_1344_);
    leanh::lean_dec_ref(v___y_1343_);
    leanh::lean_dec(v_ref_1340_);
    return v_res_1348_;
}
pub unsafe fn l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_isConstructorApp_x27_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4(
    mut v_msg_1349_: *mut leanh::LeanObject,
    mut v_declHint_1350_: *mut leanh::LeanObject,
    mut v___y_1351_: *mut leanh::LeanObject,
    mut v___y_1352_: *mut leanh::LeanObject,
    mut v___y_1353_: *mut leanh::LeanObject,
    mut v___y_1354_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1356_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1356_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_isConstructorApp_x27_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg(v_msg_1349_, v_declHint_1350_, v___y_1354_);
    return v___x_1356_;
}
pub unsafe fn l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_isConstructorApp_x27_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___boxed(
    mut v_msg_1357_: *mut leanh::LeanObject,
    mut v_declHint_1358_: *mut leanh::LeanObject,
    mut v___y_1359_: *mut leanh::LeanObject,
    mut v___y_1360_: *mut leanh::LeanObject,
    mut v___y_1361_: *mut leanh::LeanObject,
    mut v___y_1362_: *mut leanh::LeanObject,
    mut v___y_1363_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1364_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1364_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_isConstructorApp_x27_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4(v_msg_1357_, v_declHint_1358_, v___y_1359_, v___y_1360_, v___y_1361_, v___y_1362_);
    leanh::lean_dec(v___y_1362_);
    leanh::lean_dec_ref(v___y_1361_);
    leanh::lean_dec(v___y_1360_);
    leanh::lean_dec_ref(v___y_1359_);
    return v_res_1364_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_isConstructorApp_x27_x3f_spec__0_spec__0_spec__1_spec__2_spec__4(
    mut v_00_u03b1_1365_: *mut leanh::LeanObject,
    mut v_ref_1366_: *mut leanh::LeanObject,
    mut v_msg_1367_: *mut leanh::LeanObject,
    mut v___y_1368_: *mut leanh::LeanObject,
    mut v___y_1369_: *mut leanh::LeanObject,
    mut v___y_1370_: *mut leanh::LeanObject,
    mut v___y_1371_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1373_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1373_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_isConstructorApp_x27_x3f_spec__0_spec__0_spec__1_spec__2_spec__4___redArg(v_ref_1366_, v_msg_1367_, v___y_1368_, v___y_1369_, v___y_1370_, v___y_1371_);
    return v___x_1373_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_isConstructorApp_x27_x3f_spec__0_spec__0_spec__1_spec__2_spec__4___boxed(
    mut v_00_u03b1_1374_: *mut leanh::LeanObject,
    mut v_ref_1375_: *mut leanh::LeanObject,
    mut v_msg_1376_: *mut leanh::LeanObject,
    mut v___y_1377_: *mut leanh::LeanObject,
    mut v___y_1378_: *mut leanh::LeanObject,
    mut v___y_1379_: *mut leanh::LeanObject,
    mut v___y_1380_: *mut leanh::LeanObject,
    mut v___y_1381_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1382_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1382_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_isConstructorApp_x27_x3f_spec__0_spec__0_spec__1_spec__2_spec__4(v_00_u03b1_1374_, v_ref_1375_, v_msg_1376_, v___y_1377_, v___y_1378_, v___y_1379_, v___y_1380_);
    leanh::lean_dec(v___y_1380_);
    leanh::lean_dec_ref(v___y_1379_);
    leanh::lean_dec(v___y_1378_);
    leanh::lean_dec_ref(v___y_1377_);
    leanh::lean_dec(v_ref_1375_);
    return v_res_1382_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_isConstructorApp_x27_x3f_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6(
    mut v_00_u03b1_1383_: *mut leanh::LeanObject,
    mut v_msg_1384_: *mut leanh::LeanObject,
    mut v___y_1385_: *mut leanh::LeanObject,
    mut v___y_1386_: *mut leanh::LeanObject,
    mut v___y_1387_: *mut leanh::LeanObject,
    mut v___y_1388_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1390_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1390_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_isConstructorApp_x27_x3f_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6___redArg(v_msg_1384_, v___y_1385_, v___y_1386_, v___y_1387_, v___y_1388_);
    return v___x_1390_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_isConstructorApp_x27_x3f_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6___boxed(
    mut v_00_u03b1_1391_: *mut leanh::LeanObject,
    mut v_msg_1392_: *mut leanh::LeanObject,
    mut v___y_1393_: *mut leanh::LeanObject,
    mut v___y_1394_: *mut leanh::LeanObject,
    mut v___y_1395_: *mut leanh::LeanObject,
    mut v___y_1396_: *mut leanh::LeanObject,
    mut v___y_1397_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1398_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1398_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_isConstructorApp_x27_x3f_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6(v_00_u03b1_1391_, v_msg_1392_, v___y_1393_, v___y_1394_, v___y_1395_, v___y_1396_);
    leanh::lean_dec(v___y_1396_);
    leanh::lean_dec_ref(v___y_1395_);
    leanh::lean_dec(v___y_1394_);
    leanh::lean_dec_ref(v___y_1393_);
    return v_res_1398_;
}
pub unsafe fn l_Lean_Meta_isConstructorApp(
    mut v_e_1399_: *mut leanh::LeanObject,
    mut v_a_1400_: *mut leanh::LeanObject,
    mut v_a_1401_: *mut leanh::LeanObject,
    mut v_a_1402_: *mut leanh::LeanObject,
    mut v_a_1403_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1405_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1406_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1408_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1409_: u8 = 0;
    let mut v___x_1410_: u8 = 0;
    let mut v___x_1411_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1413_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1414_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1415_: u8 = 0;
    let mut v___x_1416_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1418_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1419_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1420_: u8 = 0;
    let mut v_a_1421_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1423_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1424_: u8 = 0;
    let mut v___x_1426_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1427_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1428_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1405_ = l_Lean_Meta_isConstructorApp_x3f(
                    v_e_1399_, v_a_1400_, v_a_1401_, v_a_1402_, v_a_1403_,
                );
                if leanh::lean_obj_tag(v___x_1405_) == 0 {
                    v_a_1406_ = leanh::lean_ctor_get(v___x_1405_, 0);
                    v_isSharedCheck_1420_ = (!leanh::lean_is_exclusive(v___x_1405_)) as u8;
                    if v_isSharedCheck_1420_ == 0 {
                        v___x_1408_ = v___x_1405_;
                        v_isShared_1409_ = v_isSharedCheck_1420_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_1406_);
                        leanh::lean_dec(v___x_1405_);
                        v___x_1408_ = leanh::lean_box(0);
                        v_isShared_1409_ = v_isSharedCheck_1420_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_1421_ = leanh::lean_ctor_get(v___x_1405_, 0);
                    v_isSharedCheck_1428_ = (!leanh::lean_is_exclusive(v___x_1405_)) as u8;
                    if v_isSharedCheck_1428_ == 0 {
                        v___x_1423_ = v___x_1405_;
                        v_isShared_1424_ = v_isSharedCheck_1428_;
                        state = 4;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_1421_);
                        leanh::lean_dec(v___x_1405_);
                        v___x_1423_ = leanh::lean_box(0);
                        v_isShared_1424_ = v_isSharedCheck_1428_;
                        state = 4;
                        continue;
                    }
                }
            }
            1 => {
                if leanh::lean_obj_tag(v_a_1406_) == 0 {
                    v___x_1410_ = 0;
                    v___x_1411_ = leanh::lean_box((v___x_1410_) as usize);
                    if v_isShared_1409_ == 0 {
                        leanh::lean_ctor_set(v___x_1408_, 0, v___x_1411_);
                        v___x_1413_ = v___x_1408_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_1414_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1414_, 0, v___x_1411_);
                        v___x_1413_ = v_reuseFailAlloc_1414_;
                        state = 2;
                        continue;
                    }
                } else {
                    leanh::lean_dec_ref_known(v_a_1406_, 1);
                    v___x_1415_ = 1;
                    v___x_1416_ = leanh::lean_box((v___x_1415_) as usize);
                    if v_isShared_1409_ == 0 {
                        leanh::lean_ctor_set(v___x_1408_, 0, v___x_1416_);
                        v___x_1418_ = v___x_1408_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_1419_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1419_, 0, v___x_1416_);
                        v___x_1418_ = v_reuseFailAlloc_1419_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_1413_;
            }
            3 => {
                return v___x_1418_;
            }
            4 => {
                if v_isShared_1424_ == 0 {
                    v___x_1426_ = v___x_1423_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_1427_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1427_, 0, v_a_1421_);
                    v___x_1426_ = v_reuseFailAlloc_1427_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_1426_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_isConstructorApp___boxed(
    mut v_e_1429_: *mut leanh::LeanObject,
    mut v_a_1430_: *mut leanh::LeanObject,
    mut v_a_1431_: *mut leanh::LeanObject,
    mut v_a_1432_: *mut leanh::LeanObject,
    mut v_a_1433_: *mut leanh::LeanObject,
    mut v_a_1434_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1435_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1435_ =
        l_Lean_Meta_isConstructorApp(v_e_1429_, v_a_1430_, v_a_1431_, v_a_1432_, v_a_1433_);
    leanh::lean_dec(v_a_1433_);
    leanh::lean_dec_ref(v_a_1432_);
    leanh::lean_dec(v_a_1431_);
    leanh::lean_dec_ref(v_a_1430_);
    return v_res_1435_;
}
pub unsafe fn l_Lean_Meta_isConstructorApp_x27(
    mut v_e_1436_: *mut leanh::LeanObject,
    mut v_a_1437_: *mut leanh::LeanObject,
    mut v_a_1438_: *mut leanh::LeanObject,
    mut v_a_1439_: *mut leanh::LeanObject,
    mut v_a_1440_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1442_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1443_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1444_: u8 = 0;
    let mut v___x_1445_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1446_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1447_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1448_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1450_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1451_: u8 = 0;
    let mut v___x_1453_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1454_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1455_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                leanh::lean_inc_ref(v_e_1436_);
                v___x_1442_ = l_Lean_Meta_isConstructorApp(
                    v_e_1436_, v_a_1437_, v_a_1438_, v_a_1439_, v_a_1440_,
                );
                if leanh::lean_obj_tag(v___x_1442_) == 0 {
                    v_a_1443_ = leanh::lean_ctor_get(v___x_1442_, 0);
                    leanh::lean_inc(v_a_1443_);
                    v___x_1444_ = (leanh::lean_unbox(v_a_1443_) as u8);
                    leanh::lean_dec(v_a_1443_);
                    if v___x_1444_ == 0 {
                        leanh::lean_dec_ref_known(v___x_1442_, 1);
                        leanh::lean_inc(v_a_1440_);
                        leanh::lean_inc_ref(v_a_1439_);
                        leanh::lean_inc(v_a_1438_);
                        leanh::lean_inc_ref(v_a_1437_);
                        v___x_1445_ =
                            lean_whnf(v_e_1436_, v_a_1437_, v_a_1438_, v_a_1439_, v_a_1440_);
                        if leanh::lean_obj_tag(v___x_1445_) == 0 {
                            v_a_1446_ = leanh::lean_ctor_get(v___x_1445_, 0);
                            leanh::lean_inc(v_a_1446_);
                            leanh::lean_dec_ref_known(v___x_1445_, 1);
                            v___x_1447_ = l_Lean_Meta_isConstructorApp(
                                v_a_1446_, v_a_1437_, v_a_1438_, v_a_1439_, v_a_1440_,
                            );
                            return v___x_1447_;
                        } else {
                            v_a_1448_ = leanh::lean_ctor_get(v___x_1445_, 0);
                            v_isSharedCheck_1455_ =
                                (!leanh::lean_is_exclusive(v___x_1445_)) as u8;
                            if v_isSharedCheck_1455_ == 0 {
                                v___x_1450_ = v___x_1445_;
                                v_isShared_1451_ = v_isSharedCheck_1455_;
                                state = 1;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_1448_);
                                leanh::lean_dec(v___x_1445_);
                                v___x_1450_ = leanh::lean_box(0);
                                v_isShared_1451_ = v_isSharedCheck_1455_;
                                state = 1;
                                continue;
                            }
                        }
                    } else {
                        leanh::lean_dec_ref(v_e_1436_);
                        return v___x_1442_;
                    }
                } else {
                    leanh::lean_dec_ref(v_e_1436_);
                    return v___x_1442_;
                }
            }
            1 => {
                if v_isShared_1451_ == 0 {
                    v___x_1453_ = v___x_1450_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1454_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1454_, 0, v_a_1448_);
                    v___x_1453_ = v_reuseFailAlloc_1454_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1453_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_isConstructorApp_x27___boxed(
    mut v_e_1456_: *mut leanh::LeanObject,
    mut v_a_1457_: *mut leanh::LeanObject,
    mut v_a_1458_: *mut leanh::LeanObject,
    mut v_a_1459_: *mut leanh::LeanObject,
    mut v_a_1460_: *mut leanh::LeanObject,
    mut v_a_1461_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1462_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1462_ =
        l_Lean_Meta_isConstructorApp_x27(v_e_1456_, v_a_1457_, v_a_1458_, v_a_1459_, v_a_1460_);
    leanh::lean_dec(v_a_1460_);
    leanh::lean_dec_ref(v_a_1459_);
    leanh::lean_dec(v_a_1458_);
    leanh::lean_dec_ref(v_a_1457_);
    return v_res_1462_;
}
pub unsafe fn _init_l_Lean_Meta_constructorApp_x3f___closed__0() -> *mut leanh::LeanObject {
    let mut v___x_1463_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_dummy_1464_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1463_ = leanh::lean_box(0);
    v_dummy_1464_ = l_Lean_Expr_sort___override(v___x_1463_);
    return v_dummy_1464_;
}
pub unsafe fn l_Lean_Meta_constructorApp_x3f(
    mut v_e_1465_: *mut leanh::LeanObject,
    mut v_a_1466_: *mut leanh::LeanObject,
    mut v_a_1467_: *mut leanh::LeanObject,
    mut v_a_1468_: *mut leanh::LeanObject,
    mut v_a_1469_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1471_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1472_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1474_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1475_: u8 = 0;
    let mut v___x_1476_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_declName_1477_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1478_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_1479_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1480_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1481_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1483_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1484_: u8 = 0;
    let mut v_numParams_1485_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_numFields_1486_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1487_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1488_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1489_: u8 = 0;
    let mut v___x_1490_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1492_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1493_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_dummy_1494_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1495_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1496_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1497_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1498_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1499_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1501_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1503_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1504_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1505_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1506_: u8 = 0;
    let mut v___x_1507_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1509_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1510_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1511_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1513_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1514_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1515_: u8 = 0;
    let mut v_a_1516_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1518_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1519_: u8 = 0;
    let mut v___x_1521_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1522_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1523_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1471_ =
                    l_Lean_Meta_litToCtor(v_e_1465_, v_a_1466_, v_a_1467_, v_a_1468_, v_a_1469_);
                if leanh::lean_obj_tag(v___x_1471_) == 0 {
                    v_a_1472_ = leanh::lean_ctor_get(v___x_1471_, 0);
                    v_isSharedCheck_1515_ = (!leanh::lean_is_exclusive(v___x_1471_)) as u8;
                    if v_isSharedCheck_1515_ == 0 {
                        v___x_1474_ = v___x_1471_;
                        v_isShared_1475_ = v_isSharedCheck_1515_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_1472_);
                        leanh::lean_dec(v___x_1471_);
                        v___x_1474_ = leanh::lean_box(0);
                        v_isShared_1475_ = v_isSharedCheck_1515_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_1516_ = leanh::lean_ctor_get(v___x_1471_, 0);
                    v_isSharedCheck_1523_ = (!leanh::lean_is_exclusive(v___x_1471_)) as u8;
                    if v_isSharedCheck_1523_ == 0 {
                        v___x_1518_ = v___x_1471_;
                        v_isShared_1519_ = v_isSharedCheck_1523_;
                        state = 8;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_1516_);
                        leanh::lean_dec(v___x_1471_);
                        v___x_1518_ = leanh::lean_box(0);
                        v_isShared_1519_ = v_isSharedCheck_1523_;
                        state = 8;
                        continue;
                    }
                }
            }
            1 => {
                v___x_1476_ = l_Lean_Expr_getAppFn(v_a_1472_);
                if leanh::lean_obj_tag(v___x_1476_) == 4 {
                    v_declName_1477_ = leanh::lean_ctor_get(v___x_1476_, 0);
                    leanh::lean_inc(v_declName_1477_);
                    leanh::lean_dec_ref_known(v___x_1476_, 2);
                    v___x_1478_ = lean_st_ref_get(v_a_1469_);
                    v_env_1479_ = leanh::lean_ctor_get(v___x_1478_, 0);
                    leanh::lean_inc_ref(v_env_1479_);
                    leanh::lean_dec(v___x_1478_);
                    v___x_1480_ =
                        l___private_Lean_Meta_CtorRecognizer_0__Lean_Meta_getConstructorVal_x3f(
                            v_env_1479_,
                            v_declName_1477_,
                        );
                    if leanh::lean_obj_tag(v___x_1480_) == 1 {
                        v_val_1481_ = leanh::lean_ctor_get(v___x_1480_, 0);
                        v_isSharedCheck_1506_ =
                            (!leanh::lean_is_exclusive(v___x_1480_)) as u8;
                        if v_isSharedCheck_1506_ == 0 {
                            v___x_1483_ = v___x_1480_;
                            v_isShared_1484_ = v_isSharedCheck_1506_;
                            state = 2;
                            continue;
                        } else {
                            leanh::lean_inc(v_val_1481_);
                            leanh::lean_dec(v___x_1480_);
                            v___x_1483_ = leanh::lean_box(0);
                            v_isShared_1484_ = v_isSharedCheck_1506_;
                            state = 2;
                            continue;
                        }
                    } else {
                        leanh::lean_dec(v___x_1480_);
                        leanh::lean_dec(v_a_1472_);
                        v___x_1507_ = leanh::lean_box(0);
                        if v_isShared_1475_ == 0 {
                            leanh::lean_ctor_set(v___x_1474_, 0, v___x_1507_);
                            v___x_1509_ = v___x_1474_;
                            state = 6;
                            continue;
                        } else {
                            v_reuseFailAlloc_1510_ =
                                leanh::lean_alloc_ctor(0, 1, (0) as u32);
                            leanh::lean_ctor_set(v_reuseFailAlloc_1510_, 0, v___x_1507_);
                            v___x_1509_ = v_reuseFailAlloc_1510_;
                            state = 6;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_dec_ref(v___x_1476_);
                    leanh::lean_dec(v_a_1472_);
                    v___x_1511_ = leanh::lean_box(0);
                    if v_isShared_1475_ == 0 {
                        leanh::lean_ctor_set(v___x_1474_, 0, v___x_1511_);
                        v___x_1513_ = v___x_1474_;
                        state = 7;
                        continue;
                    } else {
                        v_reuseFailAlloc_1514_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1514_, 0, v___x_1511_);
                        v___x_1513_ = v_reuseFailAlloc_1514_;
                        state = 7;
                        continue;
                    }
                }
            }
            2 => {
                v_numParams_1485_ = leanh::lean_ctor_get(v_val_1481_, 3);
                v_numFields_1486_ = leanh::lean_ctor_get(v_val_1481_, 4);
                v___x_1487_ = lean_nat_add(v_numParams_1485_, v_numFields_1486_);
                v___x_1488_ = l_Lean_Expr_getAppNumArgs(v_a_1472_);
                v___x_1489_ = lean_nat_dec_eq(v___x_1487_, v___x_1488_);
                leanh::lean_dec(v___x_1487_);
                if v___x_1489_ == 0 {
                    leanh::lean_dec(v___x_1488_);
                    leanh::lean_del_object(v___x_1483_);
                    leanh::lean_dec(v_val_1481_);
                    leanh::lean_dec(v_a_1472_);
                    v___x_1490_ = leanh::lean_box(0);
                    if v_isShared_1475_ == 0 {
                        leanh::lean_ctor_set(v___x_1474_, 0, v___x_1490_);
                        v___x_1492_ = v___x_1474_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_1493_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1493_, 0, v___x_1490_);
                        v___x_1492_ = v_reuseFailAlloc_1493_;
                        state = 3;
                        continue;
                    }
                } else {
                    v_dummy_1494_ = leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(l_Lean_Meta_constructorApp_x3f___closed__0),
                        core::ptr::addr_of_mut!(l_Lean_Meta_constructorApp_x3f___closed__0_once),
                        _init_l_Lean_Meta_constructorApp_x3f___closed__0,
                    );
                    leanh::lean_inc(v___x_1488_);
                    v___x_1495_ = lean_mk_array(v___x_1488_, v_dummy_1494_);
                    v___x_1496_ = leanh::lean_unsigned_to_nat(1);
                    v___x_1497_ = lean_nat_sub(v___x_1488_, v___x_1496_);
                    leanh::lean_dec(v___x_1488_);
                    v___x_1498_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(
                        v_a_1472_,
                        v___x_1495_,
                        v___x_1497_,
                    );
                    v___x_1499_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_1499_, 0, v_val_1481_);
                    leanh::lean_ctor_set(v___x_1499_, 1, v___x_1498_);
                    if v_isShared_1484_ == 0 {
                        leanh::lean_ctor_set(v___x_1483_, 0, v___x_1499_);
                        v___x_1501_ = v___x_1483_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_1505_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1505_, 0, v___x_1499_);
                        v___x_1501_ = v_reuseFailAlloc_1505_;
                        state = 4;
                        continue;
                    }
                }
            }
            3 => {
                return v___x_1492_;
            }
            4 => {
                if v_isShared_1475_ == 0 {
                    leanh::lean_ctor_set(v___x_1474_, 0, v___x_1501_);
                    v___x_1503_ = v___x_1474_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_1504_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1504_, 0, v___x_1501_);
                    v___x_1503_ = v_reuseFailAlloc_1504_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_1503_;
            }
            6 => {
                return v___x_1509_;
            }
            7 => {
                return v___x_1513_;
            }
            8 => {
                if v_isShared_1519_ == 0 {
                    v___x_1521_ = v___x_1518_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_1522_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1522_, 0, v_a_1516_);
                    v___x_1521_ = v_reuseFailAlloc_1522_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_1521_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_constructorApp_x3f___boxed(
    mut v_e_1524_: *mut leanh::LeanObject,
    mut v_a_1525_: *mut leanh::LeanObject,
    mut v_a_1526_: *mut leanh::LeanObject,
    mut v_a_1527_: *mut leanh::LeanObject,
    mut v_a_1528_: *mut leanh::LeanObject,
    mut v_a_1529_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1530_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1530_ =
        l_Lean_Meta_constructorApp_x3f(v_e_1524_, v_a_1525_, v_a_1526_, v_a_1527_, v_a_1528_);
    leanh::lean_dec(v_a_1528_);
    leanh::lean_dec_ref(v_a_1527_);
    leanh::lean_dec(v_a_1526_);
    leanh::lean_dec_ref(v_a_1525_);
    return v_res_1530_;
}
pub unsafe fn l_Lean_Meta_constructorApp_x27_x3f(
    mut v_e_1531_: *mut leanh::LeanObject,
    mut v_a_1532_: *mut leanh::LeanObject,
    mut v_a_1533_: *mut leanh::LeanObject,
    mut v_a_1534_: *mut leanh::LeanObject,
    mut v_a_1535_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___y_1538_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1539_: u8 = 0;
    let mut v___x_1540_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1541_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1542_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1544_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1545_: u8 = 0;
    let mut v___x_1546_: u8 = 0;
    let mut v___x_1547_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1548_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1550_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1551_: u8 = 0;
    let mut v_val_1552_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1554_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1555_: u8 = 0;
    let mut v_fst_1556_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1557_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1559_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1560_: u8 = 0;
    let mut v___x_1561_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1562_: u8 = 0;
    let mut v___x_1563_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1564_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1565_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1567_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1568_: u8 = 0;
    let mut v_val_1569_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1570_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1571_: u8 = 0;
    let mut v___x_1572_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1573_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1574_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1575_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1576_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1578_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1580_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1582_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1583_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1584_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1585_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1586_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1587_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1589_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1591_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1593_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1594_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1595_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1596_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1597_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1599_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1600_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1601_: u8 = 0;
    let mut v_a_1602_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1604_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1605_: u8 = 0;
    let mut v___x_1607_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1608_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1609_: u8 = 0;
    let mut v___x_1610_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1612_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1613_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1614_: u8 = 0;
    let mut v_isSharedCheck_1615_: u8 = 0;
    let mut v___x_1616_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1617_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1618_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1619_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1620_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1621_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1622_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1623_: u8 = 0;
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
                leanh::lean_inc_ref(v_e_1531_);
                v___x_1547_ =
                    l_Lean_Meta_isOffset_x3f(v_e_1531_, v_a_1532_, v_a_1533_, v_a_1534_, v_a_1535_);
                if leanh::lean_obj_tag(v___x_1547_) == 0 {
                    v_a_1548_ = leanh::lean_ctor_get(v___x_1547_, 0);
                    v_isSharedCheck_1623_ = (!leanh::lean_is_exclusive(v___x_1547_)) as u8;
                    if v_isSharedCheck_1623_ == 0 {
                        v___x_1550_ = v___x_1547_;
                        v_isShared_1551_ = v_isSharedCheck_1623_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_1548_);
                        leanh::lean_dec(v___x_1547_);
                        v___x_1550_ = leanh::lean_box(0);
                        v_isShared_1551_ = v_isSharedCheck_1623_;
                        state = 3;
                        continue;
                    }
                } else {
                    leanh::lean_dec_ref(v_e_1531_);
                    v_a_1624_ = leanh::lean_ctor_get(v___x_1547_, 0);
                    v_isSharedCheck_1631_ = (!leanh::lean_is_exclusive(v___x_1547_)) as u8;
                    if v_isSharedCheck_1631_ == 0 {
                        v___x_1626_ = v___x_1547_;
                        v_isShared_1627_ = v_isSharedCheck_1631_;
                        state = 17;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_1624_);
                        leanh::lean_dec(v___x_1547_);
                        v___x_1626_ = leanh::lean_box(0);
                        v_isShared_1627_ = v_isSharedCheck_1631_;
                        state = 17;
                        continue;
                    }
                }
            }
            1 => {
                if v___y_1539_ == 0 {
                    leanh::lean_dec_ref(v___y_1538_);
                    v___x_1540_ = leanh::lean_box(0);
                    v___x_1541_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_1541_, 0, v___x_1540_);
                    return v___x_1541_;
                } else {
                    v___x_1542_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_1542_, 0, v___y_1538_);
                    return v___x_1542_;
                }
            }
            2 => {
                v___x_1545_ = l_Lean_Exception_isInterrupt(v_a_1544_);
                if v___x_1545_ == 0 {
                    leanh::lean_inc_ref(v_a_1544_);
                    v___x_1546_ = l_Lean_Exception_isRuntime(v_a_1544_);
                    v___y_1538_ = v_a_1544_;
                    v___y_1539_ = v___x_1546_;
                    state = 1;
                    continue;
                } else {
                    v___y_1538_ = v_a_1544_;
                    v___y_1539_ = v___x_1545_;
                    state = 1;
                    continue;
                }
            }
            3 => {
                if leanh::lean_obj_tag(v_a_1548_) == 1 {
                    leanh::lean_dec_ref(v_e_1531_);
                    v_val_1552_ = leanh::lean_ctor_get(v_a_1548_, 0);
                    v_isSharedCheck_1615_ = (!leanh::lean_is_exclusive(v_a_1548_)) as u8;
                    if v_isSharedCheck_1615_ == 0 {
                        v___x_1554_ = v_a_1548_;
                        v_isShared_1555_ = v_isSharedCheck_1615_;
                        state = 4;
                        continue;
                    } else {
                        leanh::lean_inc(v_val_1552_);
                        leanh::lean_dec(v_a_1548_);
                        v___x_1554_ = leanh::lean_box(0);
                        v_isShared_1555_ = v_isSharedCheck_1615_;
                        state = 4;
                        continue;
                    }
                } else {
                    leanh::lean_del_object(v___x_1550_);
                    leanh::lean_dec(v_a_1548_);
                    leanh::lean_inc_ref(v_e_1531_);
                    v___x_1616_ = l_Lean_Meta_constructorApp_x3f(
                        v_e_1531_, v_a_1532_, v_a_1533_, v_a_1534_, v_a_1535_,
                    );
                    if leanh::lean_obj_tag(v___x_1616_) == 0 {
                        v_a_1617_ = leanh::lean_ctor_get(v___x_1616_, 0);
                        leanh::lean_inc(v_a_1617_);
                        if leanh::lean_obj_tag(v_a_1617_) == 1 {
                            leanh::lean_dec_ref_known(v_a_1617_, 1);
                            leanh::lean_dec_ref(v_e_1531_);
                            return v___x_1616_;
                        } else {
                            leanh::lean_dec(v_a_1617_);
                            leanh::lean_dec_ref_known(v___x_1616_, 1);
                            leanh::lean_inc(v_a_1535_);
                            leanh::lean_inc_ref(v_a_1534_);
                            leanh::lean_inc(v_a_1533_);
                            leanh::lean_inc_ref(v_a_1532_);
                            v___x_1618_ =
                                lean_whnf(v_e_1531_, v_a_1532_, v_a_1533_, v_a_1534_, v_a_1535_);
                            if leanh::lean_obj_tag(v___x_1618_) == 0 {
                                v_a_1619_ = leanh::lean_ctor_get(v___x_1618_, 0);
                                leanh::lean_inc(v_a_1619_);
                                leanh::lean_dec_ref_known(v___x_1618_, 1);
                                v___x_1620_ = l_Lean_Meta_constructorApp_x3f(
                                    v_a_1619_, v_a_1532_, v_a_1533_, v_a_1534_, v_a_1535_,
                                );
                                if leanh::lean_obj_tag(v___x_1620_) == 0 {
                                    return v___x_1620_;
                                } else {
                                    v_a_1621_ = leanh::lean_ctor_get(v___x_1620_, 0);
                                    leanh::lean_inc(v_a_1621_);
                                    leanh::lean_dec_ref_known(v___x_1620_, 1);
                                    v_a_1544_ = v_a_1621_;
                                    state = 2;
                                    continue;
                                }
                            } else {
                                v_a_1622_ = leanh::lean_ctor_get(v___x_1618_, 0);
                                leanh::lean_inc(v_a_1622_);
                                leanh::lean_dec_ref_known(v___x_1618_, 1);
                                v_a_1544_ = v_a_1622_;
                                state = 2;
                                continue;
                            }
                        }
                    } else {
                        leanh::lean_dec_ref(v_e_1531_);
                        return v___x_1616_;
                    }
                }
            }
            4 => {
                v_fst_1556_ = leanh::lean_ctor_get(v_val_1552_, 0);
                v_snd_1557_ = leanh::lean_ctor_get(v_val_1552_, 1);
                v_isSharedCheck_1614_ = (!leanh::lean_is_exclusive(v_val_1552_)) as u8;
                if v_isSharedCheck_1614_ == 0 {
                    v___x_1559_ = v_val_1552_;
                    v_isShared_1560_ = v_isSharedCheck_1614_;
                    state = 5;
                    continue;
                } else {
                    leanh::lean_inc(v_snd_1557_);
                    leanh::lean_inc(v_fst_1556_);
                    leanh::lean_dec(v_val_1552_);
                    v___x_1559_ = leanh::lean_box(0);
                    v_isShared_1560_ = v_isSharedCheck_1614_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v___x_1561_ = leanh::lean_unsigned_to_nat(0);
                v___x_1562_ = lean_nat_dec_eq(v_snd_1557_, v___x_1561_);
                if v___x_1562_ == 0 {
                    leanh::lean_del_object(v___x_1550_);
                    v___x_1563_ = l_Lean_Meta_isConstructorApp_x27_x3f___closed__2;
                    v___x_1564_ =
                        l_Lean_getConstInfo___at___00Lean_Meta_isConstructorApp_x27_x3f_spec__0(
                            v___x_1563_,
                            v_a_1532_,
                            v_a_1533_,
                            v_a_1534_,
                            v_a_1535_,
                        );
                    if leanh::lean_obj_tag(v___x_1564_) == 0 {
                        v_a_1565_ = leanh::lean_ctor_get(v___x_1564_, 0);
                        v_isSharedCheck_1601_ =
                            (!leanh::lean_is_exclusive(v___x_1564_)) as u8;
                        if v_isSharedCheck_1601_ == 0 {
                            v___x_1567_ = v___x_1564_;
                            v_isShared_1568_ = v_isSharedCheck_1601_;
                            state = 6;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_1565_);
                            leanh::lean_dec(v___x_1564_);
                            v___x_1567_ = leanh::lean_box(0);
                            v_isShared_1568_ = v_isSharedCheck_1601_;
                            state = 6;
                            continue;
                        }
                    } else {
                        leanh::lean_del_object(v___x_1559_);
                        leanh::lean_dec(v_snd_1557_);
                        leanh::lean_dec(v_fst_1556_);
                        leanh::lean_del_object(v___x_1554_);
                        v_a_1602_ = leanh::lean_ctor_get(v___x_1564_, 0);
                        v_isSharedCheck_1609_ =
                            (!leanh::lean_is_exclusive(v___x_1564_)) as u8;
                        if v_isSharedCheck_1609_ == 0 {
                            v___x_1604_ = v___x_1564_;
                            v_isShared_1605_ = v_isSharedCheck_1609_;
                            state = 14;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_1602_);
                            leanh::lean_dec(v___x_1564_);
                            v___x_1604_ = leanh::lean_box(0);
                            v_isShared_1605_ = v_isSharedCheck_1609_;
                            state = 14;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_del_object(v___x_1559_);
                    leanh::lean_dec(v_snd_1557_);
                    leanh::lean_dec(v_fst_1556_);
                    leanh::lean_del_object(v___x_1554_);
                    v___x_1610_ = leanh::lean_box(0);
                    if v_isShared_1551_ == 0 {
                        leanh::lean_ctor_set(v___x_1550_, 0, v___x_1610_);
                        v___x_1612_ = v___x_1550_;
                        state = 16;
                        continue;
                    } else {
                        v_reuseFailAlloc_1613_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1613_, 0, v___x_1610_);
                        v___x_1612_ = v_reuseFailAlloc_1613_;
                        state = 16;
                        continue;
                    }
                }
            }
            6 => {
                if leanh::lean_obj_tag(v_a_1565_) == 6 {
                    v_val_1569_ = leanh::lean_ctor_get(v_a_1565_, 0);
                    leanh::lean_inc_ref(v_val_1569_);
                    leanh::lean_dec_ref_known(v_a_1565_, 1);
                    v___x_1570_ = leanh::lean_unsigned_to_nat(1);
                    v___x_1571_ = lean_nat_dec_eq(v_snd_1557_, v___x_1570_);
                    if v___x_1571_ == 0 {
                        v___x_1572_ = lean_nat_sub(v_snd_1557_, v___x_1570_);
                        leanh::lean_dec(v_snd_1557_);
                        v___x_1573_ = l_Lean_mkNatLit(v___x_1572_);
                        v___x_1574_ = l_Lean_mkNatAdd(v_fst_1556_, v___x_1573_);
                        v___x_1575_ = lean_mk_empty_array_with_capacity(v___x_1570_);
                        v___x_1576_ = lean_array_push(v___x_1575_, v___x_1574_);
                        if v_isShared_1560_ == 0 {
                            leanh::lean_ctor_set(v___x_1559_, 1, v___x_1576_);
                            leanh::lean_ctor_set(v___x_1559_, 0, v_val_1569_);
                            v___x_1578_ = v___x_1559_;
                            state = 7;
                            continue;
                        } else {
                            v_reuseFailAlloc_1585_ =
                                leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            leanh::lean_ctor_set(v_reuseFailAlloc_1585_, 0, v_val_1569_);
                            leanh::lean_ctor_set(v_reuseFailAlloc_1585_, 1, v___x_1576_);
                            v___x_1578_ = v_reuseFailAlloc_1585_;
                            state = 7;
                            continue;
                        }
                    } else {
                        leanh::lean_dec(v_snd_1557_);
                        v___x_1586_ = lean_mk_empty_array_with_capacity(v___x_1570_);
                        v___x_1587_ = lean_array_push(v___x_1586_, v_fst_1556_);
                        if v_isShared_1560_ == 0 {
                            leanh::lean_ctor_set(v___x_1559_, 1, v___x_1587_);
                            leanh::lean_ctor_set(v___x_1559_, 0, v_val_1569_);
                            v___x_1589_ = v___x_1559_;
                            state = 10;
                            continue;
                        } else {
                            v_reuseFailAlloc_1596_ =
                                leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            leanh::lean_ctor_set(v_reuseFailAlloc_1596_, 0, v_val_1569_);
                            leanh::lean_ctor_set(v_reuseFailAlloc_1596_, 1, v___x_1587_);
                            v___x_1589_ = v_reuseFailAlloc_1596_;
                            state = 10;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_dec(v_a_1565_);
                    leanh::lean_del_object(v___x_1559_);
                    leanh::lean_dec(v_snd_1557_);
                    leanh::lean_dec(v_fst_1556_);
                    leanh::lean_del_object(v___x_1554_);
                    v___x_1597_ = leanh::lean_box(0);
                    if v_isShared_1568_ == 0 {
                        leanh::lean_ctor_set(v___x_1567_, 0, v___x_1597_);
                        v___x_1599_ = v___x_1567_;
                        state = 13;
                        continue;
                    } else {
                        v_reuseFailAlloc_1600_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1600_, 0, v___x_1597_);
                        v___x_1599_ = v_reuseFailAlloc_1600_;
                        state = 13;
                        continue;
                    }
                }
            }
            7 => {
                if v_isShared_1555_ == 0 {
                    leanh::lean_ctor_set(v___x_1554_, 0, v___x_1578_);
                    v___x_1580_ = v___x_1554_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_1584_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1584_, 0, v___x_1578_);
                    v___x_1580_ = v_reuseFailAlloc_1584_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                if v_isShared_1568_ == 0 {
                    leanh::lean_ctor_set(v___x_1567_, 0, v___x_1580_);
                    v___x_1582_ = v___x_1567_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_1583_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1583_, 0, v___x_1580_);
                    v___x_1582_ = v_reuseFailAlloc_1583_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_1582_;
            }
            10 => {
                if v_isShared_1555_ == 0 {
                    leanh::lean_ctor_set(v___x_1554_, 0, v___x_1589_);
                    v___x_1591_ = v___x_1554_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_1595_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1595_, 0, v___x_1589_);
                    v___x_1591_ = v_reuseFailAlloc_1595_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                if v_isShared_1568_ == 0 {
                    leanh::lean_ctor_set(v___x_1567_, 0, v___x_1591_);
                    v___x_1593_ = v___x_1567_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_1594_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1594_, 0, v___x_1591_);
                    v___x_1593_ = v_reuseFailAlloc_1594_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                return v___x_1593_;
            }
            13 => {
                return v___x_1599_;
            }
            14 => {
                if v_isShared_1605_ == 0 {
                    v___x_1607_ = v___x_1604_;
                    state = 15;
                    continue;
                } else {
                    v_reuseFailAlloc_1608_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1608_, 0, v_a_1602_);
                    v___x_1607_ = v_reuseFailAlloc_1608_;
                    state = 15;
                    continue;
                }
            }
            15 => {
                return v___x_1607_;
            }
            16 => {
                return v___x_1612_;
            }
            17 => {
                if v_isShared_1627_ == 0 {
                    v___x_1629_ = v___x_1626_;
                    state = 18;
                    continue;
                } else {
                    v_reuseFailAlloc_1630_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1630_, 0, v_a_1624_);
                    v___x_1629_ = v_reuseFailAlloc_1630_;
                    state = 18;
                    continue;
                }
            }
            18 => {
                return v___x_1629_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_constructorApp_x27_x3f___boxed(
    mut v_e_1632_: *mut leanh::LeanObject,
    mut v_a_1633_: *mut leanh::LeanObject,
    mut v_a_1634_: *mut leanh::LeanObject,
    mut v_a_1635_: *mut leanh::LeanObject,
    mut v_a_1636_: *mut leanh::LeanObject,
    mut v_a_1637_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1638_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1638_ =
        l_Lean_Meta_constructorApp_x27_x3f(v_e_1632_, v_a_1633_, v_a_1634_, v_a_1635_, v_a_1636_);
    leanh::lean_dec(v_a_1636_);
    leanh::lean_dec_ref(v_a_1635_);
    leanh::lean_dec(v_a_1634_);
    leanh::lean_dec_ref(v_a_1633_);
    return v_res_1638_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Meta_CtorRecognizer(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Meta_LitValues(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Offset(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Meta_CtorRecognizer(
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
pub unsafe fn initialize_Lean_Meta_CtorRecognizer(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Meta_LitValues(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Lean_Meta_Offset(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_CtorRecognizer(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Meta_CtorRecognizer(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return initialize_Lean_Meta_CtorRecognizer(builtin);
}