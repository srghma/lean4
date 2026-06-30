// Lean compiler output
// Module: Lean.PrettyPrinter.Basic
// Imports: Lean.KeyedDeclsAttribute
use crate::ffi::{
    lean_array_get, lean_has_compile_error, lean_mk_empty_array_with_capacity, lean_st_ref_get,
};
use crate::r#gen::Init::Prelude::l_Lean_replaceRef;
use crate::r#gen::Lean::Data::Name::l_Lean_Name_isAnonymous;
use crate::r#gen::Lean::Data::Options::l_Lean_Options_empty;
use crate::r#gen::Lean::Data::PersistentHashMap::l_Lean_PersistentHashMap_mkEmptyEntriesArray;
use crate::r#gen::Lean::Declaration::l_Lean_ConstantInfo_type;
use crate::r#gen::Lean::Elab::Exception::l_Lean_Elab_abortCommandExceptionId;
use crate::r#gen::Lean::Environment::{
    l_Lean_Environment_contains, l_Lean_Environment_evalConst___redArg,
    l_Lean_Environment_find_x3f, l_Lean_Environment_getModuleIdxFor_x3f, l_Lean_Environment_header,
    l_Lean_Environment_setExporting, l_Lean_EnvironmentHeader_moduleNames,
};
use crate::r#gen::Lean::Exception::l_Lean_unknownIdentifierMessageTag;
use crate::r#gen::Lean::Expr::l_Lean_Expr_isConstOf;
use crate::r#gen::Lean::InternalExceptionId::l_Lean_registerInternalExceptionId;
use crate::r#gen::Lean::KeyedDeclsAttribute::{
    initialize_Lean_KeyedDeclsAttribute, l_Lean_KeyedDeclsAttribute_getValues___redArg,
    runtime_initialize_Lean_KeyedDeclsAttribute,
};
use crate::r#gen::Lean::Message::{
    l_Lean_MessageData_note, l_Lean_MessageData_ofConstName, l_Lean_MessageData_ofName,
    l_Lean_stringToMessageData,
};
use crate::r#gen::Lean::PrivateName::l_Lean_isPrivateName;
pub static l___private_Lean_PrettyPrinter_Basic_0__Lean_PrettyPrinter_initFn___closed__0_00___x40_Lean_PrettyPrinter_Basic_613194564____hygCtx___hyg_2__value: leanh::LeanStringObject<19> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 19, m_capacity: 19, m_length: 18, m_data: [98, 97, 99, 107, 116, 114, 97, 99, 107, 70, 111, 114, 109, 97, 116, 116, 101, 114, 0]};
static mut l___private_Lean_PrettyPrinter_Basic_0__Lean_PrettyPrinter_initFn___closed__0_00___x40_Lean_PrettyPrinter_Basic_613194564____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Basic_0__Lean_PrettyPrinter_initFn___closed__0_00___x40_Lean_PrettyPrinter_Basic_613194564____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_PrettyPrinter_Basic_0__Lean_PrettyPrinter_initFn___closed__1_00___x40_Lean_PrettyPrinter_Basic_613194564____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Basic_0__Lean_PrettyPrinter_initFn___closed__0_00___x40_Lean_PrettyPrinter_Basic_613194564____hygCtx___hyg_2__value) as *mut leanh::LeanObject,7158075812765595634 as *mut leanh::LeanObject] };
static mut l___private_Lean_PrettyPrinter_Basic_0__Lean_PrettyPrinter_initFn___closed__1_00___x40_Lean_PrettyPrinter_Basic_613194564____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_PrettyPrinter_Basic_0__Lean_PrettyPrinter_initFn___closed__1_00___x40_Lean_PrettyPrinter_Basic_613194564____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static mut l_Lean_PrettyPrinter_backtrackExceptionId: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Elab_throwAbortCommand___at___00Lean_evalConst___at___00Lean_PrettyPrinter_runForNodeKind_spec__2_spec__5___redArg___closed__0_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Elab_throwAbortCommand___at___00Lean_evalConst___at___00Lean_PrettyPrinter_runForNodeKind_spec__2_spec__5___redArg___closed__0: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_PrettyPrinter_runForNodeKind_spec__1_spec__2___closed__0_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_PrettyPrinter_runForNodeKind_spec__1_spec__2___closed__0: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_PrettyPrinter_runForNodeKind_spec__1_spec__2___closed__1_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_PrettyPrinter_runForNodeKind_spec__1_spec__2___closed__1: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_PrettyPrinter_runForNodeKind_spec__1_spec__2___closed__2_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_PrettyPrinter_runForNodeKind_spec__1_spec__2___closed__2: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_PrettyPrinter_runForNodeKind_spec__1_spec__2___closed__3_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_PrettyPrinter_runForNodeKind_spec__1_spec__2___closed__3: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_PrettyPrinter_runForNodeKind_spec__1_spec__2___closed__4_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_PrettyPrinter_runForNodeKind_spec__1_spec__2___closed__4: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_PrettyPrinter_runForNodeKind_spec__1_spec__2___closed__5_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_PrettyPrinter_runForNodeKind_spec__1_spec__2___closed__5: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_runForNodeKind_spec__0_spec__0_spec__1_spec__6_spec__8_spec__9___redArg___closed__0_value: leanh::LeanStringObject<24> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 24, m_capacity: 24, m_length: 23, m_data: [65, 32, 112, 114, 105, 118, 97, 116, 101, 32, 100, 101, 99, 108, 97, 114, 97, 116, 105, 111, 110, 32, 96, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_runForNodeKind_spec__0_spec__0_spec__1_spec__6_spec__8_spec__9___redArg___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_runForNodeKind_spec__0_spec__0_spec__1_spec__6_spec__8_spec__9___redArg___closed__0_value) as *mut leanh::LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_runForNodeKind_spec__0_spec__0_spec__1_spec__6_spec__8_spec__9___redArg___closed__1_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_runForNodeKind_spec__0_spec__0_spec__1_spec__6_spec__8_spec__9___redArg___closed__1: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_runForNodeKind_spec__0_spec__0_spec__1_spec__6_spec__8_spec__9___redArg___closed__2_value: leanh::LeanStringObject<79> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 79, m_capacity: 79, m_length: 78, m_data: [96, 32, 40, 102, 114, 111, 109, 32, 116, 104, 101, 32, 99, 117, 114, 114, 101, 110, 116, 32, 109, 111, 100, 117, 108, 101, 41, 32, 101, 120, 105, 115, 116, 115, 32, 98, 117, 116, 32, 119, 111, 117, 108, 100, 32, 110, 101, 101, 100, 32, 116, 111, 32, 98, 101, 32, 112, 117, 98, 108, 105, 99, 32, 116, 111, 32, 97, 99, 99, 101, 115, 115, 32, 104, 101, 114, 101, 46, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_runForNodeKind_spec__0_spec__0_spec__1_spec__6_spec__8_spec__9___redArg___closed__2: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_runForNodeKind_spec__0_spec__0_spec__1_spec__6_spec__8_spec__9___redArg___closed__2_value) as *mut leanh::LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_runForNodeKind_spec__0_spec__0_spec__1_spec__6_spec__8_spec__9___redArg___closed__3_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_runForNodeKind_spec__0_spec__0_spec__1_spec__6_spec__8_spec__9___redArg___closed__3: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_runForNodeKind_spec__0_spec__0_spec__1_spec__6_spec__8_spec__9___redArg___closed__4_value: leanh::LeanStringObject<23> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 23, m_capacity: 23, m_length: 22, m_data: [65, 32, 112, 117, 98, 108, 105, 99, 32, 100, 101, 99, 108, 97, 114, 97, 116, 105, 111, 110, 32, 96, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_runForNodeKind_spec__0_spec__0_spec__1_spec__6_spec__8_spec__9___redArg___closed__4: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_runForNodeKind_spec__0_spec__0_spec__1_spec__6_spec__8_spec__9___redArg___closed__4_value) as *mut leanh::LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_runForNodeKind_spec__0_spec__0_spec__1_spec__6_spec__8_spec__9___redArg___closed__5_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_runForNodeKind_spec__0_spec__0_spec__1_spec__6_spec__8_spec__9___redArg___closed__5: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_runForNodeKind_spec__0_spec__0_spec__1_spec__6_spec__8_spec__9___redArg___closed__6_value: leanh::LeanStringObject<68> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 68, m_capacity: 68, m_length: 67, m_data: [96, 32, 101, 120, 105, 115, 116, 115, 32, 98, 117, 116, 32, 105, 115, 32, 105, 109, 112, 111, 114, 116, 101, 100, 32, 112, 114, 105, 118, 97, 116, 101, 108, 121, 59, 32, 99, 111, 110, 115, 105, 100, 101, 114, 32, 97, 100, 100, 105, 110, 103, 32, 96, 112, 117, 98, 108, 105, 99, 32, 105, 109, 112, 111, 114, 116, 32, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_runForNodeKind_spec__0_spec__0_spec__1_spec__6_spec__8_spec__9___redArg___closed__6: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_runForNodeKind_spec__0_spec__0_spec__1_spec__6_spec__8_spec__9___redArg___closed__6_value) as *mut leanh::LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_runForNodeKind_spec__0_spec__0_spec__1_spec__6_spec__8_spec__9___redArg___closed__7_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_runForNodeKind_spec__0_spec__0_spec__1_spec__6_spec__8_spec__9___redArg___closed__7: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_runForNodeKind_spec__0_spec__0_spec__1_spec__6_spec__8_spec__9___redArg___closed__8_value: leanh::LeanStringObject<3> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [96, 46, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_runForNodeKind_spec__0_spec__0_spec__1_spec__6_spec__8_spec__9___redArg___closed__8: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_runForNodeKind_spec__0_spec__0_spec__1_spec__6_spec__8_spec__9___redArg___closed__8_value) as *mut leanh::LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_runForNodeKind_spec__0_spec__0_spec__1_spec__6_spec__8_spec__9___redArg___closed__9_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_runForNodeKind_spec__0_spec__0_spec__1_spec__6_spec__8_spec__9___redArg___closed__9: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_runForNodeKind_spec__0_spec__0_spec__1_spec__6_spec__8_spec__9___redArg___closed__10_value: leanh::LeanStringObject<10> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [96, 32, 40, 102, 114, 111, 109, 32, 96, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_runForNodeKind_spec__0_spec__0_spec__1_spec__6_spec__8_spec__9___redArg___closed__10: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_runForNodeKind_spec__0_spec__0_spec__1_spec__6_spec__8_spec__9___redArg___closed__10_value) as *mut leanh::LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_runForNodeKind_spec__0_spec__0_spec__1_spec__6_spec__8_spec__9___redArg___closed__11_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_runForNodeKind_spec__0_spec__0_spec__1_spec__6_spec__8_spec__9___redArg___closed__11: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_runForNodeKind_spec__0_spec__0_spec__1_spec__6_spec__8_spec__9___redArg___closed__12_value: leanh::LeanStringObject<54> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 54, m_capacity: 54, m_length: 53, m_data: [96, 41, 32, 101, 120, 105, 115, 116, 115, 32, 98, 117, 116, 32, 119, 111, 117, 108, 100, 32, 110, 101, 101, 100, 32, 116, 111, 32, 98, 101, 32, 112, 117, 98, 108, 105, 99, 32, 116, 111, 32, 97, 99, 99, 101, 115, 115, 32, 104, 101, 114, 101, 46, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_runForNodeKind_spec__0_spec__0_spec__1_spec__6_spec__8_spec__9___redArg___closed__12: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_runForNodeKind_spec__0_spec__0_spec__1_spec__6_spec__8_spec__9___redArg___closed__12_value) as *mut leanh::LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_runForNodeKind_spec__0_spec__0_spec__1_spec__6_spec__8_spec__9___redArg___closed__13_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_runForNodeKind_spec__0_spec__0_spec__1_spec__6_spec__8_spec__9___redArg___closed__13: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_runForNodeKind_spec__0_spec__0_spec__1___redArg___closed__0_value: leanh::LeanStringObject<19> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 19, m_capacity: 19, m_length: 18, m_data: [85, 110, 107, 110, 111, 119, 110, 32, 99, 111, 110, 115, 116, 97, 110, 116, 32, 96, 0]};
static mut l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_runForNodeKind_spec__0_spec__0_spec__1___redArg___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_runForNodeKind_spec__0_spec__0_spec__1___redArg___closed__0_value) as *mut leanh::LeanObject;
static mut l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_runForNodeKind_spec__0_spec__0_spec__1___redArg___closed__1_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_runForNodeKind_spec__0_spec__0_spec__1___redArg___closed__1: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_runForNodeKind_spec__0_spec__0_spec__1___redArg___closed__2_value: leanh::LeanStringObject<2> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [96, 0]};
static mut l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_runForNodeKind_spec__0_spec__0_spec__1___redArg___closed__2: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_runForNodeKind_spec__0_spec__0_spec__1___redArg___closed__2_value) as *mut leanh::LeanObject;
static mut l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_runForNodeKind_spec__0_spec__0_spec__1___redArg___closed__3_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_runForNodeKind_spec__0_spec__0_spec__1___redArg___closed__3: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_PrettyPrinter_runForNodeKind___redArg___closed__0_value:
    leanh::LeanStringObject<30> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 30,
    m_capacity: 30,
    m_length: 29,
    m_data: [
        110, 111, 32, 100, 101, 99, 108, 97, 114, 97, 116, 105, 111, 110, 32, 111, 102, 32, 97,
        116, 116, 114, 105, 98, 117, 116, 101, 32, 91, 0,
    ],
};
static mut l_Lean_PrettyPrinter_runForNodeKind___redArg___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_PrettyPrinter_runForNodeKind___redArg___closed__0_value)
        as *mut leanh::LeanObject;
static mut l_Lean_PrettyPrinter_runForNodeKind___redArg___closed__1_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_PrettyPrinter_runForNodeKind___redArg___closed__1: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_PrettyPrinter_runForNodeKind___redArg___closed__2_value:
    leanh::LeanStringObject<14> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 14,
    m_capacity: 14,
    m_length: 13,
    m_data: [
        93, 32, 102, 111, 117, 110, 100, 32, 102, 111, 114, 32, 96, 0,
    ],
};
static mut l_Lean_PrettyPrinter_runForNodeKind___redArg___closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_PrettyPrinter_runForNodeKind___redArg___closed__2_value)
        as *mut leanh::LeanObject;
static mut l_Lean_PrettyPrinter_runForNodeKind___redArg___closed__3_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_PrettyPrinter_runForNodeKind___redArg___closed__3: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_PrettyPrinter_runForNodeKind___redArg___closed__4_value:
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
    m_data: [76, 101, 97, 110, 0],
};
static mut l_Lean_PrettyPrinter_runForNodeKind___redArg___closed__4: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_PrettyPrinter_runForNodeKind___redArg___closed__4_value)
        as *mut leanh::LeanObject;
pub static l_Lean_PrettyPrinter_runForNodeKind___redArg___closed__5_value:
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
    m_data: [80, 97, 114, 115, 101, 114, 68, 101, 115, 99, 114, 0],
};
static mut l_Lean_PrettyPrinter_runForNodeKind___redArg___closed__5: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_PrettyPrinter_runForNodeKind___redArg___closed__5_value)
        as *mut leanh::LeanObject;
static l_Lean_PrettyPrinter_runForNodeKind___redArg___closed__6_value_aux_0:
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
        core::ptr::addr_of!(l_Lean_PrettyPrinter_runForNodeKind___redArg___closed__4_value)
            as *mut leanh::LeanObject,
        11948124481539785030 as *mut leanh::LeanObject,
    ],
};
pub static l_Lean_PrettyPrinter_runForNodeKind___redArg___closed__6_value:
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
        core::ptr::addr_of!(l_Lean_PrettyPrinter_runForNodeKind___redArg___closed__6_value_aux_0)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_PrettyPrinter_runForNodeKind___redArg___closed__5_value)
            as *mut leanh::LeanObject,
        8878632049041653596 as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_PrettyPrinter_runForNodeKind___redArg___closed__6: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_PrettyPrinter_runForNodeKind___redArg___closed__6_value)
        as *mut leanh::LeanObject;
pub static l_Lean_PrettyPrinter_runForNodeKind___redArg___closed__7_value:
    leanh::LeanStringObject<20> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 20,
    m_capacity: 20,
    m_length: 19,
    m_data: [
        84, 114, 97, 105, 108, 105, 110, 103, 80, 97, 114, 115, 101, 114, 68, 101, 115, 99, 114, 0,
    ],
};
static mut l_Lean_PrettyPrinter_runForNodeKind___redArg___closed__7: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_PrettyPrinter_runForNodeKind___redArg___closed__7_value)
        as *mut leanh::LeanObject;
static l_Lean_PrettyPrinter_runForNodeKind___redArg___closed__8_value_aux_0:
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
        core::ptr::addr_of!(l_Lean_PrettyPrinter_runForNodeKind___redArg___closed__4_value)
            as *mut leanh::LeanObject,
        11948124481539785030 as *mut leanh::LeanObject,
    ],
};
pub static l_Lean_PrettyPrinter_runForNodeKind___redArg___closed__8_value:
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
        core::ptr::addr_of!(l_Lean_PrettyPrinter_runForNodeKind___redArg___closed__8_value_aux_0)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_PrettyPrinter_runForNodeKind___redArg___closed__7_value)
            as *mut leanh::LeanObject,
        18049428212802854473 as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_PrettyPrinter_runForNodeKind___redArg___closed__8: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_PrettyPrinter_runForNodeKind___redArg___closed__8_value)
        as *mut leanh::LeanObject;
pub unsafe fn l___private_Lean_PrettyPrinter_Basic_0__Lean_PrettyPrinter_initFn_00___x40_Lean_PrettyPrinter_Basic_613194564____hygCtx___hyg_2_()
-> *mut leanh::LeanObject {
    let mut v___x_551_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_552_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_551_ = l___private_Lean_PrettyPrinter_Basic_0__Lean_PrettyPrinter_initFn___closed__1_00___x40_Lean_PrettyPrinter_Basic_613194564____hygCtx___hyg_2_;
    v___x_552_ = l_Lean_registerInternalExceptionId(v___x_551_);
    return v___x_552_;
}
pub unsafe fn l___private_Lean_PrettyPrinter_Basic_0__Lean_PrettyPrinter_initFn_00___x40_Lean_PrettyPrinter_Basic_613194564____hygCtx___hyg_2____boxed(
    mut v_a_553_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_554_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_554_ = l___private_Lean_PrettyPrinter_Basic_0__Lean_PrettyPrinter_initFn_00___x40_Lean_PrettyPrinter_Basic_613194564____hygCtx___hyg_2_();
    return v_res_554_;
}
pub unsafe fn _init_l_Lean_Elab_throwAbortCommand___at___00Lean_evalConst___at___00Lean_PrettyPrinter_runForNodeKind_spec__2_spec__5___redArg___closed__0()
-> *mut leanh::LeanObject {
    let mut v___x_555_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_556_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_557_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_555_ = leanh::lean_box(0);
    v___x_556_ = l_Lean_Elab_abortCommandExceptionId;
    v___x_557_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_557_, 0, v___x_556_);
    leanh::lean_ctor_set(v___x_557_, 1, v___x_555_);
    return v___x_557_;
}
pub unsafe fn l_Lean_Elab_throwAbortCommand___at___00Lean_evalConst___at___00Lean_PrettyPrinter_runForNodeKind_spec__2_spec__5___redArg()
-> *mut leanh::LeanObject {
    let mut v___x_559_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_560_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_559_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_throwAbortCommand___at___00Lean_evalConst___at___00Lean_PrettyPrinter_runForNodeKind_spec__2_spec__5___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_Elab_throwAbortCommand___at___00Lean_evalConst___at___00Lean_PrettyPrinter_runForNodeKind_spec__2_spec__5___redArg___closed__0_once), _init_l_Lean_Elab_throwAbortCommand___at___00Lean_evalConst___at___00Lean_PrettyPrinter_runForNodeKind_spec__2_spec__5___redArg___closed__0);
    v___x_560_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_560_, 0, v___x_559_);
    return v___x_560_;
}
pub unsafe fn l_Lean_Elab_throwAbortCommand___at___00Lean_evalConst___at___00Lean_PrettyPrinter_runForNodeKind_spec__2_spec__5___redArg___boxed(
    mut v___y_561_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_562_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_562_ = l_Lean_Elab_throwAbortCommand___at___00Lean_evalConst___at___00Lean_PrettyPrinter_runForNodeKind_spec__2_spec__5___redArg();
    return v_res_562_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_PrettyPrinter_runForNodeKind_spec__1_spec__2___closed__0()
-> *mut leanh::LeanObject {
    let mut v___x_563_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_563_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(
        leanh::lean_box(0),
        leanh::lean_box(0),
    );
    return v___x_563_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_PrettyPrinter_runForNodeKind_spec__1_spec__2___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_564_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_565_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_564_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_PrettyPrinter_runForNodeKind_spec__1_spec__2___closed__0), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_PrettyPrinter_runForNodeKind_spec__1_spec__2___closed__0_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_PrettyPrinter_runForNodeKind_spec__1_spec__2___closed__0);
    v___x_565_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_565_, 0, v___x_564_);
    return v___x_565_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_PrettyPrinter_runForNodeKind_spec__1_spec__2___closed__2()
-> *mut leanh::LeanObject {
    let mut v___x_566_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_567_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_568_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_566_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_PrettyPrinter_runForNodeKind_spec__1_spec__2___closed__1), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_PrettyPrinter_runForNodeKind_spec__1_spec__2___closed__1_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_PrettyPrinter_runForNodeKind_spec__1_spec__2___closed__1);
    v___x_567_ = leanh::lean_unsigned_to_nat(0);
    v___x_568_ = leanh::lean_alloc_ctor(0, 10, (0) as u32);
    leanh::lean_ctor_set(v___x_568_, 0, v___x_567_);
    leanh::lean_ctor_set(v___x_568_, 1, v___x_567_);
    leanh::lean_ctor_set(v___x_568_, 2, v___x_567_);
    leanh::lean_ctor_set(v___x_568_, 3, v___x_567_);
    leanh::lean_ctor_set(v___x_568_, 4, v___x_566_);
    leanh::lean_ctor_set(v___x_568_, 5, v___x_566_);
    leanh::lean_ctor_set(v___x_568_, 6, v___x_566_);
    leanh::lean_ctor_set(v___x_568_, 7, v___x_566_);
    leanh::lean_ctor_set(v___x_568_, 8, v___x_566_);
    leanh::lean_ctor_set(v___x_568_, 9, v___x_566_);
    return v___x_568_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_PrettyPrinter_runForNodeKind_spec__1_spec__2___closed__3()
-> *mut leanh::LeanObject {
    let mut v___x_569_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_570_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_571_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_569_ = leanh::lean_unsigned_to_nat(32);
    v___x_570_ = lean_mk_empty_array_with_capacity(v___x_569_);
    v___x_571_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_571_, 0, v___x_570_);
    return v___x_571_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_PrettyPrinter_runForNodeKind_spec__1_spec__2___closed__4()
-> *mut leanh::LeanObject {
    let mut v___x_572_: usize = 0;
    let mut v___x_573_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_574_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_575_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_576_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_577_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_572_ = 5usize;
    v___x_573_ = leanh::lean_unsigned_to_nat(0);
    v___x_574_ = leanh::lean_unsigned_to_nat(32);
    v___x_575_ = lean_mk_empty_array_with_capacity(v___x_574_);
    v___x_576_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_PrettyPrinter_runForNodeKind_spec__1_spec__2___closed__3), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_PrettyPrinter_runForNodeKind_spec__1_spec__2___closed__3_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_PrettyPrinter_runForNodeKind_spec__1_spec__2___closed__3);
    v___x_577_ = leanh::lean_alloc_ctor(0, 4, (core::mem::size_of::<usize>() * 1) as u32);
    leanh::lean_ctor_set(v___x_577_, 0, v___x_576_);
    leanh::lean_ctor_set(v___x_577_, 1, v___x_575_);
    leanh::lean_ctor_set(v___x_577_, 2, v___x_573_);
    leanh::lean_ctor_set(v___x_577_, 3, v___x_573_);
    leanh::lean_ctor_set_usize(v___x_577_, 4, v___x_572_);
    return v___x_577_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_PrettyPrinter_runForNodeKind_spec__1_spec__2___closed__5()
-> *mut leanh::LeanObject {
    let mut v___x_578_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_579_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_580_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_581_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_578_ = leanh::lean_box(1);
    v___x_579_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_PrettyPrinter_runForNodeKind_spec__1_spec__2___closed__4), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_PrettyPrinter_runForNodeKind_spec__1_spec__2___closed__4_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_PrettyPrinter_runForNodeKind_spec__1_spec__2___closed__4);
    v___x_580_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_PrettyPrinter_runForNodeKind_spec__1_spec__2___closed__1), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_PrettyPrinter_runForNodeKind_spec__1_spec__2___closed__1_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_PrettyPrinter_runForNodeKind_spec__1_spec__2___closed__1);
    v___x_581_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_581_, 0, v___x_580_);
    leanh::lean_ctor_set(v___x_581_, 1, v___x_579_);
    leanh::lean_ctor_set(v___x_581_, 2, v___x_578_);
    return v___x_581_;
}
pub unsafe fn l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_PrettyPrinter_runForNodeKind_spec__1_spec__2(
    mut v_msgData_582_: *mut leanh::LeanObject,
    mut v___y_583_: *mut leanh::LeanObject,
    mut v___y_584_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_586_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_587_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_588_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_589_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_590_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_591_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_592_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_593_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_586_ = lean_st_ref_get(v___y_584_);
    v_env_587_ = leanh::lean_ctor_get(v___x_586_, 0);
    leanh::lean_inc_ref(v_env_587_);
    leanh::lean_dec(v___x_586_);
    v_options_588_ = leanh::lean_ctor_get(v___y_583_, 2);
    v___x_589_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_PrettyPrinter_runForNodeKind_spec__1_spec__2___closed__2), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_PrettyPrinter_runForNodeKind_spec__1_spec__2___closed__2_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_PrettyPrinter_runForNodeKind_spec__1_spec__2___closed__2);
    v___x_590_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_PrettyPrinter_runForNodeKind_spec__1_spec__2___closed__5), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_PrettyPrinter_runForNodeKind_spec__1_spec__2___closed__5_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_PrettyPrinter_runForNodeKind_spec__1_spec__2___closed__5);
    leanh::lean_inc_ref(v_options_588_);
    v___x_591_ = leanh::lean_alloc_ctor(0, 4, (0) as u32);
    leanh::lean_ctor_set(v___x_591_, 0, v_env_587_);
    leanh::lean_ctor_set(v___x_591_, 1, v___x_589_);
    leanh::lean_ctor_set(v___x_591_, 2, v___x_590_);
    leanh::lean_ctor_set(v___x_591_, 3, v_options_588_);
    v___x_592_ = leanh::lean_alloc_ctor(3, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_592_, 0, v___x_591_);
    leanh::lean_ctor_set(v___x_592_, 1, v_msgData_582_);
    v___x_593_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_593_, 0, v___x_592_);
    return v___x_593_;
}
pub unsafe fn l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_PrettyPrinter_runForNodeKind_spec__1_spec__2___boxed(
    mut v_msgData_594_: *mut leanh::LeanObject,
    mut v___y_595_: *mut leanh::LeanObject,
    mut v___y_596_: *mut leanh::LeanObject,
    mut v___y_597_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_598_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_598_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_PrettyPrinter_runForNodeKind_spec__1_spec__2(v_msgData_594_, v___y_595_, v___y_596_);
    leanh::lean_dec(v___y_596_);
    leanh::lean_dec_ref(v___y_595_);
    return v_res_598_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_PrettyPrinter_runForNodeKind_spec__1___redArg(
    mut v_msg_599_: *mut leanh::LeanObject,
    mut v___y_600_: *mut leanh::LeanObject,
    mut v___y_601_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_ref_603_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_604_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_605_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_607_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_608_: u8 = 0;
    let mut v___x_609_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_611_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_612_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_613_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ref_603_ = leanh::lean_ctor_get(v___y_600_, 5);
                v___x_604_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_PrettyPrinter_runForNodeKind_spec__1_spec__2(v_msg_599_, v___y_600_, v___y_601_);
                v_a_605_ = leanh::lean_ctor_get(v___x_604_, 0);
                v_isSharedCheck_613_ = (!leanh::lean_is_exclusive(v___x_604_)) as u8;
                if v_isSharedCheck_613_ == 0 {
                    v___x_607_ = v___x_604_;
                    v_isShared_608_ = v_isSharedCheck_613_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_a_605_);
                    leanh::lean_dec(v___x_604_);
                    v___x_607_ = leanh::lean_box(0);
                    v_isShared_608_ = v_isSharedCheck_613_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                leanh::lean_inc(v_ref_603_);
                v___x_609_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_609_, 0, v_ref_603_);
                leanh::lean_ctor_set(v___x_609_, 1, v_a_605_);
                if v_isShared_608_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_607_, 1);
                    leanh::lean_ctor_set(v___x_607_, 0, v___x_609_);
                    v___x_611_ = v___x_607_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_612_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_612_, 0, v___x_609_);
                    v___x_611_ = v_reuseFailAlloc_612_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_611_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_throwError___at___00Lean_PrettyPrinter_runForNodeKind_spec__1___redArg___boxed(
    mut v_msg_614_: *mut leanh::LeanObject,
    mut v___y_615_: *mut leanh::LeanObject,
    mut v___y_616_: *mut leanh::LeanObject,
    mut v___y_617_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_618_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_618_ = l_Lean_throwError___at___00Lean_PrettyPrinter_runForNodeKind_spec__1___redArg(
        v_msg_614_, v___y_615_, v___y_616_,
    );
    leanh::lean_dec(v___y_616_);
    leanh::lean_dec_ref(v___y_615_);
    return v_res_618_;
}
pub unsafe fn l_Lean_ofExcept___at___00Lean_evalConst___at___00Lean_PrettyPrinter_runForNodeKind_spec__2_spec__4___redArg(
    mut v_x_619_: *mut leanh::LeanObject,
    mut v___y_620_: *mut leanh::LeanObject,
    mut v___y_621_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_a_623_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_624_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_625_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_626_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_628_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_629_: u8 = 0;
    let mut v___x_631_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_632_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_633_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_619_) == 0 {
                    v_a_623_ = leanh::lean_ctor_get(v_x_619_, 0);
                    leanh::lean_inc(v_a_623_);
                    leanh::lean_dec_ref_known(v_x_619_, 1);
                    v___x_624_ = l_Lean_stringToMessageData(v_a_623_);
                    v___x_625_ = l_Lean_throwError___at___00Lean_PrettyPrinter_runForNodeKind_spec__1___redArg(v___x_624_, v___y_620_, v___y_621_);
                    return v___x_625_;
                } else {
                    v_a_626_ = leanh::lean_ctor_get(v_x_619_, 0);
                    v_isSharedCheck_633_ = (!leanh::lean_is_exclusive(v_x_619_)) as u8;
                    if v_isSharedCheck_633_ == 0 {
                        v___x_628_ = v_x_619_;
                        v_isShared_629_ = v_isSharedCheck_633_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_626_);
                        leanh::lean_dec(v_x_619_);
                        v___x_628_ = leanh::lean_box(0);
                        v_isShared_629_ = v_isSharedCheck_633_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_629_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_628_, 0);
                    v___x_631_ = v___x_628_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_632_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_632_, 0, v_a_626_);
                    v___x_631_ = v_reuseFailAlloc_632_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_631_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_ofExcept___at___00Lean_evalConst___at___00Lean_PrettyPrinter_runForNodeKind_spec__2_spec__4___redArg___boxed(
    mut v_x_634_: *mut leanh::LeanObject,
    mut v___y_635_: *mut leanh::LeanObject,
    mut v___y_636_: *mut leanh::LeanObject,
    mut v___y_637_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_638_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_638_ = l_Lean_ofExcept___at___00Lean_evalConst___at___00Lean_PrettyPrinter_runForNodeKind_spec__2_spec__4___redArg(v_x_634_, v___y_635_, v___y_636_);
    leanh::lean_dec(v___y_636_);
    leanh::lean_dec_ref(v___y_635_);
    return v_res_638_;
}
pub unsafe fn l_Lean_evalConst___at___00Lean_PrettyPrinter_runForNodeKind_spec__2___redArg(
    mut v_constName_639_: *mut leanh::LeanObject,
    mut v_checkMeta_640_: u8,
    mut v___y_641_: *mut leanh::LeanObject,
    mut v___y_642_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_644_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_645_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_646_: u8 = 0;
    let mut v___x_647_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_648_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_649_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_650_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_651_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_652_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_653_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_654_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_655_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_656_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_657_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_658_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_660_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_661_: u8 = 0;
    let mut v___x_663_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_664_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_665_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_644_ = lean_st_ref_get(v___y_642_);
                v_env_645_ = leanh::lean_ctor_get(v___x_644_, 0);
                leanh::lean_inc_ref(v_env_645_);
                leanh::lean_dec(v___x_644_);
                leanh::lean_inc(v_constName_639_);
                v___x_646_ = lean_has_compile_error(v_env_645_, v_constName_639_);
                if v___x_646_ == 0 {
                    v___x_647_ = lean_st_ref_get(v___y_642_);
                    v_env_648_ = leanh::lean_ctor_get(v___x_647_, 0);
                    leanh::lean_inc_ref(v_env_648_);
                    leanh::lean_dec(v___x_647_);
                    v_options_649_ = leanh::lean_ctor_get(v___y_641_, 2);
                    v___x_650_ = l_Lean_Environment_evalConst___redArg(
                        v_env_648_,
                        v_options_649_,
                        v_constName_639_,
                        v_checkMeta_640_,
                    );
                    leanh::lean_dec(v_constName_639_);
                    leanh::lean_dec_ref(v_env_648_);
                    v___x_651_ = l_Lean_ofExcept___at___00Lean_evalConst___at___00Lean_PrettyPrinter_runForNodeKind_spec__2_spec__4___redArg(v___x_650_, v___y_641_, v___y_642_);
                    return v___x_651_;
                } else {
                    v___x_652_ = l_Lean_Elab_throwAbortCommand___at___00Lean_evalConst___at___00Lean_PrettyPrinter_runForNodeKind_spec__2_spec__5___redArg();
                    if leanh::lean_obj_tag(v___x_652_) == 0 {
                        leanh::lean_dec_ref_known(v___x_652_, 1);
                        v___x_653_ = lean_st_ref_get(v___y_642_);
                        v_env_654_ = leanh::lean_ctor_get(v___x_653_, 0);
                        leanh::lean_inc_ref(v_env_654_);
                        leanh::lean_dec(v___x_653_);
                        v_options_655_ = leanh::lean_ctor_get(v___y_641_, 2);
                        v___x_656_ = l_Lean_Environment_evalConst___redArg(
                            v_env_654_,
                            v_options_655_,
                            v_constName_639_,
                            v_checkMeta_640_,
                        );
                        leanh::lean_dec(v_constName_639_);
                        leanh::lean_dec_ref(v_env_654_);
                        v___x_657_ = l_Lean_ofExcept___at___00Lean_evalConst___at___00Lean_PrettyPrinter_runForNodeKind_spec__2_spec__4___redArg(v___x_656_, v___y_641_, v___y_642_);
                        return v___x_657_;
                    } else {
                        leanh::lean_dec(v_constName_639_);
                        v_a_658_ = leanh::lean_ctor_get(v___x_652_, 0);
                        v_isSharedCheck_665_ = (!leanh::lean_is_exclusive(v___x_652_)) as u8;
                        if v_isSharedCheck_665_ == 0 {
                            v___x_660_ = v___x_652_;
                            v_isShared_661_ = v_isSharedCheck_665_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_658_);
                            leanh::lean_dec(v___x_652_);
                            v___x_660_ = leanh::lean_box(0);
                            v_isShared_661_ = v_isSharedCheck_665_;
                            state = 1;
                            continue;
                        }
                    }
                }
            }
            1 => {
                if v_isShared_661_ == 0 {
                    v___x_663_ = v___x_660_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_664_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_664_, 0, v_a_658_);
                    v___x_663_ = v_reuseFailAlloc_664_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_663_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_evalConst___at___00Lean_PrettyPrinter_runForNodeKind_spec__2___redArg___boxed(
    mut v_constName_666_: *mut leanh::LeanObject,
    mut v_checkMeta_667_: *mut leanh::LeanObject,
    mut v___y_668_: *mut leanh::LeanObject,
    mut v___y_669_: *mut leanh::LeanObject,
    mut v___y_670_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_checkMeta_boxed_671_: u8 = 0;
    let mut v_res_672_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_checkMeta_boxed_671_ = (leanh::lean_unbox(v_checkMeta_667_) as u8);
    v_res_672_ = l_Lean_evalConst___at___00Lean_PrettyPrinter_runForNodeKind_spec__2___redArg(
        v_constName_666_,
        v_checkMeta_boxed_671_,
        v___y_668_,
        v___y_669_,
    );
    leanh::lean_dec(v___y_669_);
    leanh::lean_dec_ref(v___y_668_);
    return v_res_672_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_runForNodeKind_spec__0_spec__0_spec__1_spec__6_spec__9___redArg(
    mut v_ref_673_: *mut leanh::LeanObject,
    mut v_msg_674_: *mut leanh::LeanObject,
    mut v___y_675_: *mut leanh::LeanObject,
    mut v___y_676_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_fileName_678_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fileMap_679_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_680_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_currRecDepth_681_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_maxRecDepth_682_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_683_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_currNamespace_684_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_openDecls_685_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_initHeartbeats_686_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_maxHeartbeats_687_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_quotContext_688_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_currMacroScope_689_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_diag_690_: u8 = 0;
    let mut v_cancelTk_x3f_691_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_suppressElabErrors_692_: u8 = 0;
    let mut v_inheritedTraceOptions_693_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_694_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_695_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_696_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_fileName_678_ = leanh::lean_ctor_get(v___y_675_, 0);
    v_fileMap_679_ = leanh::lean_ctor_get(v___y_675_, 1);
    v_options_680_ = leanh::lean_ctor_get(v___y_675_, 2);
    v_currRecDepth_681_ = leanh::lean_ctor_get(v___y_675_, 3);
    v_maxRecDepth_682_ = leanh::lean_ctor_get(v___y_675_, 4);
    v_ref_683_ = leanh::lean_ctor_get(v___y_675_, 5);
    v_currNamespace_684_ = leanh::lean_ctor_get(v___y_675_, 6);
    v_openDecls_685_ = leanh::lean_ctor_get(v___y_675_, 7);
    v_initHeartbeats_686_ = leanh::lean_ctor_get(v___y_675_, 8);
    v_maxHeartbeats_687_ = leanh::lean_ctor_get(v___y_675_, 9);
    v_quotContext_688_ = leanh::lean_ctor_get(v___y_675_, 10);
    v_currMacroScope_689_ = leanh::lean_ctor_get(v___y_675_, 11);
    v_diag_690_ = leanh::lean_ctor_get_uint8(
        v___y_675_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 14) as u32,
    );
    v_cancelTk_x3f_691_ = leanh::lean_ctor_get(v___y_675_, 12);
    v_suppressElabErrors_692_ = leanh::lean_ctor_get_uint8(
        v___y_675_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 14 + 1) as u32,
    );
    v_inheritedTraceOptions_693_ = leanh::lean_ctor_get(v___y_675_, 13);
    v_ref_694_ = l_Lean_replaceRef(v_ref_673_, v_ref_683_);
    leanh::lean_inc_ref(v_inheritedTraceOptions_693_);
    leanh::lean_inc(v_cancelTk_x3f_691_);
    leanh::lean_inc(v_currMacroScope_689_);
    leanh::lean_inc(v_quotContext_688_);
    leanh::lean_inc(v_maxHeartbeats_687_);
    leanh::lean_inc(v_initHeartbeats_686_);
    leanh::lean_inc(v_openDecls_685_);
    leanh::lean_inc(v_currNamespace_684_);
    leanh::lean_inc(v_maxRecDepth_682_);
    leanh::lean_inc(v_currRecDepth_681_);
    leanh::lean_inc_ref(v_options_680_);
    leanh::lean_inc_ref(v_fileMap_679_);
    leanh::lean_inc_ref(v_fileName_678_);
    v___x_695_ = leanh::lean_alloc_ctor(0, 14, (2) as u32);
    leanh::lean_ctor_set(v___x_695_, 0, v_fileName_678_);
    leanh::lean_ctor_set(v___x_695_, 1, v_fileMap_679_);
    leanh::lean_ctor_set(v___x_695_, 2, v_options_680_);
    leanh::lean_ctor_set(v___x_695_, 3, v_currRecDepth_681_);
    leanh::lean_ctor_set(v___x_695_, 4, v_maxRecDepth_682_);
    leanh::lean_ctor_set(v___x_695_, 5, v_ref_694_);
    leanh::lean_ctor_set(v___x_695_, 6, v_currNamespace_684_);
    leanh::lean_ctor_set(v___x_695_, 7, v_openDecls_685_);
    leanh::lean_ctor_set(v___x_695_, 8, v_initHeartbeats_686_);
    leanh::lean_ctor_set(v___x_695_, 9, v_maxHeartbeats_687_);
    leanh::lean_ctor_set(v___x_695_, 10, v_quotContext_688_);
    leanh::lean_ctor_set(v___x_695_, 11, v_currMacroScope_689_);
    leanh::lean_ctor_set(v___x_695_, 12, v_cancelTk_x3f_691_);
    leanh::lean_ctor_set(v___x_695_, 13, v_inheritedTraceOptions_693_);
    leanh::lean_ctor_set_uint8(
        v___x_695_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 14) as u32,
        v_diag_690_,
    );
    leanh::lean_ctor_set_uint8(
        v___x_695_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 14 + 1) as u32,
        v_suppressElabErrors_692_,
    );
    v___x_696_ = l_Lean_throwError___at___00Lean_PrettyPrinter_runForNodeKind_spec__1___redArg(
        v_msg_674_, v___x_695_, v___y_676_,
    );
    leanh::lean_dec_ref_known(v___x_695_, 14);
    return v___x_696_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_runForNodeKind_spec__0_spec__0_spec__1_spec__6_spec__9___redArg___boxed(
    mut v_ref_697_: *mut leanh::LeanObject,
    mut v_msg_698_: *mut leanh::LeanObject,
    mut v___y_699_: *mut leanh::LeanObject,
    mut v___y_700_: *mut leanh::LeanObject,
    mut v___y_701_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_702_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_702_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_runForNodeKind_spec__0_spec__0_spec__1_spec__6_spec__9___redArg(v_ref_697_, v_msg_698_, v___y_699_, v___y_700_);
    leanh::lean_dec(v___y_700_);
    leanh::lean_dec_ref(v___y_699_);
    leanh::lean_dec(v_ref_697_);
    return v_res_702_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_runForNodeKind_spec__0_spec__0_spec__1_spec__6_spec__8_spec__9___redArg___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_704_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_705_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_704_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_runForNodeKind_spec__0_spec__0_spec__1_spec__6_spec__8_spec__9___redArg___closed__0;
    v___x_705_ = l_Lean_stringToMessageData(v___x_704_);
    return v___x_705_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_runForNodeKind_spec__0_spec__0_spec__1_spec__6_spec__8_spec__9___redArg___closed__3()
-> *mut leanh::LeanObject {
    let mut v___x_707_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_708_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_707_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_runForNodeKind_spec__0_spec__0_spec__1_spec__6_spec__8_spec__9___redArg___closed__2;
    v___x_708_ = l_Lean_stringToMessageData(v___x_707_);
    return v___x_708_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_runForNodeKind_spec__0_spec__0_spec__1_spec__6_spec__8_spec__9___redArg___closed__5()
-> *mut leanh::LeanObject {
    let mut v___x_710_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_711_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_710_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_runForNodeKind_spec__0_spec__0_spec__1_spec__6_spec__8_spec__9___redArg___closed__4;
    v___x_711_ = l_Lean_stringToMessageData(v___x_710_);
    return v___x_711_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_runForNodeKind_spec__0_spec__0_spec__1_spec__6_spec__8_spec__9___redArg___closed__7()
-> *mut leanh::LeanObject {
    let mut v___x_713_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_714_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_713_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_runForNodeKind_spec__0_spec__0_spec__1_spec__6_spec__8_spec__9___redArg___closed__6;
    v___x_714_ = l_Lean_stringToMessageData(v___x_713_);
    return v___x_714_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_runForNodeKind_spec__0_spec__0_spec__1_spec__6_spec__8_spec__9___redArg___closed__9()
-> *mut leanh::LeanObject {
    let mut v___x_716_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_717_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_716_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_runForNodeKind_spec__0_spec__0_spec__1_spec__6_spec__8_spec__9___redArg___closed__8;
    v___x_717_ = l_Lean_stringToMessageData(v___x_716_);
    return v___x_717_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_runForNodeKind_spec__0_spec__0_spec__1_spec__6_spec__8_spec__9___redArg___closed__11()
-> *mut leanh::LeanObject {
    let mut v___x_719_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_720_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_719_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_runForNodeKind_spec__0_spec__0_spec__1_spec__6_spec__8_spec__9___redArg___closed__10;
    v___x_720_ = l_Lean_stringToMessageData(v___x_719_);
    return v___x_720_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_runForNodeKind_spec__0_spec__0_spec__1_spec__6_spec__8_spec__9___redArg___closed__13()
-> *mut leanh::LeanObject {
    let mut v___x_722_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_723_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_722_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_runForNodeKind_spec__0_spec__0_spec__1_spec__6_spec__8_spec__9___redArg___closed__12;
    v___x_723_ = l_Lean_stringToMessageData(v___x_722_);
    return v___x_723_;
}
pub unsafe fn l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_runForNodeKind_spec__0_spec__0_spec__1_spec__6_spec__8_spec__9___redArg(
    mut v_msg_724_: *mut leanh::LeanObject,
    mut v_declHint_725_: *mut leanh::LeanObject,
    mut v___y_726_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_728_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_729_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_730_: u8 = 0;
    let mut v_isExporting_731_: u8 = 0;
    let mut v___x_732_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_733_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_734_: u8 = 0;
    let mut v___x_735_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_736_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_737_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_738_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_739_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_740_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_c_741_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_742_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_743_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_744_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_745_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_746_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_747_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_748_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_749_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_750_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_752_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_753_: u8 = 0;
    let mut v___x_754_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_755_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_756_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_mod_757_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_758_: u8 = 0;
    let mut v___x_759_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_760_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_761_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_762_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_763_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_764_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_765_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_766_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_767_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_768_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_770_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_771_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_772_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_773_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_774_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_775_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_776_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_777_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_778_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_779_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_780_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_781_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_783_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_784_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_785_: u8 = 0;
    let mut v___x_786_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_728_ = lean_st_ref_get(v___y_726_);
                v_env_729_ = leanh::lean_ctor_get(v___x_728_, 0);
                leanh::lean_inc_ref(v_env_729_);
                leanh::lean_dec(v___x_728_);
                v___x_730_ = l_Lean_Name_isAnonymous(v_declHint_725_);
                if v___x_730_ == 0 {
                    v_isExporting_731_ = leanh::lean_ctor_get_uint8(
                        v_env_729_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 8) as u32,
                    );
                    if v_isExporting_731_ == 0 {
                        leanh::lean_dec_ref(v_env_729_);
                        leanh::lean_dec(v_declHint_725_);
                        v___x_732_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v___x_732_, 0, v_msg_724_);
                        return v___x_732_;
                    } else {
                        leanh::lean_inc_ref(v_env_729_);
                        v___x_733_ = l_Lean_Environment_setExporting(v_env_729_, v___x_730_);
                        leanh::lean_inc(v_declHint_725_);
                        leanh::lean_inc_ref(v___x_733_);
                        v___x_734_ = l_Lean_Environment_contains(
                            v___x_733_,
                            v_declHint_725_,
                            v_isExporting_731_,
                        );
                        if v___x_734_ == 0 {
                            leanh::lean_dec_ref(v___x_733_);
                            leanh::lean_dec_ref(v_env_729_);
                            leanh::lean_dec(v_declHint_725_);
                            v___x_735_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                            leanh::lean_ctor_set(v___x_735_, 0, v_msg_724_);
                            return v___x_735_;
                        } else {
                            v___x_736_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_PrettyPrinter_runForNodeKind_spec__1_spec__2___closed__2), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_PrettyPrinter_runForNodeKind_spec__1_spec__2___closed__2_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_PrettyPrinter_runForNodeKind_spec__1_spec__2___closed__2);
                            v___x_737_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_PrettyPrinter_runForNodeKind_spec__1_spec__2___closed__5), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_PrettyPrinter_runForNodeKind_spec__1_spec__2___closed__5_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_PrettyPrinter_runForNodeKind_spec__1_spec__2___closed__5);
                            v___x_738_ = l_Lean_Options_empty;
                            v___x_739_ = leanh::lean_alloc_ctor(0, 4, (0) as u32);
                            leanh::lean_ctor_set(v___x_739_, 0, v___x_733_);
                            leanh::lean_ctor_set(v___x_739_, 1, v___x_736_);
                            leanh::lean_ctor_set(v___x_739_, 2, v___x_737_);
                            leanh::lean_ctor_set(v___x_739_, 3, v___x_738_);
                            leanh::lean_inc(v_declHint_725_);
                            v___x_740_ =
                                l_Lean_MessageData_ofConstName(v_declHint_725_, v___x_730_);
                            v_c_741_ = leanh::lean_alloc_ctor(3, 2, (0) as u32);
                            leanh::lean_ctor_set(v_c_741_, 0, v___x_739_);
                            leanh::lean_ctor_set(v_c_741_, 1, v___x_740_);
                            v___x_742_ =
                                l_Lean_Environment_getModuleIdxFor_x3f(v_env_729_, v_declHint_725_);
                            if leanh::lean_obj_tag(v___x_742_) == 0 {
                                leanh::lean_dec_ref(v_env_729_);
                                leanh::lean_dec(v_declHint_725_);
                                v___x_743_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_runForNodeKind_spec__0_spec__0_spec__1_spec__6_spec__8_spec__9___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_runForNodeKind_spec__0_spec__0_spec__1_spec__6_spec__8_spec__9___redArg___closed__1_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_runForNodeKind_spec__0_spec__0_spec__1_spec__6_spec__8_spec__9___redArg___closed__1);
                                v___x_744_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                                leanh::lean_ctor_set(v___x_744_, 0, v___x_743_);
                                leanh::lean_ctor_set(v___x_744_, 1, v_c_741_);
                                v___x_745_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_runForNodeKind_spec__0_spec__0_spec__1_spec__6_spec__8_spec__9___redArg___closed__3), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_runForNodeKind_spec__0_spec__0_spec__1_spec__6_spec__8_spec__9___redArg___closed__3_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_runForNodeKind_spec__0_spec__0_spec__1_spec__6_spec__8_spec__9___redArg___closed__3);
                                v___x_746_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                                leanh::lean_ctor_set(v___x_746_, 0, v___x_744_);
                                leanh::lean_ctor_set(v___x_746_, 1, v___x_745_);
                                v___x_747_ = l_Lean_MessageData_note(v___x_746_);
                                v___x_748_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                                leanh::lean_ctor_set(v___x_748_, 0, v_msg_724_);
                                leanh::lean_ctor_set(v___x_748_, 1, v___x_747_);
                                v___x_749_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                                leanh::lean_ctor_set(v___x_749_, 0, v___x_748_);
                                return v___x_749_;
                            } else {
                                v_val_750_ = leanh::lean_ctor_get(v___x_742_, 0);
                                v_isSharedCheck_785_ =
                                    (!leanh::lean_is_exclusive(v___x_742_)) as u8;
                                if v_isSharedCheck_785_ == 0 {
                                    v___x_752_ = v___x_742_;
                                    v_isShared_753_ = v_isSharedCheck_785_;
                                    state = 1;
                                    continue;
                                } else {
                                    leanh::lean_inc(v_val_750_);
                                    leanh::lean_dec(v___x_742_);
                                    v___x_752_ = leanh::lean_box(0);
                                    v_isShared_753_ = v_isSharedCheck_785_;
                                    state = 1;
                                    continue;
                                }
                            }
                        }
                    }
                } else {
                    leanh::lean_dec_ref(v_env_729_);
                    leanh::lean_dec(v_declHint_725_);
                    v___x_786_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_786_, 0, v_msg_724_);
                    return v___x_786_;
                }
            }
            1 => {
                v___x_754_ = leanh::lean_box(0);
                v___x_755_ = l_Lean_Environment_header(v_env_729_);
                leanh::lean_dec_ref(v_env_729_);
                v___x_756_ = l_Lean_EnvironmentHeader_moduleNames(v___x_755_);
                v_mod_757_ = lean_array_get(v___x_754_, v___x_756_, v_val_750_);
                leanh::lean_dec(v_val_750_);
                leanh::lean_dec_ref(v___x_756_);
                v___x_758_ = l_Lean_isPrivateName(v_declHint_725_);
                leanh::lean_dec(v_declHint_725_);
                if v___x_758_ == 0 {
                    v___x_759_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_runForNodeKind_spec__0_spec__0_spec__1_spec__6_spec__8_spec__9___redArg___closed__5), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_runForNodeKind_spec__0_spec__0_spec__1_spec__6_spec__8_spec__9___redArg___closed__5_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_runForNodeKind_spec__0_spec__0_spec__1_spec__6_spec__8_spec__9___redArg___closed__5);
                    v___x_760_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_760_, 0, v___x_759_);
                    leanh::lean_ctor_set(v___x_760_, 1, v_c_741_);
                    v___x_761_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_runForNodeKind_spec__0_spec__0_spec__1_spec__6_spec__8_spec__9___redArg___closed__7), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_runForNodeKind_spec__0_spec__0_spec__1_spec__6_spec__8_spec__9___redArg___closed__7_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_runForNodeKind_spec__0_spec__0_spec__1_spec__6_spec__8_spec__9___redArg___closed__7);
                    v___x_762_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_762_, 0, v___x_760_);
                    leanh::lean_ctor_set(v___x_762_, 1, v___x_761_);
                    v___x_763_ = l_Lean_MessageData_ofName(v_mod_757_);
                    v___x_764_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_764_, 0, v___x_762_);
                    leanh::lean_ctor_set(v___x_764_, 1, v___x_763_);
                    v___x_765_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_runForNodeKind_spec__0_spec__0_spec__1_spec__6_spec__8_spec__9___redArg___closed__9), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_runForNodeKind_spec__0_spec__0_spec__1_spec__6_spec__8_spec__9___redArg___closed__9_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_runForNodeKind_spec__0_spec__0_spec__1_spec__6_spec__8_spec__9___redArg___closed__9);
                    v___x_766_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_766_, 0, v___x_764_);
                    leanh::lean_ctor_set(v___x_766_, 1, v___x_765_);
                    v___x_767_ = l_Lean_MessageData_note(v___x_766_);
                    v___x_768_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_768_, 0, v_msg_724_);
                    leanh::lean_ctor_set(v___x_768_, 1, v___x_767_);
                    if v_isShared_753_ == 0 {
                        leanh::lean_ctor_set_tag(v___x_752_, 0);
                        leanh::lean_ctor_set(v___x_752_, 0, v___x_768_);
                        v___x_770_ = v___x_752_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_771_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_771_, 0, v___x_768_);
                        v___x_770_ = v_reuseFailAlloc_771_;
                        state = 2;
                        continue;
                    }
                } else {
                    v___x_772_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_runForNodeKind_spec__0_spec__0_spec__1_spec__6_spec__8_spec__9___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_runForNodeKind_spec__0_spec__0_spec__1_spec__6_spec__8_spec__9___redArg___closed__1_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_runForNodeKind_spec__0_spec__0_spec__1_spec__6_spec__8_spec__9___redArg___closed__1);
                    v___x_773_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_773_, 0, v___x_772_);
                    leanh::lean_ctor_set(v___x_773_, 1, v_c_741_);
                    v___x_774_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_runForNodeKind_spec__0_spec__0_spec__1_spec__6_spec__8_spec__9___redArg___closed__11), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_runForNodeKind_spec__0_spec__0_spec__1_spec__6_spec__8_spec__9___redArg___closed__11_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_runForNodeKind_spec__0_spec__0_spec__1_spec__6_spec__8_spec__9___redArg___closed__11);
                    v___x_775_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_775_, 0, v___x_773_);
                    leanh::lean_ctor_set(v___x_775_, 1, v___x_774_);
                    v___x_776_ = l_Lean_MessageData_ofName(v_mod_757_);
                    v___x_777_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_777_, 0, v___x_775_);
                    leanh::lean_ctor_set(v___x_777_, 1, v___x_776_);
                    v___x_778_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_runForNodeKind_spec__0_spec__0_spec__1_spec__6_spec__8_spec__9___redArg___closed__13), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_runForNodeKind_spec__0_spec__0_spec__1_spec__6_spec__8_spec__9___redArg___closed__13_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_runForNodeKind_spec__0_spec__0_spec__1_spec__6_spec__8_spec__9___redArg___closed__13);
                    v___x_779_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_779_, 0, v___x_777_);
                    leanh::lean_ctor_set(v___x_779_, 1, v___x_778_);
                    v___x_780_ = l_Lean_MessageData_note(v___x_779_);
                    v___x_781_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_781_, 0, v_msg_724_);
                    leanh::lean_ctor_set(v___x_781_, 1, v___x_780_);
                    if v_isShared_753_ == 0 {
                        leanh::lean_ctor_set_tag(v___x_752_, 0);
                        leanh::lean_ctor_set(v___x_752_, 0, v___x_781_);
                        v___x_783_ = v___x_752_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_784_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_784_, 0, v___x_781_);
                        v___x_783_ = v_reuseFailAlloc_784_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_770_;
            }
            3 => {
                return v___x_783_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_runForNodeKind_spec__0_spec__0_spec__1_spec__6_spec__8_spec__9___redArg___boxed(
    mut v_msg_787_: *mut leanh::LeanObject,
    mut v_declHint_788_: *mut leanh::LeanObject,
    mut v___y_789_: *mut leanh::LeanObject,
    mut v___y_790_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_791_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_791_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_runForNodeKind_spec__0_spec__0_spec__1_spec__6_spec__8_spec__9___redArg(v_msg_787_, v_declHint_788_, v___y_789_);
    leanh::lean_dec(v___y_789_);
    return v_res_791_;
}
pub unsafe fn l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_runForNodeKind_spec__0_spec__0_spec__1_spec__6_spec__8(
    mut v_msg_792_: *mut leanh::LeanObject,
    mut v_declHint_793_: *mut leanh::LeanObject,
    mut v___y_794_: *mut leanh::LeanObject,
    mut v___y_795_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_797_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_798_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_800_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_801_: u8 = 0;
    let mut v___x_802_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_803_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_805_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_806_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_807_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_797_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_runForNodeKind_spec__0_spec__0_spec__1_spec__6_spec__8_spec__9___redArg(v_msg_792_, v_declHint_793_, v___y_795_);
                v_a_798_ = leanh::lean_ctor_get(v___x_797_, 0);
                v_isSharedCheck_807_ = (!leanh::lean_is_exclusive(v___x_797_)) as u8;
                if v_isSharedCheck_807_ == 0 {
                    v___x_800_ = v___x_797_;
                    v_isShared_801_ = v_isSharedCheck_807_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_a_798_);
                    leanh::lean_dec(v___x_797_);
                    v___x_800_ = leanh::lean_box(0);
                    v_isShared_801_ = v_isSharedCheck_807_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_802_ = l_Lean_unknownIdentifierMessageTag;
                v___x_803_ = leanh::lean_alloc_ctor(8, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_803_, 0, v___x_802_);
                leanh::lean_ctor_set(v___x_803_, 1, v_a_798_);
                if v_isShared_801_ == 0 {
                    leanh::lean_ctor_set(v___x_800_, 0, v___x_803_);
                    v___x_805_ = v___x_800_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_806_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_806_, 0, v___x_803_);
                    v___x_805_ = v_reuseFailAlloc_806_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_805_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_runForNodeKind_spec__0_spec__0_spec__1_spec__6_spec__8___boxed(
    mut v_msg_808_: *mut leanh::LeanObject,
    mut v_declHint_809_: *mut leanh::LeanObject,
    mut v___y_810_: *mut leanh::LeanObject,
    mut v___y_811_: *mut leanh::LeanObject,
    mut v___y_812_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_813_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_813_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_runForNodeKind_spec__0_spec__0_spec__1_spec__6_spec__8(v_msg_808_, v_declHint_809_, v___y_810_, v___y_811_);
    leanh::lean_dec(v___y_811_);
    leanh::lean_dec_ref(v___y_810_);
    return v_res_813_;
}
pub unsafe fn l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_runForNodeKind_spec__0_spec__0_spec__1_spec__6___redArg(
    mut v_ref_814_: *mut leanh::LeanObject,
    mut v_msg_815_: *mut leanh::LeanObject,
    mut v_declHint_816_: *mut leanh::LeanObject,
    mut v___y_817_: *mut leanh::LeanObject,
    mut v___y_818_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_820_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_821_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_822_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_820_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_runForNodeKind_spec__0_spec__0_spec__1_spec__6_spec__8(v_msg_815_, v_declHint_816_, v___y_817_, v___y_818_);
    v_a_821_ = leanh::lean_ctor_get(v___x_820_, 0);
    leanh::lean_inc(v_a_821_);
    leanh::lean_dec_ref(v___x_820_);
    v___x_822_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_runForNodeKind_spec__0_spec__0_spec__1_spec__6_spec__9___redArg(v_ref_814_, v_a_821_, v___y_817_, v___y_818_);
    return v___x_822_;
}
pub unsafe fn l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_runForNodeKind_spec__0_spec__0_spec__1_spec__6___redArg___boxed(
    mut v_ref_823_: *mut leanh::LeanObject,
    mut v_msg_824_: *mut leanh::LeanObject,
    mut v_declHint_825_: *mut leanh::LeanObject,
    mut v___y_826_: *mut leanh::LeanObject,
    mut v___y_827_: *mut leanh::LeanObject,
    mut v___y_828_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_829_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_829_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_runForNodeKind_spec__0_spec__0_spec__1_spec__6___redArg(v_ref_823_, v_msg_824_, v_declHint_825_, v___y_826_, v___y_827_);
    leanh::lean_dec(v___y_827_);
    leanh::lean_dec_ref(v___y_826_);
    leanh::lean_dec(v_ref_823_);
    return v_res_829_;
}
pub unsafe fn _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_runForNodeKind_spec__0_spec__0_spec__1___redArg___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_831_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_832_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_831_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_runForNodeKind_spec__0_spec__0_spec__1___redArg___closed__0;
    v___x_832_ = l_Lean_stringToMessageData(v___x_831_);
    return v___x_832_;
}
pub unsafe fn _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_runForNodeKind_spec__0_spec__0_spec__1___redArg___closed__3()
-> *mut leanh::LeanObject {
    let mut v___x_834_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_835_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_834_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_runForNodeKind_spec__0_spec__0_spec__1___redArg___closed__2;
    v___x_835_ = l_Lean_stringToMessageData(v___x_834_);
    return v___x_835_;
}
pub unsafe fn l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_runForNodeKind_spec__0_spec__0_spec__1___redArg(
    mut v_ref_836_: *mut leanh::LeanObject,
    mut v_constName_837_: *mut leanh::LeanObject,
    mut v___y_838_: *mut leanh::LeanObject,
    mut v___y_839_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_841_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_842_: u8 = 0;
    let mut v___x_843_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_844_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_845_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_846_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_847_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_841_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_runForNodeKind_spec__0_spec__0_spec__1___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_runForNodeKind_spec__0_spec__0_spec__1___redArg___closed__1_once), _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_runForNodeKind_spec__0_spec__0_spec__1___redArg___closed__1);
    v___x_842_ = 0;
    leanh::lean_inc(v_constName_837_);
    v___x_843_ = l_Lean_MessageData_ofConstName(v_constName_837_, v___x_842_);
    v___x_844_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_844_, 0, v___x_841_);
    leanh::lean_ctor_set(v___x_844_, 1, v___x_843_);
    v___x_845_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_runForNodeKind_spec__0_spec__0_spec__1___redArg___closed__3), core::ptr::addr_of_mut!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_runForNodeKind_spec__0_spec__0_spec__1___redArg___closed__3_once), _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_runForNodeKind_spec__0_spec__0_spec__1___redArg___closed__3);
    v___x_846_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_846_, 0, v___x_844_);
    leanh::lean_ctor_set(v___x_846_, 1, v___x_845_);
    v___x_847_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_runForNodeKind_spec__0_spec__0_spec__1_spec__6___redArg(v_ref_836_, v___x_846_, v_constName_837_, v___y_838_, v___y_839_);
    return v___x_847_;
}
pub unsafe fn l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_runForNodeKind_spec__0_spec__0_spec__1___redArg___boxed(
    mut v_ref_848_: *mut leanh::LeanObject,
    mut v_constName_849_: *mut leanh::LeanObject,
    mut v___y_850_: *mut leanh::LeanObject,
    mut v___y_851_: *mut leanh::LeanObject,
    mut v___y_852_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_853_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_853_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_runForNodeKind_spec__0_spec__0_spec__1___redArg(v_ref_848_, v_constName_849_, v___y_850_, v___y_851_);
    leanh::lean_dec(v___y_851_);
    leanh::lean_dec_ref(v___y_850_);
    leanh::lean_dec(v_ref_848_);
    return v_res_853_;
}
pub unsafe fn l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_runForNodeKind_spec__0_spec__0___redArg(
    mut v_constName_854_: *mut leanh::LeanObject,
    mut v___y_855_: *mut leanh::LeanObject,
    mut v___y_856_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_ref_858_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_859_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_ref_858_ = leanh::lean_ctor_get(v___y_855_, 5);
    v___x_859_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_runForNodeKind_spec__0_spec__0_spec__1___redArg(v_ref_858_, v_constName_854_, v___y_855_, v___y_856_);
    return v___x_859_;
}
pub unsafe fn l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_runForNodeKind_spec__0_spec__0___redArg___boxed(
    mut v_constName_860_: *mut leanh::LeanObject,
    mut v___y_861_: *mut leanh::LeanObject,
    mut v___y_862_: *mut leanh::LeanObject,
    mut v___y_863_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_864_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_864_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_runForNodeKind_spec__0_spec__0___redArg(v_constName_860_, v___y_861_, v___y_862_);
    leanh::lean_dec(v___y_862_);
    leanh::lean_dec_ref(v___y_861_);
    return v_res_864_;
}
pub unsafe fn l_Lean_getConstInfo___at___00Lean_PrettyPrinter_runForNodeKind_spec__0(
    mut v_constName_865_: *mut leanh::LeanObject,
    mut v___y_866_: *mut leanh::LeanObject,
    mut v___y_867_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_869_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_870_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_871_: u8 = 0;
    let mut v___x_872_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_873_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_874_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_876_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_877_: u8 = 0;
    let mut v___x_879_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_880_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_881_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_869_ = lean_st_ref_get(v___y_867_);
                v_env_870_ = leanh::lean_ctor_get(v___x_869_, 0);
                leanh::lean_inc_ref(v_env_870_);
                leanh::lean_dec(v___x_869_);
                v___x_871_ = 0;
                leanh::lean_inc(v_constName_865_);
                v___x_872_ = l_Lean_Environment_find_x3f(v_env_870_, v_constName_865_, v___x_871_);
                if leanh::lean_obj_tag(v___x_872_) == 0 {
                    v___x_873_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_runForNodeKind_spec__0_spec__0___redArg(v_constName_865_, v___y_866_, v___y_867_);
                    return v___x_873_;
                } else {
                    leanh::lean_dec(v_constName_865_);
                    v_val_874_ = leanh::lean_ctor_get(v___x_872_, 0);
                    v_isSharedCheck_881_ = (!leanh::lean_is_exclusive(v___x_872_)) as u8;
                    if v_isSharedCheck_881_ == 0 {
                        v___x_876_ = v___x_872_;
                        v_isShared_877_ = v_isSharedCheck_881_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_val_874_);
                        leanh::lean_dec(v___x_872_);
                        v___x_876_ = leanh::lean_box(0);
                        v_isShared_877_ = v_isSharedCheck_881_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_877_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_876_, 0);
                    v___x_879_ = v___x_876_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_880_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_880_, 0, v_val_874_);
                    v___x_879_ = v_reuseFailAlloc_880_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_879_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_getConstInfo___at___00Lean_PrettyPrinter_runForNodeKind_spec__0___boxed(
    mut v_constName_882_: *mut leanh::LeanObject,
    mut v___y_883_: *mut leanh::LeanObject,
    mut v___y_884_: *mut leanh::LeanObject,
    mut v___y_885_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_886_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_886_ = l_Lean_getConstInfo___at___00Lean_PrettyPrinter_runForNodeKind_spec__0(
        v_constName_882_,
        v___y_883_,
        v___y_884_,
    );
    leanh::lean_dec(v___y_884_);
    leanh::lean_dec_ref(v___y_883_);
    return v_res_886_;
}
pub unsafe fn _init_l_Lean_PrettyPrinter_runForNodeKind___redArg___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_888_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_889_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_888_ = l_Lean_PrettyPrinter_runForNodeKind___redArg___closed__0;
    v___x_889_ = l_Lean_stringToMessageData(v___x_888_);
    return v___x_889_;
}
pub unsafe fn _init_l_Lean_PrettyPrinter_runForNodeKind___redArg___closed__3()
-> *mut leanh::LeanObject {
    let mut v___x_891_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_892_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_891_ = l_Lean_PrettyPrinter_runForNodeKind___redArg___closed__2;
    v___x_892_ = l_Lean_stringToMessageData(v___x_891_);
    return v___x_892_;
}
pub unsafe fn l_Lean_PrettyPrinter_runForNodeKind___redArg(
    mut v_attr_902_: *mut leanh::LeanObject,
    mut v_k_903_: *mut leanh::LeanObject,
    mut v_interp_904_: *mut leanh::LeanObject,
    mut v_a_905_: *mut leanh::LeanObject,
    mut v_a_906_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_908_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_909_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_910_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_911_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_912_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_913_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_914_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_916_: u8 = 0;
    let mut v_defn_917_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_name_918_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_919_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_920_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_921_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_922_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_923_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_924_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_925_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_926_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_927_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_928_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_929_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_930_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_931_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_932_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_934_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_935_: u8 = 0;
    let mut v___x_937_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_938_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_939_: u8 = 0;
    let mut v___x_940_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_941_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_942_: u8 = 0;
    let mut v___x_943_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_944_: u8 = 0;
    let mut v_a_945_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_947_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_948_: u8 = 0;
    let mut v___x_950_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_951_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_952_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_908_ = lean_st_ref_get(v_a_906_);
                v_env_909_ = leanh::lean_ctor_get(v___x_908_, 0);
                leanh::lean_inc_ref(v_env_909_);
                leanh::lean_dec(v___x_908_);
                v___x_910_ = l_Lean_KeyedDeclsAttribute_getValues___redArg(
                    v_attr_902_,
                    v_env_909_,
                    v_k_903_,
                );
                if leanh::lean_obj_tag(v___x_910_) == 1 {
                    leanh::lean_dec_ref(v_interp_904_);
                    leanh::lean_dec(v_k_903_);
                    leanh::lean_dec_ref(v_attr_902_);
                    v_head_911_ = leanh::lean_ctor_get(v___x_910_, 0);
                    leanh::lean_inc(v_head_911_);
                    leanh::lean_dec_ref_known(v___x_910_, 2);
                    v___x_912_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_912_, 0, v_head_911_);
                    return v___x_912_;
                } else {
                    leanh::lean_dec(v___x_910_);
                    leanh::lean_inc(v_k_903_);
                    v___x_913_ =
                        l_Lean_getConstInfo___at___00Lean_PrettyPrinter_runForNodeKind_spec__0(
                            v_k_903_, v_a_905_, v_a_906_,
                        );
                    if leanh::lean_obj_tag(v___x_913_) == 0 {
                        v_a_914_ = leanh::lean_ctor_get(v___x_913_, 0);
                        leanh::lean_inc(v_a_914_);
                        leanh::lean_dec_ref_known(v___x_913_, 1);
                        v___x_940_ = l_Lean_ConstantInfo_type(v_a_914_);
                        leanh::lean_dec(v_a_914_);
                        v___x_941_ = l_Lean_PrettyPrinter_runForNodeKind___redArg___closed__6;
                        v___x_942_ = l_Lean_Expr_isConstOf(v___x_940_, v___x_941_);
                        if v___x_942_ == 0 {
                            v___x_943_ = l_Lean_PrettyPrinter_runForNodeKind___redArg___closed__8;
                            v___x_944_ = l_Lean_Expr_isConstOf(v___x_940_, v___x_943_);
                            leanh::lean_dec_ref(v___x_940_);
                            v___y_916_ = v___x_944_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_dec_ref(v___x_940_);
                            v___y_916_ = v___x_942_;
                            state = 1;
                            continue;
                        }
                    } else {
                        leanh::lean_dec_ref(v_interp_904_);
                        leanh::lean_dec(v_k_903_);
                        leanh::lean_dec_ref(v_attr_902_);
                        v_a_945_ = leanh::lean_ctor_get(v___x_913_, 0);
                        v_isSharedCheck_952_ = (!leanh::lean_is_exclusive(v___x_913_)) as u8;
                        if v_isSharedCheck_952_ == 0 {
                            v___x_947_ = v___x_913_;
                            v_isShared_948_ = v_isSharedCheck_952_;
                            state = 4;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_945_);
                            leanh::lean_dec(v___x_913_);
                            v___x_947_ = leanh::lean_box(0);
                            v_isShared_948_ = v_isSharedCheck_952_;
                            state = 4;
                            continue;
                        }
                    }
                }
            }
            1 => {
                if v___y_916_ == 0 {
                    leanh::lean_dec_ref(v_interp_904_);
                    v_defn_917_ = leanh::lean_ctor_get(v_attr_902_, 0);
                    leanh::lean_inc_ref(v_defn_917_);
                    leanh::lean_dec_ref(v_attr_902_);
                    v_name_918_ = leanh::lean_ctor_get(v_defn_917_, 1);
                    leanh::lean_inc(v_name_918_);
                    leanh::lean_dec_ref(v_defn_917_);
                    v___x_919_ = leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(
                            l_Lean_PrettyPrinter_runForNodeKind___redArg___closed__1
                        ),
                        core::ptr::addr_of_mut!(
                            l_Lean_PrettyPrinter_runForNodeKind___redArg___closed__1_once
                        ),
                        _init_l_Lean_PrettyPrinter_runForNodeKind___redArg___closed__1,
                    );
                    v___x_920_ = l_Lean_MessageData_ofName(v_name_918_);
                    v___x_921_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_921_, 0, v___x_919_);
                    leanh::lean_ctor_set(v___x_921_, 1, v___x_920_);
                    v___x_922_ = leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(
                            l_Lean_PrettyPrinter_runForNodeKind___redArg___closed__3
                        ),
                        core::ptr::addr_of_mut!(
                            l_Lean_PrettyPrinter_runForNodeKind___redArg___closed__3_once
                        ),
                        _init_l_Lean_PrettyPrinter_runForNodeKind___redArg___closed__3,
                    );
                    v___x_923_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_923_, 0, v___x_921_);
                    leanh::lean_ctor_set(v___x_923_, 1, v___x_922_);
                    v___x_924_ = l_Lean_MessageData_ofName(v_k_903_);
                    v___x_925_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_925_, 0, v___x_923_);
                    leanh::lean_ctor_set(v___x_925_, 1, v___x_924_);
                    v___x_926_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_runForNodeKind_spec__0_spec__0_spec__1___redArg___closed__3), core::ptr::addr_of_mut!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_runForNodeKind_spec__0_spec__0_spec__1___redArg___closed__3_once), _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_runForNodeKind_spec__0_spec__0_spec__1___redArg___closed__3);
                    v___x_927_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_927_, 0, v___x_925_);
                    leanh::lean_ctor_set(v___x_927_, 1, v___x_926_);
                    v___x_928_ = l_Lean_throwError___at___00Lean_PrettyPrinter_runForNodeKind_spec__1___redArg(v___x_927_, v_a_905_, v_a_906_);
                    return v___x_928_;
                } else {
                    leanh::lean_dec_ref(v_attr_902_);
                    v___x_929_ = l_Lean_evalConst___at___00Lean_PrettyPrinter_runForNodeKind_spec__2___redArg(v_k_903_, v___y_916_, v_a_905_, v_a_906_);
                    if leanh::lean_obj_tag(v___x_929_) == 0 {
                        v_a_930_ = leanh::lean_ctor_get(v___x_929_, 0);
                        leanh::lean_inc(v_a_930_);
                        leanh::lean_dec_ref_known(v___x_929_, 1);
                        leanh::lean_inc(v_a_906_);
                        leanh::lean_inc_ref(v_a_905_);
                        v___x_931_ = leanh::lean_apply_4(
                            v_interp_904_,
                            v_a_930_,
                            v_a_905_,
                            v_a_906_,
                            leanh::lean_box(0),
                        );
                        return v___x_931_;
                    } else {
                        leanh::lean_dec_ref(v_interp_904_);
                        v_a_932_ = leanh::lean_ctor_get(v___x_929_, 0);
                        v_isSharedCheck_939_ = (!leanh::lean_is_exclusive(v___x_929_)) as u8;
                        if v_isSharedCheck_939_ == 0 {
                            v___x_934_ = v___x_929_;
                            v_isShared_935_ = v_isSharedCheck_939_;
                            state = 2;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_932_);
                            leanh::lean_dec(v___x_929_);
                            v___x_934_ = leanh::lean_box(0);
                            v_isShared_935_ = v_isSharedCheck_939_;
                            state = 2;
                            continue;
                        }
                    }
                }
            }
            2 => {
                if v_isShared_935_ == 0 {
                    v___x_937_ = v___x_934_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_938_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_938_, 0, v_a_932_);
                    v___x_937_ = v_reuseFailAlloc_938_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_937_;
            }
            4 => {
                if v_isShared_948_ == 0 {
                    v___x_950_ = v___x_947_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_951_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_951_, 0, v_a_945_);
                    v___x_950_ = v_reuseFailAlloc_951_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_950_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PrettyPrinter_runForNodeKind___redArg___boxed(
    mut v_attr_953_: *mut leanh::LeanObject,
    mut v_k_954_: *mut leanh::LeanObject,
    mut v_interp_955_: *mut leanh::LeanObject,
    mut v_a_956_: *mut leanh::LeanObject,
    mut v_a_957_: *mut leanh::LeanObject,
    mut v_a_958_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_959_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_959_ = l_Lean_PrettyPrinter_runForNodeKind___redArg(
        v_attr_953_,
        v_k_954_,
        v_interp_955_,
        v_a_956_,
        v_a_957_,
    );
    leanh::lean_dec(v_a_957_);
    leanh::lean_dec_ref(v_a_956_);
    return v_res_959_;
}
pub unsafe fn l_Lean_PrettyPrinter_runForNodeKind(
    mut v_00_u03b1_960_: *mut leanh::LeanObject,
    mut v_attr_961_: *mut leanh::LeanObject,
    mut v_k_962_: *mut leanh::LeanObject,
    mut v_interp_963_: *mut leanh::LeanObject,
    mut v_a_964_: *mut leanh::LeanObject,
    mut v_a_965_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_967_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_967_ = l_Lean_PrettyPrinter_runForNodeKind___redArg(
        v_attr_961_,
        v_k_962_,
        v_interp_963_,
        v_a_964_,
        v_a_965_,
    );
    return v___x_967_;
}
pub unsafe fn l_Lean_PrettyPrinter_runForNodeKind___boxed(
    mut v_00_u03b1_968_: *mut leanh::LeanObject,
    mut v_attr_969_: *mut leanh::LeanObject,
    mut v_k_970_: *mut leanh::LeanObject,
    mut v_interp_971_: *mut leanh::LeanObject,
    mut v_a_972_: *mut leanh::LeanObject,
    mut v_a_973_: *mut leanh::LeanObject,
    mut v_a_974_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_975_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_975_ = l_Lean_PrettyPrinter_runForNodeKind(
        v_00_u03b1_968_,
        v_attr_969_,
        v_k_970_,
        v_interp_971_,
        v_a_972_,
        v_a_973_,
    );
    leanh::lean_dec(v_a_973_);
    leanh::lean_dec_ref(v_a_972_);
    return v_res_975_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_PrettyPrinter_runForNodeKind_spec__1(
    mut v_00_u03b1_976_: *mut leanh::LeanObject,
    mut v_msg_977_: *mut leanh::LeanObject,
    mut v___y_978_: *mut leanh::LeanObject,
    mut v___y_979_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_981_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_981_ = l_Lean_throwError___at___00Lean_PrettyPrinter_runForNodeKind_spec__1___redArg(
        v_msg_977_, v___y_978_, v___y_979_,
    );
    return v___x_981_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_PrettyPrinter_runForNodeKind_spec__1___boxed(
    mut v_00_u03b1_982_: *mut leanh::LeanObject,
    mut v_msg_983_: *mut leanh::LeanObject,
    mut v___y_984_: *mut leanh::LeanObject,
    mut v___y_985_: *mut leanh::LeanObject,
    mut v___y_986_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_987_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_987_ = l_Lean_throwError___at___00Lean_PrettyPrinter_runForNodeKind_spec__1(
        v_00_u03b1_982_,
        v_msg_983_,
        v___y_984_,
        v___y_985_,
    );
    leanh::lean_dec(v___y_985_);
    leanh::lean_dec_ref(v___y_984_);
    return v_res_987_;
}
pub unsafe fn l_Lean_Elab_throwAbortCommand___at___00Lean_evalConst___at___00Lean_PrettyPrinter_runForNodeKind_spec__2_spec__5(
    mut v_00_u03b1_988_: *mut leanh::LeanObject,
    mut v___y_989_: *mut leanh::LeanObject,
    mut v___y_990_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_992_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_992_ = l_Lean_Elab_throwAbortCommand___at___00Lean_evalConst___at___00Lean_PrettyPrinter_runForNodeKind_spec__2_spec__5___redArg();
    return v___x_992_;
}
pub unsafe fn l_Lean_Elab_throwAbortCommand___at___00Lean_evalConst___at___00Lean_PrettyPrinter_runForNodeKind_spec__2_spec__5___boxed(
    mut v_00_u03b1_993_: *mut leanh::LeanObject,
    mut v___y_994_: *mut leanh::LeanObject,
    mut v___y_995_: *mut leanh::LeanObject,
    mut v___y_996_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_997_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_997_ = l_Lean_Elab_throwAbortCommand___at___00Lean_evalConst___at___00Lean_PrettyPrinter_runForNodeKind_spec__2_spec__5(v_00_u03b1_993_, v___y_994_, v___y_995_);
    leanh::lean_dec(v___y_995_);
    leanh::lean_dec_ref(v___y_994_);
    return v_res_997_;
}
pub unsafe fn l_Lean_evalConst___at___00Lean_PrettyPrinter_runForNodeKind_spec__2(
    mut v_00_u03b1_998_: *mut leanh::LeanObject,
    mut v_constName_999_: *mut leanh::LeanObject,
    mut v_checkMeta_1000_: u8,
    mut v___y_1001_: *mut leanh::LeanObject,
    mut v___y_1002_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1004_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1004_ = l_Lean_evalConst___at___00Lean_PrettyPrinter_runForNodeKind_spec__2___redArg(
        v_constName_999_,
        v_checkMeta_1000_,
        v___y_1001_,
        v___y_1002_,
    );
    return v___x_1004_;
}
pub unsafe fn l_Lean_evalConst___at___00Lean_PrettyPrinter_runForNodeKind_spec__2___boxed(
    mut v_00_u03b1_1005_: *mut leanh::LeanObject,
    mut v_constName_1006_: *mut leanh::LeanObject,
    mut v_checkMeta_1007_: *mut leanh::LeanObject,
    mut v___y_1008_: *mut leanh::LeanObject,
    mut v___y_1009_: *mut leanh::LeanObject,
    mut v___y_1010_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_checkMeta_boxed_1011_: u8 = 0;
    let mut v_res_1012_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_checkMeta_boxed_1011_ = (leanh::lean_unbox(v_checkMeta_1007_) as u8);
    v_res_1012_ = l_Lean_evalConst___at___00Lean_PrettyPrinter_runForNodeKind_spec__2(
        v_00_u03b1_1005_,
        v_constName_1006_,
        v_checkMeta_boxed_1011_,
        v___y_1008_,
        v___y_1009_,
    );
    leanh::lean_dec(v___y_1009_);
    leanh::lean_dec_ref(v___y_1008_);
    return v_res_1012_;
}
pub unsafe fn l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_runForNodeKind_spec__0_spec__0(
    mut v_00_u03b1_1013_: *mut leanh::LeanObject,
    mut v_constName_1014_: *mut leanh::LeanObject,
    mut v___y_1015_: *mut leanh::LeanObject,
    mut v___y_1016_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1018_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1018_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_runForNodeKind_spec__0_spec__0___redArg(v_constName_1014_, v___y_1015_, v___y_1016_);
    return v___x_1018_;
}
pub unsafe fn l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_runForNodeKind_spec__0_spec__0___boxed(
    mut v_00_u03b1_1019_: *mut leanh::LeanObject,
    mut v_constName_1020_: *mut leanh::LeanObject,
    mut v___y_1021_: *mut leanh::LeanObject,
    mut v___y_1022_: *mut leanh::LeanObject,
    mut v___y_1023_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1024_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1024_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_runForNodeKind_spec__0_spec__0(v_00_u03b1_1019_, v_constName_1020_, v___y_1021_, v___y_1022_);
    leanh::lean_dec(v___y_1022_);
    leanh::lean_dec_ref(v___y_1021_);
    return v_res_1024_;
}
pub unsafe fn l_Lean_ofExcept___at___00Lean_evalConst___at___00Lean_PrettyPrinter_runForNodeKind_spec__2_spec__4(
    mut v_00_u03b1_1025_: *mut leanh::LeanObject,
    mut v_x_1026_: *mut leanh::LeanObject,
    mut v___y_1027_: *mut leanh::LeanObject,
    mut v___y_1028_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1030_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1030_ = l_Lean_ofExcept___at___00Lean_evalConst___at___00Lean_PrettyPrinter_runForNodeKind_spec__2_spec__4___redArg(v_x_1026_, v___y_1027_, v___y_1028_);
    return v___x_1030_;
}
pub unsafe fn l_Lean_ofExcept___at___00Lean_evalConst___at___00Lean_PrettyPrinter_runForNodeKind_spec__2_spec__4___boxed(
    mut v_00_u03b1_1031_: *mut leanh::LeanObject,
    mut v_x_1032_: *mut leanh::LeanObject,
    mut v___y_1033_: *mut leanh::LeanObject,
    mut v___y_1034_: *mut leanh::LeanObject,
    mut v___y_1035_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1036_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1036_ = l_Lean_ofExcept___at___00Lean_evalConst___at___00Lean_PrettyPrinter_runForNodeKind_spec__2_spec__4(v_00_u03b1_1031_, v_x_1032_, v___y_1033_, v___y_1034_);
    leanh::lean_dec(v___y_1034_);
    leanh::lean_dec_ref(v___y_1033_);
    return v_res_1036_;
}
pub unsafe fn l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_runForNodeKind_spec__0_spec__0_spec__1(
    mut v_00_u03b1_1037_: *mut leanh::LeanObject,
    mut v_ref_1038_: *mut leanh::LeanObject,
    mut v_constName_1039_: *mut leanh::LeanObject,
    mut v___y_1040_: *mut leanh::LeanObject,
    mut v___y_1041_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1043_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1043_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_runForNodeKind_spec__0_spec__0_spec__1___redArg(v_ref_1038_, v_constName_1039_, v___y_1040_, v___y_1041_);
    return v___x_1043_;
}
pub unsafe fn l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_runForNodeKind_spec__0_spec__0_spec__1___boxed(
    mut v_00_u03b1_1044_: *mut leanh::LeanObject,
    mut v_ref_1045_: *mut leanh::LeanObject,
    mut v_constName_1046_: *mut leanh::LeanObject,
    mut v___y_1047_: *mut leanh::LeanObject,
    mut v___y_1048_: *mut leanh::LeanObject,
    mut v___y_1049_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1050_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1050_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_runForNodeKind_spec__0_spec__0_spec__1(v_00_u03b1_1044_, v_ref_1045_, v_constName_1046_, v___y_1047_, v___y_1048_);
    leanh::lean_dec(v___y_1048_);
    leanh::lean_dec_ref(v___y_1047_);
    leanh::lean_dec(v_ref_1045_);
    return v_res_1050_;
}
pub unsafe fn l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_runForNodeKind_spec__0_spec__0_spec__1_spec__6(
    mut v_00_u03b1_1051_: *mut leanh::LeanObject,
    mut v_ref_1052_: *mut leanh::LeanObject,
    mut v_msg_1053_: *mut leanh::LeanObject,
    mut v_declHint_1054_: *mut leanh::LeanObject,
    mut v___y_1055_: *mut leanh::LeanObject,
    mut v___y_1056_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1058_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1058_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_runForNodeKind_spec__0_spec__0_spec__1_spec__6___redArg(v_ref_1052_, v_msg_1053_, v_declHint_1054_, v___y_1055_, v___y_1056_);
    return v___x_1058_;
}
pub unsafe fn l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_runForNodeKind_spec__0_spec__0_spec__1_spec__6___boxed(
    mut v_00_u03b1_1059_: *mut leanh::LeanObject,
    mut v_ref_1060_: *mut leanh::LeanObject,
    mut v_msg_1061_: *mut leanh::LeanObject,
    mut v_declHint_1062_: *mut leanh::LeanObject,
    mut v___y_1063_: *mut leanh::LeanObject,
    mut v___y_1064_: *mut leanh::LeanObject,
    mut v___y_1065_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1066_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1066_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_runForNodeKind_spec__0_spec__0_spec__1_spec__6(v_00_u03b1_1059_, v_ref_1060_, v_msg_1061_, v_declHint_1062_, v___y_1063_, v___y_1064_);
    leanh::lean_dec(v___y_1064_);
    leanh::lean_dec_ref(v___y_1063_);
    leanh::lean_dec(v_ref_1060_);
    return v_res_1066_;
}
pub unsafe fn l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_runForNodeKind_spec__0_spec__0_spec__1_spec__6_spec__8_spec__9(
    mut v_msg_1067_: *mut leanh::LeanObject,
    mut v_declHint_1068_: *mut leanh::LeanObject,
    mut v___y_1069_: *mut leanh::LeanObject,
    mut v___y_1070_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1072_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1072_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_runForNodeKind_spec__0_spec__0_spec__1_spec__6_spec__8_spec__9___redArg(v_msg_1067_, v_declHint_1068_, v___y_1070_);
    return v___x_1072_;
}
pub unsafe fn l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_runForNodeKind_spec__0_spec__0_spec__1_spec__6_spec__8_spec__9___boxed(
    mut v_msg_1073_: *mut leanh::LeanObject,
    mut v_declHint_1074_: *mut leanh::LeanObject,
    mut v___y_1075_: *mut leanh::LeanObject,
    mut v___y_1076_: *mut leanh::LeanObject,
    mut v___y_1077_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1078_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1078_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_runForNodeKind_spec__0_spec__0_spec__1_spec__6_spec__8_spec__9(v_msg_1073_, v_declHint_1074_, v___y_1075_, v___y_1076_);
    leanh::lean_dec(v___y_1076_);
    leanh::lean_dec_ref(v___y_1075_);
    return v_res_1078_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_runForNodeKind_spec__0_spec__0_spec__1_spec__6_spec__9(
    mut v_00_u03b1_1079_: *mut leanh::LeanObject,
    mut v_ref_1080_: *mut leanh::LeanObject,
    mut v_msg_1081_: *mut leanh::LeanObject,
    mut v___y_1082_: *mut leanh::LeanObject,
    mut v___y_1083_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1085_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1085_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_runForNodeKind_spec__0_spec__0_spec__1_spec__6_spec__9___redArg(v_ref_1080_, v_msg_1081_, v___y_1082_, v___y_1083_);
    return v___x_1085_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_runForNodeKind_spec__0_spec__0_spec__1_spec__6_spec__9___boxed(
    mut v_00_u03b1_1086_: *mut leanh::LeanObject,
    mut v_ref_1087_: *mut leanh::LeanObject,
    mut v_msg_1088_: *mut leanh::LeanObject,
    mut v___y_1089_: *mut leanh::LeanObject,
    mut v___y_1090_: *mut leanh::LeanObject,
    mut v___y_1091_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1092_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1092_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_PrettyPrinter_runForNodeKind_spec__0_spec__0_spec__1_spec__6_spec__9(v_00_u03b1_1086_, v_ref_1087_, v_msg_1088_, v___y_1089_, v___y_1090_);
    leanh::lean_dec(v___y_1090_);
    leanh::lean_dec_ref(v___y_1089_);
    leanh::lean_dec(v_ref_1087_);
    return v_res_1092_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_PrettyPrinter_Basic(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_KeyedDeclsAttribute(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = l___private_Lean_PrettyPrinter_Basic_0__Lean_PrettyPrinter_initFn_00___x40_Lean_PrettyPrinter_Basic_613194564____hygCtx___hyg_2_();
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    l_Lean_PrettyPrinter_backtrackExceptionId = leanh::lean_io_result_get_value(res);
    leanh::lean_mark_persistent(l_Lean_PrettyPrinter_backtrackExceptionId);
    leanh::lean_dec_ref(res);
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_PrettyPrinter_Basic(
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
pub unsafe fn initialize_Lean_PrettyPrinter_Basic(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_KeyedDeclsAttribute(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_PrettyPrinter_Basic(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_PrettyPrinter_Basic(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return initialize_Lean_PrettyPrinter_Basic(builtin);
}